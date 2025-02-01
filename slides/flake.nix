{
  description = "Slides built with Pandoc, with continious compilation.";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = {
    nixpkgs,
    ...
  }: let
    supportedSystems = ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"];
    forAllSystems = f:
      nixpkgs.lib.genAttrs supportedSystems (system:
        f {
          pkgs = import nixpkgs {inherit system;};
        });
  in {
    formatter = forAllSystems ({pkgs}: pkgs.alejandra);

    packages = forAllSystems ({pkgs}: let
      fonts = pkgs.makeFontsConf { fontDirectories = [ pkgs.dejavu_fonts ]; };
      latexPkgs =  with pkgs; [
        pandoc
        haskellPackages.pandoc-crossref
        texlive.combined.scheme-full
        librsvg
      ];
      mk-pandoc-script = pkgs.writeShellApplication {
        name = "mk-pandoc-script";
        runtimeInputs = latexPkgs;
        text = ''
          # Loop through each .md file in the folder
          for filename in ./*.md; do
              pandoc "$filename" \
                -H header.tex \
                --highlight-style gruvbox.theme \
                -t beamer \
                --slide-level 2 \
                --metadata date="$(date -u '+%Y-%m-%d - %H:%M:%S %Z')" \
                -o "$1/''${filename%.md}.pdf"
          done
        '';
      };
      debug = pkgs.writeShellApplication {
        name = "mk-pandoc-debug";
        runtimeInputs = latexPkgs;
        text = ''
          # Loop through each .md file in the folder
          for filename in ./*.md; do
              pandoc "$filename" \
                -H header.tex \
                --citeproc \
                --metadata date="$(date -u '+%Y-%m-%d - %H:%M:%S %Z')" \
                --highlight-style gruvbox.theme \
                -o "$1/''${filename%.md}.tex"
          done
        '';
      };
      mk-pandoc = pkgs.writeShellApplication {
        name = "mk-pandoc";
        runtimeInputs = latexPkgs;
        text = ''${pkgs.lib.getExe mk-pandoc-script} "."'';
      };
      mk-pandoc-loop = pkgs.writeShellApplication {
        name = "pandoc-compile-continuous";
        runtimeInputs = [mk-pandoc pkgs.fswatch];
        text = ''
          set +e
          echo "Listening for file changes"
          fswatch --event Updated ./*.md | xargs -n 1 sh -c 'date "+%Y-%m-%d - %H:%M:%S %Z"; mk-pandoc'
        '';
      };
      spellcheck = pkgs.writeShellApplication {
        name = "spellcheck";
        runtimeInputs = [pkgs.nodePackages_latest.cspell];
        text = ''cspell "*.md"'';
      };
      spellcheck-watch = pkgs.writeShellApplication {
        name = "spellcheck";
        runtimeInputs = [pkgs.nodePackages_latest.cspell];
        text = ''watch --color cspell --color "*.md"'';
      };
      slides = pkgs.stdenv.mkDerivation {
        name = "slides";
        src = ./.;
        buildInputs = latexPkgs;
        phases = ["unpackPhase" "buildPhase"];
        buildPhase = ''
          export FONTCONFIG_FILE=${fonts}
          mkdir -p $out
          ${pkgs.lib.getExe mk-pandoc-script} "$out"
        '';
      };
      in {
        default = slides;
        loop = mk-pandoc-loop;
        pandoc = mk-pandoc;
        debug = debug;
        spellcheck = spellcheck;
        spellcheck-watch = spellcheck-watch;
      });
  };
}
