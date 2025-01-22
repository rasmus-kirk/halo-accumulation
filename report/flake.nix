{
  description = "A report built with Pandoc, with continious compilation.";

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
      pandoc-script = pkgs.writeShellApplication {
        name = "pandoc-compile";
        runtimeInputs = latexPkgs;
        text = ''
          # Loop through each .md file in the folder
          for filename in ./*.md; do
              pandoc "$filename" \
                -H header.tex \
                -V colorlinks=true \
                -V linkcolor=black \
                -V urlcolor=GbBlueDk \
                -V toccolor=gray \
                --metadata date="$(date -u '+%Y-%m-%d - %H:%M:%S %Z')" \
                --highlight-style gruvbox.theme \
                -o "$1/''${filename%.md}.pdf"
          done
        '';
      };
      pandoc-compile = pkgs.writeShellApplication {
        name = "pandoc-compile";
        runtimeInputs = latexPkgs;
        text = ''${pkgs.lib.getExe pandoc-script} "."'';
      };
      pandoc-compile-continuous = pkgs.writeShellApplication {
        name = "pandoc-compile-continuous";
        runtimeInputs = [pandoc-compile pkgs.fswatch];
        text = ''
          set +e
          echo "Listening for file changes"
          fswatch --event Updated ./*.md | xargs -n 1 sh -c 'date "+%Y-%m-%d - %H:%M:%S %Z"; pandoc-compile'
        '';
      };
      report = pkgs.stdenv.mkDerivation {
        name = "report";
        src = ./.;
        buildInputs = latexPkgs;
        phases = ["unpackPhase" "buildPhase"];
        buildPhase = ''
          export FONTCONFIG_FILE=${fonts}
          mkdir -p $out
          ${pkgs.lib.getExe pandoc-script} "$out"
        '';
      };
      in {
        default = report;
        loop = pandoc-compile-continuous;
      });
  };
}
