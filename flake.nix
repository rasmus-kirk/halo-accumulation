{
  description = "Flake for GH-pages";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";

    # code
    code.url = "./code";
    code.inputs.nixpkgs.follows = "nixpkgs";
    # report
    report.url = "./report";
    report.inputs.nixpkgs.follows = "nixpkgs";

    website-builder.url = "github:rasmus-kirk/website-builder";
    website-builder.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = {
    nixpkgs,
    website-builder,
    report,
    ...
  }: let
    supportedSystems = ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"];
    forAllSystems = f:
      nixpkgs.lib.genAttrs supportedSystems (system:
        f {
          pkgs = import nixpkgs {inherit system;};
        });
  in {
    packages = forAllSystems ({pkgs}: let
      reportPkg = report.outputs.packages."${pkgs.system}".default;
      website = website-builder.lib {
        pkgs = pkgs;
        src = ./.;
        headerTitle = "Halo Accumulation Scheme";
        includedDirs = [ reportPkg ];
        standalonePages = [{
          title = "Investigating IVC with Accumulation Schemes";
          inputFile = ./README.md;
          outputFile = "index.html";
        }];
        navbar = [
          {
            title = "Home";
            location = "/";
          }
          {
            title = "Report";
            location = "/report/report.pdf";
          }
          {
            title = "Github";
            location = "https://github.com/rasmus-kirk/halo-accumulation";
          }
        ];
      };
    in {
      default = website.package;
      debug = website.loop;
    });

    formatter = forAllSystems ({pkgs}: pkgs.alejandra);
  };
}
