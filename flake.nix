{
  description = "Test project to see if Agda is working";

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = {self, nixpkgs, flake-utils}:
    let
      supportedSystems = ["x86_64-linux"];
    in
      flake-utils.lib.eachSystem supportedSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in rec{
          devShells.default = pkgs.mkShell {
            nativeBuildInputs = [pkgs.pkg-config];
            buildInputs = [pkgs.idris2];
          };
        });
}
