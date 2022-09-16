{
  description = "A very basic flake";
  inputs = {
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system}; in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            zlib
            secp256k1
            libff
            (haskell-language-server.override { supportedGhcVersions = ["924"] ; })
          ];
        };
      });
}
