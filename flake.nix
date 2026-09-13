{
  description = "GnuCOBOL toolchain for lean4cobol";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/ffd8177a246bbf499a2ac73ac60498f4970fa5de";

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
    in {
      devShells = nixpkgs.lib.genAttrs systems (system:
        let pkgs = nixpkgs.legacyPackages.${system};
        in {
          default = pkgs.mkShell {
            packages = with pkgs; [ gnucobol.bin gcc gnumake python3 ];
          };
        });
    };
}
