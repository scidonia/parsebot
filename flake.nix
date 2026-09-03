{
  description = "parsebot — inhabited parsing: certified parser-plan synthesis from declarative grammars";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = inputs @ {flake-parts, ...}:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = ["x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin"];
      perSystem = {pkgs, ...}: {
        devShells.default = pkgs.mkShellNoCC {
          packages = [
            # Rocq 9.1 + stdpp. Iris and InteractionTrees are deliberately absent:
            # the pure core (plan §8.1) needs neither; they arrive with streaming (§5.2).
            (pkgs.rocq-core.withPackages (ps: [ ps.stdpp ]))
          ];
        };
      };
    };
}
