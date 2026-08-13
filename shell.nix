{ nixpkgs ? import <nixpkgs> {} }:
with nixpkgs;
let
  ghc = haskellPackages.ghcWithPackages (ps: with ps; [
          glew
          SDL2
          zlib
          libz
          libGL
          libGLU
          freeglut
          pkg-config
        ]);
in
stdenv.mkDerivation {
  LD_LIBRARY_PATH="/run/opengl-driver/lib:/run/opengl-driver-32/lib";
  SDL_VIDEODRIVER="wayland";
  name = "my-haskell-env";
  buildInputs = [ ghc zlib pkg-config glew libz SDL2 libGL ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
