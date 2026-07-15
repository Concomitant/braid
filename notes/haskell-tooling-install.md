# Haskell tooling installation

Installed via apt:

```
apt-get update
apt-get install -y ghc cabal-install haskell-stack
```

Version checks:

```
ghc --version
cabal --version
stack --version
```

Observed versions on Ubuntu 24.04:

```
The Glorious Glasgow Haskell Compilation System, version 9.4.7
cabal-install version 3.8.1.0
stack 2.9.3.1 x86_64
```

## macOS (no local GHC)

No Haskell toolchain installed on the Mac; use Docker with the official
image instead (matches the Ubuntu setup above):

```
docker run --rm -v "$PWD":/w -w /w haskell:9.4-slim cabal test
docker run --rm -v "$PWD":/w -w /w haskell:9.4-slim cabal run braid
```

Tip: compile rather than `runghc` for anything nontrivial — interpreted
runs over the bind mount are slow.
