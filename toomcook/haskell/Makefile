build:
	@cabal-dev build --ghc-options="-H64m -rtsopts"

prof:
	@cabal-dev build --ghc-options="-rtsopts -prof -fprof-auto -H64m"

release:
	@cabal-dev build --ghc-options="-fllvm -O2 -H64m"

configure:
	@cabal-dev install \
		--force-reinstalls \
		--enable-library-profiling \
		--enable-executable-profiling
	@cabal-dev configure \
		--enable-library-profiling \
		--enable-executable-profiling \
		--enable-benchmarks \
		--enable-tests

ghci:
	ghci -isrc -fobject-code -outputdir /tmp src/Properties.hs

clean:
	@cabal-dev clean --save-configure

lint:
	@hlint src
