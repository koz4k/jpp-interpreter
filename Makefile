all:
	cabal update
	cabal install mtl
	cabal install STMonadTrans
	happy -gca Parser.y --info=info.txt
	alex -g Lexer.x
	ghc --make Main.hs -o interpreter

clean:
	rm -f *.log *.aux *.hi *.o *.dvi
