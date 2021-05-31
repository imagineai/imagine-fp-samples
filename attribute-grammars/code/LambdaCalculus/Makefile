
all : infer

infer: Lambda.hs Type.hs
	ghc -o infer Main

Lambda.hs: Lambda.ag Makefile
	uuagc -dcfswH Lambda.ag

Type.hs: Type.ag Makefile
	uuagc -dcfswH Type.ag

clean:
	rm -f infer *.hi *.o Lambda.hs Type.hs
