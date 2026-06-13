agda=agda
latex=tectonic

.PHONY: default
default: index.html tex agda

.PHONY: all
all: index.html tex agda haskell

index.html: README.md
	pandoc --standalone --css pandoc.css -t html -o $@ -f gfm $<

.PHONY: tex
tex:
	make -C tex agda=$(agda) latex=$(latex)

.PHONY: agda
agda:
	make -C agda agda=$(agda)

.PHONY: haskell
haskell:
	cabal build

# EOF
