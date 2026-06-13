# Build the paper.
# Prerequisites: LaTeX and Agda installed.
agda=agda
latex=pdflatex

.PHONY: default
default: main.pdf html

#main.pdf:
#	latexmk -pdf main
# -interaction=nonstopmode  ## does not work with non-existing files

paper.pdf: main.pdf
	mv $< $@

.PHONY: html
html:
	$(agda) -i ../agda -i . -l standard-library --html References.agda

.PHONY: nix
nix:
	nix-shell --run make

.PHONY: clean
clean:
	rm -f *.aux *.bbl *.blg *.fdb_latexmk *.fls *.log extras.zip
	rm -rf html

.PHONY: ship
ship: extras.zip

extras.zip:
	rm -f $@
	rm -fr agda
	cp -R ../agda .
	cp References.agda agda/
	zip -r $@ README.md html `find agda -name "*.agda"` agda/Main.agda-lib

# destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
# 	  -- 'print.use.tab = OFF' \
# 	  -- 'check.double = ON' \
# 	  -- 'check.double.delete = ON' \
# 	  -- 'delete.field = { abstract }' \
# 	  -- 'delete.field = { dvi }' \
# 	  -- 'delete.field = { postscript }' \
# 	  -- 'delete.field = { pdf }' \
# 	  -- 'delete.field = { month }' \
# 	  -- 'delete.field = { isbn }' \
# 	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }' \
# catcfg=sed -e "s/%.*//g" <
bibliography=all.bib

# stdlib=$(HOME)/agda/std-lib/src

files=jfp-epi.cls Makefile \
  textMacros.tex \
  newunicodedefs.tex \
  latex/Code.tex

# .PHONY : default add all pack ship debugMake html

.PRECIOUS : %.pdf %.tex

latex/%.tex : %.lagda.tex
	$(agda) --latex $<

# default : all # main.pdf

# all : main.pdf long.zip sources.zip

# ship: $(destdir)/main.pdf $(destdir)/main-long.pdf

# $(destdir)/% : %
# 	cp -p -f $< $@

# sources.zip: main.tex acmart.cls
# 	zip $@ $<

# long.zip: main-long.pdf
# 	zip $@ $<

# add : additional-material.tgz

# additional-material.tgz : main-long.pdf
# 	tar czhf $@ $^

# pack : main.zip

# main.zip : main.pdf $(files) jfp1.cls harpoons.sty main.bbl jfp.bst auto-main.bib
# 	zip $@ $^


# # main
# ##################################################################

# clean:
# 	rm -rf latex
# 	rm -f *.pdf

# # main.pdf: latex/main.tex $(files)
# # 	latexmk -f -pdf latex/main.tex

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
main_aux : main.tex $(files)
	-$(latex) $<;
	touch $@;

# then, run bibtex
main.bbl : main_aux auto-main.bib
	-bibtex main;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
main.pdf : main.bbl
	-$(latex) main.tex;
	$(latex) main.tex;

# auto-main.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-main.bib : main_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x main.aux -i $(bibliography) >> $@;
endif
endif

# # main-long
# ##################################################################

# # initially, run latex once to create an .aux file
# # mark .aux file as fresh by creating a stamp _aux
# main-long_aux : latex/main-long.tex $(files)
# 	$(latex) latex/main-long.tex;
# 	touch $@;

# # then, run bibtex
# main-long.bbl : main-long_aux auto-main.bib
# 	-bibtex main-long;

# # finally, finish by running latex twice again
# # this will update .aux, but leave the stamp _aux intact
# # (otherwise we would not converge and make would never
# # return a "Nothing to do")
# main-long.pdf : main-long.bbl
# 	$(latex) latex/main-long.tex;
# 	$(latex) latex/main-long.tex;

# # auto-main-long.bib is only defined if bibtool is present and all.bib exists

# ifneq ($(shell which bibtool),)
# ifneq ($(shell ls $(bibliography)),)
# auto-main-long.bib : main-long_aux $(bibliography)
# 	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
# 	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
# 	echo "" >> $@ ;
# 	$(bibtool) -x main-long.aux -i $(bibliography) >> $@;
# endif
# endif



# # Templates (reverted back to simple templates)


# talk% : talk%.pdf
# 	cp -p $? $(destdir)/;
# 	touch $@;

# talk%.pdf : talk%.tex
# 	pdflatex $<;


# %.tex : %.lhs
# 	lhs2TeX --poly -i lhs2TeX.fmt $< > $@
# # /usr/local/share/lhs2tex-1.13/

# % :  %.pdf # %.dvi %.ps.gz # %.tar.gz
# 	cp -p $? $(destdir)/;
# 	touch $@;

# %.pdf : %.dvi
# 	pdflatex $*.tex;

# %.ps  : %.dvi
# 	dvips -o $@ $<;

# %.gz : %
# 	cat $< | gzip > $@

# ## does not work since $ is evaluated before %
# #%.tar : %.cfg $(shell cat %.cfg)
# #	echo $?


# #EOF
