AGDA=agda
AFLAGS=-i/Users/ak3n/Develop/agda-stdlib/src -i. --latex
SOURCE=report
#LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'
LATEX=latexmk -pdf -use-make -e '$$pdflatex=q/lualatex %O %S/'

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	cd latex/ && \
	$(LATEX) $(SOURCE).tex && \
	mv $(SOURCE).pdf ..
