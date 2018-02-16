TARGET     := report
.PHONY: all clean

all: $(TARGET).pdf

$(TARGET).pdf: $(TARGET).tex
	@ latexmk -pdflatex="pdflatex -interaction=nonstopmode" -pdf $(TARGET).tex

clean:
	rm -f *~
	@ latexmk -c -bibtex
