TMP=tmp
REPORT=mproj

report.pdf: mproj.tex mproj.bib lstcoq.sty mproj.cls images/*
	mkdir -p $(TMP)
	pdflatex -output-directory $(TMP) $(REPORT).tex
	cp mproj.bib $(TMP) && cd $(TMP) && bibtex $(REPORT).aux
	pdflatex -output-directory $(TMP) $(REPORT).tex
	pdflatex -output-directory $(TMP) $(REPORT).tex
	mv $(TMP)/$(REPORT).pdf .

clean:
	rm -r $(TMP)
