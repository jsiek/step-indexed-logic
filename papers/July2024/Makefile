paper.pdf: paper.tex latex/July2024/StepIndexedLogic.tex latex/July2024/STLC.tex latex/July2024/STLCDeterministic.tex latex/July2024/STLCBind.tex latex/July2024/STLCSafe.tex latex/July2024/STLCDeterministic.tex
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper

texclean:
	rm -f paper.out paper.aux paper.bbl paper.blg

clean:
	rm -f paper.out paper.aux paper.bbl paper.blg latex/July2024/*


latex/July2024/StepIndexedLogic.tex: StepIndexedLogic.lagda
	agda --latex StepIndexedLogic.lagda

latex/July2024/STLC.tex: STLC.lagda StepIndexedLogic.lagda
	agda --latex STLC.lagda

latex/July2024/STLCDeterministic.tex: STLCDeterministic.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCDeterministic.lagda

latex/July2024/STLCBind.tex: STLCBind.lagda STLCDeterministic.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCBind.lagda

latex/July2024/STLCSafe.tex: STLCSafe.lagda  STLCBind.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCSafe.lagda
