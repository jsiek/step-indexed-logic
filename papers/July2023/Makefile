paper.pdf: paper.tex latex/July2023/StepIndexedLogic.tex latex/July2023/SILIntro.tex latex/July2023/SILReference.tex latex/July2023/STLC.tex latex/July2023/STLCDeterministic.tex latex/July2023/STLCBind.tex latex/July2023/STLCSafe.tex latex/July2023/STLCDeterministic.tex
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper

texclean:
	rm -f paper.out paper.aux paper.bbl paper.blg

clean:
	rm -f paper.out paper.aux paper.bbl paper.blg latex/July2023/*


latex/July2023/StepIndexedLogic.tex: StepIndexedLogic.lagda
	agda --latex StepIndexedLogic.lagda

latex/July2023/SILIntro.tex: SILIntro.lagda StepIndexedLogic.lagda
	agda --latex SILIntro.lagda

latex/July2023/SILReference.tex: SILReference.lagda StepIndexedLogic.lagda
	agda --latex SILReference.lagda

latex/July2023/STLC.tex: STLC.lagda StepIndexedLogic.lagda
	agda --latex STLC.lagda

latex/July2023/STLCDeterministic.tex: STLCDeterministic.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCDeterministic.lagda

latex/July2023/STLCBind.tex: STLCBind.lagda STLCDeterministic.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCBind.lagda

latex/July2023/STLCSafe.tex: STLCSafe.lagda  STLCBind.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCSafe.lagda
