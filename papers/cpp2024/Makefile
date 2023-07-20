paper.pdf: paper.tex latex/cpp2024/StepIndexedLogic.tex latex/cpp2024/STLC.tex latex/cpp2024/STLCDeterministic.tex latex/cpp2024/STLCBind.tex latex/cpp2024/STLCSafe.tex latex/cpp2024/STLCDeterministic.tex
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper

clean:
	rm -f paper.aux latex/cpp2024/*

latex/cpp2024/StepIndexedLogic.tex: StepIndexedLogic.lagda
	agda --latex StepIndexedLogic.lagda

latex/cpp2024/STLC.tex: STLC.lagda StepIndexedLogic.lagda
	agda --latex STLC.lagda

latex/cpp2024/STLCDeterministic.tex: STLCDeterministic.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCDeterministic.lagda

latex/cpp2024/STLCBind.tex: STLCBind.lagda STLCDeterministic.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCBind.lagda

latex/cpp2024/STLCSafe.tex: STLCSafe.lagda  STLCBind.lagda STLC.lagda StepIndexedLogic.lagda
	agda --latex STLCSafe.lagda
