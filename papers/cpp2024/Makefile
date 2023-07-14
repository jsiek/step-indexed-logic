paper.pdf: latex/cpp2024/StepIndexedLogic.tex latex/cpp2024/STLC.tex latex/cpp2024/STLCDeterministic.tex latex/cpp2024/STLCBind.tex latex/cpp2024/STLCSafe.tex 
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper
	/Library/TeX/texbin/pdflatex paper
	/Library/TeX/texbin/bibtex paper

clean:
	rm -f paper.aux latex/cpp2024/*

latex/cpp2024/StepIndexedLogic.tex:
	agda --latex StepIndexedLogic.lagda

latex/cpp2024/STLC.tex:
	agda --latex STLC.lagda

latex/cpp2024/STLCDeterministic.tex:
	agda --latex STLCDeterministic.lagda

latex/cpp2024/STLCBind.tex:
	agda --latex STLCBind.lagda

latex/cpp2024/STLCSafe.tex:
	agda --latex STLCSafe.lagda
