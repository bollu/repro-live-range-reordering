run:
	./create_ll.sh twodloop.cpp
	opt -S -polly-process-unprofitable -polly-scops -polly-dependences \
			twodloop.llpp -polly-use-llvm-names -debug-only=polly-dependences,polly-scops \
			-polly-dependences-analysis-level=reference-wise -polly-codegen-ppcg  -debug-only=polly-codegen-ppcg
