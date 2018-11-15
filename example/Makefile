run:
	./create_ll.sh twodloop.cpp
	opt -analyze -polly-process-unprofitable -polly-scops -polly-dependences \
			twodloop.llpp
