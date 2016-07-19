src=$(shell find src/ -name \"\*.agda\")

default : all

all : $(src)
	cd ./src && agda README.agda
	./todo.sh
