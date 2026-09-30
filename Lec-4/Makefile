all: main.o
	./main.o

main.o: main.cpp prop.cpp ND.cpp
	g++ main.cpp prop.cpp ND.cpp -o main.o

clean:
	rm main.o