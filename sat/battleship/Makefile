battleship: clean File.o Proof.o Solver.o battleship.o 
	g++ -o $@ -std=c++11 -g File.o Proof.o Solver.o battleship.o 

File.o: File.cpp
	g++ -c -std=c++11 -g File.cpp

Proof.o: Proof.cpp
	g++ -c -std=c++11 -g Proof.cpp

Solve.o: Solver.cpp
	g++ -c -std=c++11 -g Solver.cpp

battleship.o: battleship.cpp
	g++ -c -std=c++11 -g battleship.cpp

# ddiagram.o: ddiagram.h
# 	g++ -c -std=c++11 -g ddiagram.h



# utilities.o: utilities.cpp
# 	g++ -c -std=c++11 -g utilities.cpp

clean:
	rm -f *.o battleship tags
