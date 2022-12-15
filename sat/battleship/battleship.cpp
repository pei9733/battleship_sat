#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <limits>
#include <chrono>
#include "sat.h"
#include "battleship.h"
#include "utilities.h"

using namespace std;

class Gate
{
public:
   Gate(unsigned i = 0) : _gid(i) {}
   ~Gate() {}

   Var getVar() const { return _var; }
   void setVar(const Var &v) { _var = v; }

private:
   unsigned _gid; // for debugging purpose...
   Var _var;
};

//
//[0] PI  1 (a)
//[1] PI  2 (b)
//[2] AIG 4 1 2
//[3] PI  3 (c)
//[4] AIG 5 1 3
//[5] AIG 6 !4 !5
//[6] PO  9 !6
//[7] AIG 7 !2 !3
//[8] AIG 8 !7 1
//[9] PO  10 8
//
vector<Gate *> gates;

vector<Cell *> cells;

void initCircuit()
{
   // Init gates
   gates.push_back(new Gate(1));  // gates[0]
   gates.push_back(new Gate(2));  // gates[1]
   gates.push_back(new Gate(4));  // gates[2]
   gates.push_back(new Gate(3));  // gates[3]
   gates.push_back(new Gate(5));  // gates[4]
   gates.push_back(new Gate(6));  // gates[5]
   gates.push_back(new Gate(9));  // gates[6]
   gates.push_back(new Gate(7));  // gates[7]
   gates.push_back(new Gate(8));  // gates[8]
   gates.push_back(new Gate(10)); // gates[9]

   // POs are not needed in this demo example
}

void initBoard(SatSolver &solver, Board &board, int I, int J) // I*i+j
{
   for (int i = 0; i < (I + 2) * (J + 2); ++i)
   {
      cells.push_back(new Cell(i));
      cells[i]->setVar(i);
   }
   board.setLs(solver);
}

void genProofModel(SatSolver &solver, Board &board)
{
   vec<vec<Var>> rowTally(board.getI());
   vec<vec<Var>> colTally(board.getJ());
   vec<vec<Var>> LTally(board.getL());
   // Allocate and record variables; No Var ID for POs
   for (size_t i = 0, n = cells.size(), I = board.getI(), J = board.getJ(); i < n; ++i)
   {
      cells[i]->setCellVariable(solver, board);
      if (i < (1 * (J + 2) + 1) || i > (I * (J + 2) + J) || (i % (J + 2) == 0) || (i % (J + 2) == (J + 1)))
         solver.assertProperty(cells[i]->getXs()[0], true);
   }
   for (int i = 0, n = cells.size(); i < n; ++i) // (1) & (2)
   {
      solver.addExactOne(cells[i]->getXs()); // (1)
      Var initsegment = cells[i]->getinitseg();
      if (initsegment != -1) //(2)
      {
         solver.assertProperty(cells[i]->getXs()[initsegment], true);
      }
   }
   for (size_t I = board.getI(), J = board.getJ(), i = (1 * (J + 2) + 1), n = (I * (J + 2) + J); i <= n; ++i)
   {
      if ((i % (J + 2) == 0) || (i % (J + 2) == (J + 1)))
         continue;
      push_segments(rowTally[i / (J + 2) - 1], cells[i]->getXs());                                      // (3)
      push_segments(colTally[i % (J + 2) - 1], cells[i]->getXs());                                      // (4)
      solver.addClause_2var(cells[i]->getSs()[0], cells[i]->getXs()[6]);                                // (5) - 1
      solver.addClause_2var(cells[i]->getXs()[6], cells[i]->getSs()[0]);                                // (5) - 2
      solver.addClause_sf_6(cells[i]->getSs(), board.getLs()[(i / (J + 2) - 1) * J + i % (J + 2) - 1]); // (6) - 1
      addClause_len_6(solver, board, cells, board.getL(), i, I, J);                                     //(6) - 2
      push_segLength(LTally, cells[i]->getSs());                                                        // (7)
      solver.addSurroundWater(cells[i]->getXs(), cells[i + J + 3]->getXs()[0]);                         // (8) - 1
      // solver.addSurroundWater(cells[i - J - 3]->getXs(), cells[i]->getXs()[0]);                        // (8) - 2
      // solver.addSurroundWater(cells[i]->getXs(), cells[i - J - 1]->getXs()[0]); // (9) - 1
      solver.addSurroundWater(cells[i - J - 1]->getXs(), cells[i]->getXs()[0]);                        // (9) - 2
      solver.addClause_3var(cells[i + 1]->getXs()[2], cells[i + 1]->getXs()[5], cells[i]->getXs()[1]); // (10)
      if (i % (J + 2) != 1)
         solver.addClause_2var(cells[i]->getXs()[1], cells[i - 1]->getXs()[0]); // (11)
      else if (i % (J + 2) != J)
         solver.addClause_2var(cells[i]->getXs()[2], cells[i + 1]->getXs()[0]); // (12)

      solver.addClause_3var(cells[i - 1]->getXs()[1], cells[i - 1]->getXs()[5], cells[i]->getXs()[2]);         // (13)
      solver.addClause_3var(cells[i + J + 2]->getXs()[4], cells[i + J + 2]->getXs()[5], cells[i]->getXs()[3]); // (14)
      if ((i / (J + 2)) != 1)
         solver.addClause_2var(cells[i]->getXs()[3], cells[i - J - 2]->getXs()[0]); // (15)
      else if ((i / (J + 2)) != I)
         solver.addClause_2var(cells[i]->getXs()[4], cells[i + J + 2]->getXs()[0]);                                                                                // (16)
      solver.addClause_3var(cells[i - J - 2]->getXs()[3], cells[i - J - 2]->getXs()[5], cells[i]->getXs()[4]);                                                     // (17)
      solver.addClause_5var(cells[i - J - 2]->getXs()[3], cells[i - J - 2]->getXs()[5], cells[i + 1]->getXs()[2], cells[i + 1]->getXs()[5], cells[i]->getXs()[5]); //(18)
      solver.addClause_5var(cells[i - J - 2]->getXs()[3], cells[i - J - 2]->getXs()[5], cells[i - 1]->getXs()[1], cells[i - 1]->getXs()[5], cells[i]->getXs()[5]); //(19)
      solver.addClause_5var(cells[i + J + 2]->getXs()[4], cells[i + J + 2]->getXs()[5], cells[i - 1]->getXs()[1], cells[i - 1]->getXs()[5], cells[i]->getXs()[5]); // (20)
      solver.addClause_5var(cells[i + J + 2]->getXs()[4], cells[i + J + 2]->getXs()[5], cells[i + 1]->getXs()[2], cells[i + 1]->getXs()[5], cells[i]->getXs()[5]);
      solver.addClause_single(cells[i - 1]->getXs()[6], cells[i]->getXs()[6]);     //(22)
      solver.addClause_single(cells[i - J - 2]->getXs()[6], cells[i]->getXs()[6]); //(23)
      // solver.addClause_single(cells[i - J - 2]->getXs()[6], cells[i]->getXs()[0]); //(24)
      // solver.addClause_single(cells[i - J + 2]->getXs()[6], cells[i]->getXs()[0]); //(25)
   }

   for (int i = 0, n = board.getI(); i < n; ++i)
      solver.addClause_PB_eq(rowTally[i], board.getRi(i)); //(3)
   for (int i = 0, n = board.getJ(); i < n; ++i)
      solver.addClause_PB_eq(colTally[i], board.getCi(i)); //(4)
   for (int i = 0, n = board.getL(); i < n; ++i)
      solver.addClause_PB_eq(LTally[i], board.getSi(i)); // (7)
}

void reportResult(const SatSolver &solver, bool result, int I, int J)
{
   solver.printStats();
   cout << (result ? "SAT" : "UNSAT") << endl;
   if (result)
   {

      int tmp = 0;
      for (size_t i = (1 * (J + 2) + 1), n = (I * (J + 2) + J), k = 0; i <= n; ++i, ++k)
      {
         if ((i % (J + 2) == 0) || (i % (J + 2) == (J + 1)))
            continue;
         else if ((i % (J + 2)) == 1 && i != (1 * (J + 2) + 1))
            cout << endl;
         for (int j = 0; j < 7; ++j)
         {
            int val = solver.getValue(cells[i]->getXs()[j]);
            if (val)
               print_result(j);
            // cout << val << ' ';
         }
         // cout << endl;
         // ++tmp;

         //////
      }
      // cout << "\n\n";
      // for (size_t i = (1 * (J + 2) + 1), n = (I * (J + 2) + J), k = 0; i <= n; ++i, ++k)
      // {
      //    if ((i % (J + 2) == 0) || (i % (J + 2) == (J + 1)))
      //    {
      //       cout << "======================\n";
      //       continue;
      //    }
      //    // else if ((i % (J + 2)) == 1 && i != (1 * (J + 2) + 1))
      //    //    cout << endl;
      //    for (int j = 0; j < 7; ++j)
      //    {
      //       int val = solver.getValue(cells[i]->getXs()[j]);
      //       // if (val)
      //       //    print_result(j);
      //       cout << val << ' ';
      //    }
      //    cout << endl;
      //    ++tmp;
      //    //////
      // }
      // cout << "\ntmp = " << tmp << endl;
   }
}

void reporttestResult(SatSolver &solver, bool result, vec<Var> &_V)
{
   solver.printStats();
   cout << (result ? "SAT" : "UNSAT") << endl;
   if (result)
   {
      vec<Lit> lits;
      for (int i = 0; i < _V.size(); ++i)
      {
         Var val = solver.getValue(_V[i]);
         lits.push((val ? ~Lit(_V[i]) : Lit(_V[i])));
         cout << val << ' ';
      }
      solver.addClause(lits);
      lits.clear();
   }
   cout << endl;
}

int main(int argc, char *argv[])
{
   using std::chrono::duration;
   using std::chrono::duration_cast;
   using std::chrono::high_resolution_clock;
   using std::chrono::milliseconds;
   auto t1 = high_resolution_clock::now();
   // initCircuit();
   SatSolver solver;
   Board board;
   solver.initialize();
   // file reading

   ifstream fin(argv[1]);
   Var inputbuffer1, inputbuffer2, inputbuffer3;
   fin >> inputbuffer1;
   board.setL(inputbuffer1);
   for (int i = 0, n = inputbuffer1; i < n; ++i)
   {
      fin >> inputbuffer1;
      board.S_push(inputbuffer1);
   }

   fin >> inputbuffer1 >> inputbuffer2;
   board.setI(inputbuffer1);
   board.setJ(inputbuffer2);
   initBoard(solver, board, board.getI(), board.getJ());
   string row_tally = "", col_tally = "";
   fin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
   getline(fin, row_tally);
   getline(fin, col_tally);
   split(row_tally, board._R, ',');
   split(col_tally, board._C, ',');
   while (fin >> inputbuffer1 >> inputbuffer2 >> inputbuffer3)
   {
      cells[(inputbuffer1 + 1) * (board.getJ() + 2) + (inputbuffer2 + 1)]->setinitseg(inputbuffer3); // i * (J + 2) + j
   }
   genProofModel(solver, board);
   // cells[35]->printSs();
   // printvector("cells", cells);

   bool result = true;
   // vec<Var> varstest;
   // for (int i = 0; i < 4; ++i)
   //    varstest.push(solver.newVar());
   // solver.addMUXCNF(varstest[0], varstest[1], varstest[2], varstest[3], -1, 0);
   solver.assumeRelease(); // Clear assumptions
   // solver.assumeProperty(newV, true); // k = 1
   // solver.assertProperty(varstest[3], 1);
   result = solver.assumpSolve();

   reportResult(solver, result, board.getI(), board.getJ());

   // reporttestResult(solver, result, DDtestv);

   cout << endl
        << endl
        << "======================" << endl;
   auto t2 = high_resolution_clock::now();
   /* Getting number of milliseconds as an integer. */
   auto ms_int = duration_cast<milliseconds>(t2 - t1);

   /* Getting number of milliseconds as a double. */
   duration<double, std::milli> ms_double = t2 - t1;

   // std::cout << ms_int.count() << "ms\n";
   std::cout << ms_double.count() << "ms\n";
   return 0;

   {
       // bool result = true;
       // DDiagram DDtest;
       // vec<Var> DDtestv;
       // vector<vector<DDnode>> pseudoDDnodetest;
       // int k_tmp = 4, n_tmp = 5;
       // for (int i = 0; i < k_tmp; ++i) // k
       // {
       //    vector<DDnode> tmp;
       //    for (int j = 0; j < n_tmp - k_tmp + 1; ++j) // N - k + 1
       //    {
       //       tmp.push_back(DDnode(-1));
       //    }
       //    pseudoDDnodetest.push_back(tmp);
       // }
       // for (int i = 0; i < n_tmp; ++i)
       //    DDtestv.push(solver.newVar());
       // solver.addClause_PB_ineq(DDtestv, k_tmp); // 0,1不行
       // // solver.buildDiagram_ineq(DDtestv, pseudoDDnodetest, k_tmp);
       // // for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
       // // {
       // //    for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
       // //    {
       // //       cout << pseudoDDnodetest[i][j]._pi << ' ' << (pseudoDDnodetest[i][j]._l_assert ? pseudoDDnodetest[i][j]._l_assert : pseudoDDnodetest[i][j]._l) << ' '
       // //            << ((!pseudoDDnodetest[i][j]._r_assert) ? pseudoDDnodetest[i][j]._r_assert : pseudoDDnodetest[i][j]._r) << '/';
       // //    }
       // //    cout << endl;
       // // }

       // // Var f_test = solver.newVar();
       // // solver.assertProperty(f_test, true);
       // // solver.addMUXCNF(f_test, pseudoDDnodetest[0][0]._x, pseudoDDnodetest[0][0]._l, pseudoDDnodetest[0][0]._r);
       // // for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
       // // {
       // //    for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
       // //    {
       // //       if (!i && !j)
       // //          continue;
       // //       // cout << "i + j = " << i + j << endl;
       // //       DDnode &tmp = pseudoDDnodetest[i][j];
       // //       Var *params = new Var[4];
       // //       params[0] = tmp._pi; // parent's Var
       // //       params[1] = tmp._x;  // selector
       // //       params[2] = tmp._l;  // left child's Var
       // //       params[3] = tmp._r;  // right child's Var
       // //       if (i == N - 1 && j == n - 1)
       // //       {
       // //          params[2] = tmp._l_assert;
       // //          params[3] = tmp._r_assert;
       // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], params[2], params[3]);
       // //       }
       // //       else if (i == N - 1)
       // //       {
       // //          params[2] = tmp._l_assert;
       // //          // cout << params[0] << ' ' << params[1] << ' ' << params[2] << ' ' << params[3] << endl;
       // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], params[2], -1);
       // //       }
       // //       else if (j == n - 1)
       // //       {
       // //          params[3] = tmp._r_assert;
       // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], -1, params[3]);
       // //       }

       // //       else
       // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], -1, -1);
       // //       delete[] params;
       // //    }
       // // }

       // // solver.addXorCNF(newV, gates[5]->getVar(), false, gates[8]->getVar(), true);
       // int counter = 0;
       // for (; result;)
       // {
       //    ++counter;
       //    solver.assumeRelease(); // Clear assumptions
       //    // solver.assumeProperty(newV, true); // k = 1
       //    // solver.assertProperty(varstest[3], 1);
       //    result = solver.assumpSolve();

       //    // reportResult(solver, result, board.getI(), board.getJ());

       //    reporttestResult(solver, result, DDtestv);

       //    cout << endl
       //         << endl
       //         << "======================" << endl;
       // }
       // cout << "counter = " << counter - 1 << endl;
   }

   {
      // DDiagram DDtest;
      // vec<Var> DDtestv;
      // vector<vector<DDnode>> pseudoDDnodetest;
      // int k_tmp = 5, N_tmp = 5;
      // for (int i = 0; i < k_tmp + 1; ++i) // k + 1
      // {
      //    vector<DDnode> tmp;
      //    for (int j = 0; j < N_tmp - k_tmp + 1; ++j) // N - k + 1
      //    {
      //       if (i == k_tmp && j == N_tmp - k_tmp - 1)
      //          continue;
      //       tmp.push_back(DDnode(-1));
      //    }
      //    pseudoDDnodetest.push_back(tmp);
      // }
      // for (int i = 0; i < N_tmp; ++i)
      //    DDtestv.push(solver.newVar());
      // solver.addClause_PB_eq(DDtestv, k_tmp);
      // // solver.buildDiagram_eq(DDtestv, pseudoDDnodetest, k_tmp);
      // // for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
      // // {
      // //    for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
      // //    {
      // //       cout << pseudoDDnodetest[i][j]._pi << ' ' << pseudoDDnodetest[i][j]._l << ' ' << pseudoDDnodetest[i][j]._r << ' ' << pseudoDDnodetest[i][j]._l_assert << ' '
      // //            << pseudoDDnodetest[i][j]._r_assert << '/';
      // //    }
      // //    cout << endl;
      // // }
      // // Var f_test = solver.newVar();
      // // solver.assertProperty(f_test, true);
      // // solver.addMUXCNF(f_test, pseudoDDnodetest[0][0]._x, pseudoDDnodetest[0][0]._l, pseudoDDnodetest[0][0]._r);
      // // // cout << " N = " << pseudoDDnodetest.size() << endl;
      // // // cout << "n = " << pseudoDDnodetest[3].size() << endl;
      // // // pseudoDDnodetest[3][2];
      // // for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
      // // {
      // //    for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
      // //    {
      // //       // cout << "i = " << i << " , j = " << j << endl;
      // //       if (!i && !j)
      // //          continue;
      // //       // cout << "i + j = " << i + j << endl;
      // //       DDnode &tmp = pseudoDDnodetest[i][j];
      // //       Var *params = new Var[4];
      // //       params[0] = tmp._pi; // parent's Var
      // //       params[1] = tmp._x;  // selector
      // //       params[2] = tmp._l;  // left child's Var
      // //       params[3] = tmp._r;  // right child's Var
      // //       // for (int J = 0; J < 4; ++J)
      // //       //    cout << params[J] << " ";
      // //       // cout << endl;
      // //       if (j == n - 1 && (i == N - 1 || i == N - 2))
      // //       {
      // //          params[2] = tmp._l_assert;
      // //          params[3] = tmp._r_assert;
      // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], params[2], params[3]);
      // //       }
      // //       else if (i == N - 1)
      // //       {
      // //          params[2] = tmp._l_assert;
      // //          // cout << params[0] << ' ' << params[1] << ' ' << params[2] << ' ' << params[3] << endl;
      // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], params[2], -1);
      // //       }
      // //       else if (j == n - 1)
      // //       {

      // //          params[3] = tmp._r_assert;
      // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], -1, params[3]);
      // //       }
      // //       else
      // //          solver.addMUXCNF(params[0], params[1], params[2], params[3], -1, -1);
      // //       delete[] params;
      // //    }
      // // }
      // int count = 0;
      // for (; result;)
      // {
      //    ++count;
      //    solver.assumeRelease(); // Clear assumptions
      //    // solver.assumeProperty(newV, true); // k = 1
      //    // solver.assertProperty(varstest[3], 1);
      //    result = solver.assumpSolve();

      //    // reportResult(solver, result, board.getI(), board.getJ());

      //    reporttestResult(solver, result, DDtestv);

      //    cout << endl
      //         << endl
      //         << "======================" << endl;
      // }
      // cout << "count = " << count << endl;
   }
   // // k = Solve(Gate(3) & !Gate(7))
   // newV = solver.newVar();
   // solver.addAigCNF(newV, gates[3]->getVar(), false, gates[7]->getVar(), true);
   // solver.assumeRelease();            // Clear assumptions
   // solver.assumeProperty(newV, true); // k = 1
   // result = solver.assumpSolve();
   // reportResult(solver, result);
}
