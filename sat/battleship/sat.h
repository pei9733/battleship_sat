/****************************************************************************
  FileName     [ sat.h ]
  PackageName  [ sat ]
  Synopsis     [ Define miniSat solver interface functions ]
  Author       [ Chung-Yang (Ric) Huang, Cheng-Yin Wu ]
  Copyright    [ Copyleft(c) 2010-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef SAT_H
#define SAT_H

#include <cassert>
#include <iostream>
#include "Solver.h"

using namespace std;
class DDnode;
class DDiagram;
class DDnode
{
public:
   Var _x;           // selector
   Var _l;           // left child's Var
   Var _r;           // right child's Var
   Var _pi;          // parent's Var
   DDnode *left;     // pointer to left child;
   DDnode *right;    // pointer to left child;
   DDnode *parent_l; // pointer to left parent;
   DDnode *parent_r; // pointer to right parent;
   int value;
   int _r_assert; // right child is 0
   int _l_assert; // left child is 1

   DDnode() : left(0), right(0), parent_l(0), parent_r(0), value(-1), _x(-1), _l(-1), _r(-1), _pi(-1), _r_assert(-1), _l_assert(-1){};
   DDnode(int _value) : left(0), right(0), parent_l(0), parent_r(0), value(_value), _x(-1), _l(-1), _r(-1), _pi(-1), _r_assert(-1), _l_assert(-1){};
};

/********** MiniSAT_Solver **********/
class SatSolver
{
public:
   SatSolver() : _solver(0) {}
   ~SatSolver()
   {
      if (_solver)
         delete _solver;
   }

   // Solver initialization and reset
   void initialize()
   {
      reset();
      if (_curVar == 0)
      {
         _solver->newVar();
         ++_curVar;
      }
   }
   void reset()
   {
      if (_solver)
         delete _solver;
      _solver = new Solver();
      _assump.clear();
      _curVar = 0;
   }

   // Constructing proof model
   // Return the Var ID of the new Var
   inline Var newVar()
   {
      _solver->newVar();
      return _curVar++;
   }
   // fa/fb = true if it is inverted
   void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb)
   {
      vec<Lit> lits;
      Lit lf = Lit(vf);
      Lit la = fa ? ~Lit(va) : Lit(va);
      Lit lb = fb ? ~Lit(vb) : Lit(vb);
      lits.push(la);
      lits.push(~lf);
      _solver->addClause(lits);
      lits.clear();
      lits.push(lb);
      lits.push(~lf);
      _solver->addClause(lits);
      lits.clear();
      lits.push(~la);
      lits.push(~lb);
      lits.push(lf);
      _solver->addClause(lits);
      lits.clear();
   }
   // fa/fb = true if it is inverted
   void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb)
   {
      vec<Lit> lits;
      Lit lf = Lit(vf);
      Lit la = fa ? ~Lit(va) : Lit(va);
      Lit lb = fb ? ~Lit(vb) : Lit(vb);
      lits.push(~la);
      lits.push(lb);
      lits.push(lf);
      _solver->addClause(lits);
      lits.clear();
      lits.push(la);
      lits.push(~lb);
      lits.push(lf);
      _solver->addClause(lits);
      lits.clear();
      lits.push(la);
      lits.push(lb);
      lits.push(~lf);
      _solver->addClause(lits);
      lits.clear();
      lits.push(~la);
      lits.push(~lb);
      lits.push(~lf);
      _solver->addClause(lits);
      lits.clear();
   }
   void addMUXCNF(Var _f, Var _s, Var _a, Var _b, int _a_assert = -1, int _b_assert = -1) // bool _sf = 1, bool _ss = 1, bool _sa = 1, bool _sb = 1)
   {
      vec<Lit> lits;
      // Lit lf = _sf ? Lit(_f) : ~Lit(_f);
      // Lit ls = _ss ? Lit(_s) : ~Lit(_s);
      // Lit la = _sa ? Lit(_a) : ~Lit(_a);
      // Lit lb = _sb ? Lit(_b) : ~Lit(_b);
      Lit lf = Lit(_f);
      Lit ls = Lit(_s);
      Lit la = Lit(_a);
      Lit lb = Lit(_b);
      if (_a_assert == 1 && _b_assert == 0)
      {
         lits.push(~ls);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         lits.push(ls);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         return;
      }
      else if (_a_assert == 0 && _b_assert == 1)
      {
         lits.push(~ls);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         lits.push(ls);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         return;
      }
      else if (_a_assert == 1) // a = 1
      {
         lits.push(ls);
         lits.push(lb);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         lits.push(~lb);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         lits.push(~ls);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         return;
      }
      else if (_a_assert == 0) // a = 0
      {

         lits.push(ls);
         lits.push(~lb);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         lits.push(lb);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         lits.push(~ls);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         return;
      }
      else if (_b_assert == 1)
      {
         lits.push(~ls);
         lits.push(la);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         lits.push(~la);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         lits.push(ls);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         return;
      }
      else if (_b_assert == 0)
      {

         lits.push(~ls);
         lits.push(~la);
         lits.push(lf);
         addClause(lits);
         lits.clear();
         lits.push(la);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         lits.push(ls);
         lits.push(~lf);
         addClause(lits);
         lits.clear();
         return;
      }

      // 1
      lits.push(~ls);
      lits.push(~lf);
      lits.push(la);
      addClause(lits);
      lits.clear();
      // 2
      lits.push(~ls);
      lits.push(lf);
      lits.push(~la);
      addClause(lits);
      lits.clear();
      // 3
      lits.push(ls);
      lits.push(~lf);
      lits.push(lb);
      addClause(lits);
      lits.clear();
      // 4
      lits.push(ls);
      lits.push(lf);
      lits.push(~lb);
      addClause(lits);
      lits.clear();
      // // 5
      // lits.push(la);
      // lits.push(lb);
      // lits.push(~lf);
      // addClause(lits);
      // lits.clear();
      // // 6
      // lits.push(~la);
      // lits.push(~lb);
      // lits.push(lf);
      // addClause(lits);
      // lits.clear();
   }
   void addExactOne(vec<Var> &v)
   {
      // cout << v.size() << endl;
      vec<Lit> lits;
      for (int i = 0, n = v.size(); i < n; ++i)
         lits.push(Lit(v[i]));
      addClause(lits);
      lits.clear();
      for (int i = 0, n = v.size(); i < n; ++i)
      {
         for (int j = i + 1; j < n; ++j)
         {
            lits.push(~Lit(v[i]));
            lits.push(~Lit(v[j]));
            addClause(lits);
            lits.clear();
         }
      }
   }

   void addSurroundWater(vec<Var> &v, Var _n)
   {
      vec<Lit> lits;
      for (int i = 1, n = v.size(); i < n; ++i)
      {
         lits.push(~Lit(v[i]));
         lits.push(Lit(_n));
         addClause(lits);
         lits.clear();
      }
      lits.clear();
   }
   void addClause_3var(Var _2, Var _5, Var _neg_1)
   {
      vec<Lit> lits;
      lits.push(Lit(_2));
      lits.push(Lit(_5));
      lits.push(~Lit(_neg_1));
      addClause(lits);
      lits.clear();
   }

   void addClause_2var(Var _neg_v1, Var _v2)
   {
      vec<Lit> lits;
      lits.push(~Lit(_neg_v1));
      lits.push(Lit(_v2));
      addClause(lits);
      lits.clear();
   }

   void addClause_5var(Var _v1, Var _v2, Var _v3, Var _v4, Var _neg_v5)
   {
      vec<Lit> lits;
      lits.push(~Lit(_neg_v5));
      lits.push(Lit(_v1));
      lits.push(Lit(_v2));
      lits.push(Lit(_v3));
      lits.push(Lit(_v4));
      addClause(lits);
      lits.clear();
   }

   void addClause_single(Var _v1, Var _v2)
   {
      vec<Lit> lits;
      lits.push(~Lit(_v1));
      lits.push(~Lit(_v2));
      addClause(lits);
      lits.clear();
   }

   void addClause_single_twopos(Var _v1, Var _v2)
   {
      vec<Lit> lits;
      lits.push(~Lit(_v1));
      lits.push(Lit(_v2));
      addClause(lits);
      lits.clear();
   }

   void addClause_PB_eq(vec<Var> &_V, int _target); // PB : abbreviation of Pseudo Boolean Constraint
   void addClause_PB_ineq(vec<Var> &_V, int _target, Var f_test, bool isftrue);
   void addClause_sf_6(vec<Var> &_V, vec<Var> &_Lsi)
   {
      for (int i = 1, n = _V.size(); i < n; ++i)
         addClause_single_twopos(_V[i], _Lsi[i]);
   }
   // void addClause_len_6(SatSolver &solver, vector<Cell *> &cells, int _L, int _i, int _J) is at utilities.h
   // For incremental proof, use "assumeSolve()"
   void assumeRelease()
   {
      _assump.clear();
   }
   void assumeProperty(Var prop, bool val)
   {
      _assump.push(val ? Lit(prop) : ~Lit(prop));
   }
   bool assumpSolve() { return _solver->solve(_assump); }

   // For one time proof, use "solve"
   void assertProperty(Var prop, bool val)
   {
      _solver->addUnit(val ? Lit(prop) : ~Lit(prop));
   }
   bool solve()
   {
      _solver->solve();
      return _solver->okay();
   }

   // Functions about Reporting
   // Return 1/0/-1; -1 means unknown value
   int getValue(Var v) const
   {
      return (_solver->modelValue(v) == l_True ? 1 : (_solver->modelValue(v) == l_False ? 0 : -1));
   }
   void printStats() const { const_cast<Solver *>(_solver)->printStats(); }
   void addClause(const vec<Lit> &lits)
   {
      _solver->addClause(lits);
   }
   void buildDiagram_ineq(vec<Var> &_V, vector<vector<DDnode>> &pseudoDDiagram, int _target);
   void buildDiagram_eq(vec<Var> &_V, vector<vector<DDnode>> &pseudoDDiagram, int _target);

private:
   Solver *_solver;  // Pointer to a Minisat solver
   Var _curVar;      // Variable currently
   vec<Lit> _assump; // Assumption List for assumption solve
};

class DDiagram
{
private:
   DDnode *root;

public:
   int *height_MAX;
   DDiagram() : root(0){};
   DDnode *getroot() { return root; }
   void setroot(DDnode *_root) { root = _root; }
};
void SatSolver::buildDiagram_ineq(vec<Var> &_V, vector<vector<DDnode>> &pseudoDDiagram, int _target)
{
   int len = _V.size();
   if (_target > len)
   {
      cerr << "in buildDiagram_ineq : "
           << "_target > len" << endl;
      exit(0);
      return;
   }
   // cout << "len = " << len << endl;
   // vector<vector<DDnode>> pseudoDDiagram;
   for (int i = 0; i < _target; ++i) // initialize every node with their selector
   {
      for (int j = 0, n = len - _target + 1; j < n; ++j)
      {
         DDnode tmp;
         tmp._x = _V[i + j];
         pseudoDDiagram[i][j] = tmp;
      }
   }
   for (int i = 0, n = len - _target + 1; i < _target; ++i) // 把每一條右斜的line中的node連起來
   {
      for (int j = 0, N = n - 1; j < N; ++j)
      {
         DDnode &node = pseudoDDiagram[i][j];
         DDnode &node_R = pseudoDDiagram[i][j + 1];
         Var var_r = newVar();
         // right child
         node._r = var_r;
         node_R._pi = var_r;
         if (i == _target - 1)
            node._l_assert = 1;
      }
      DDnode &tmp = pseudoDDiagram[i][n - 1];
      // cout << " i  = " << i << ", i + n - 1 = " << i + n - 1 << endl;
      tmp._r_assert = 0;
      if (i == _target - 1)
      {
         // cout << "I'm here\n";
         tmp._l_assert = 1;
      }
   }

   for (int i = 0, n = len - _target + 1; i < _target - 1; ++i) // 把每一條右斜的line中跟他的下一條連起來
   {
      for (int j = 0; j < n; ++j)
      {
         DDnode &node = pseudoDDiagram[i][j];
         DDnode &node_L = pseudoDDiagram[i + 1][j];
         if (node._l != -1)
            node_L._pi = node._l;
         else if (node_L._pi != -1)
            node._l = node_L._pi;
         else
         {
            Var tmp = newVar();
            node._l = tmp;
            node_L._pi = tmp;
         }
      }
   }
}

void SatSolver::buildDiagram_eq(vec<Var> &_V, vector<vector<DDnode>> &pseudoDDiagram, int _target)
{
   int len = _V.size();
   if (_target > len)
   {
      cerr << "in buildDiagram_eq : "
           << "_target > len" << endl;
      exit(0);
      return;
   }
   for (int i = 0; i <= _target; ++i) // initialize every node with their selector
   {
      for (int j = 0, n = len - _target + 1; j < n; ++j)
      {
         if (i == _target && j == n - 1)
            break;
         DDnode tmp;
         tmp._x = _V[i + j];
         pseudoDDiagram[i][j] = tmp;
      }
   }

   for (int i = 0, n = len - _target + 1; i < _target; ++i) // 把每一條右斜的line中的node連起來(前K條)
   {
      for (int j = 0, N = n - 1; j < N; ++j)
      {
         DDnode &node = pseudoDDiagram[i][j];
         DDnode &node_R = pseudoDDiagram[i][j + 1];
         Var var_r = newVar();
         // right child
         node._r = var_r;
         node_R._pi = var_r;
         // if (i == _target - 1)
         //    node._l_assert = 1;
      }
      DDnode &tmp = pseudoDDiagram[i][n - 1];

      tmp._r_assert = 0;
      // if (i == _target - 1)
      // {

      //    tmp._l_assert = 1;
      // }
   }
   pseudoDDiagram[_target - 1][len - _target]._l_assert = 1;           //最右下那個點
   for (int I = _target, j = 0, n = len - _target + 1 - 1; j < n; ++j) //把每一條右斜的line中的node連起來(第 k + 1 條)
   {
      DDnode &node = pseudoDDiagram[I][j];
      node._l_assert = 0;
      if (j == n - 1)
      {
         node._r_assert = 1;
         break;
      }
      DDnode &node_R = pseudoDDiagram[I][j + 1];
      Var var_r = newVar();
      node._r = var_r;
      node_R._pi = var_r;
   }
   for (int i = 0, n = len - _target + 1; i < _target; ++i) // 把每一條右斜的line中跟他的下一條連起來
   {
      for (int j = 0; j < n; ++j)
      {
         if (i == _target - 1 && j == n - 1)
            continue;
         DDnode &node = pseudoDDiagram[i][j];
         DDnode &node_L = pseudoDDiagram[i + 1][j];
         if (node._l != -1)
            node_L._pi = node._l;
         else if (node_L._pi != -1)
            node._l = node_L._pi;
         else
         {
            Var tmp = newVar();
            node._l = tmp;
            node_L._pi = tmp;
         }
      }
   }
}

void SatSolver::addClause_PB_eq(vec<Var> &_V, int _target)
{

   DDiagram DDtest;
   vector<vector<DDnode>> pseudoDDnodetest;
   int k_tmp = _target, N_tmp = _V.size();
   if (k_tmp > N_tmp)
   {
      cerr << "in addClause_PB_eq : "
           << "_target > _V.size()" << endl;
      exit(0);
      return;
   }
   else if (_target == 1)
   {
      addExactOne(_V);
      return;
   }
   else if (_target == 0)
   {
      vec<Lit> lits;
      for (int i = 0; i < N_tmp; ++i)
      {
         lits.push(~Lit(_V[i]));
         addClause(lits);
         lits.clear();
      }

      return;
   }
   else if (_target == N_tmp)
   {
      vec<Lit> lits;
      for (int i = 0; i < N_tmp; ++i)
      {
         lits.push(Lit(_V[i]));
         addClause(lits);
         lits.clear();
      }

      return;
   }
   for (int i = 0; i < k_tmp + 1; ++i) // k + 1
   {
      vector<DDnode> tmp;
      for (int j = 0; j < N_tmp - k_tmp + 1; ++j) // N - k + 1
      {
         if (i == k_tmp && j == N_tmp - k_tmp - 1)
            continue;
         tmp.push_back(DDnode(-1));
      }
      pseudoDDnodetest.push_back(tmp);
   }

   // for (int i = 0; i < N_tmp; ++i)
   //    _V.push(newVar());
   buildDiagram_eq(_V, pseudoDDnodetest, k_tmp);

   Var f_test = newVar();
   assertProperty(f_test, true);
   addMUXCNF(f_test, pseudoDDnodetest[0][0]._x, pseudoDDnodetest[0][0]._l, pseudoDDnodetest[0][0]._r);
   // cout << " N = " << pseudoDDnodetest.size() << endl;
   // cout << "n = " << pseudoDDnodetest[3].size() << endl;
   // pseudoDDnodetest[3][2];

   for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
   {
      for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
      {
         // cout << "i = " << i << " , j = " << j << endl;
         if (!i && !j)
            continue;
         // cout << "i + j = " << i + j << endl;
         DDnode &tmp = pseudoDDnodetest[i][j];

         Var *params = new Var[4];
         params[0] = tmp._pi; // parent's Var
         params[1] = tmp._x;  // selector
         params[2] = tmp._l;  // left child's Var
         params[3] = tmp._r;  // right child's Var
         // for (int J = 0; J < 4; ++J)
         //    cout << params[J] << " ";
         // cout << endl;
         if (j == n - 1 && (i == N - 1 || i == N - 2))
         {
            params[2] = tmp._l_assert;
            params[3] = tmp._r_assert;
            addMUXCNF(params[0], params[1], params[2], params[3], params[2], params[3]);
         }
         else if (i == N - 1)
         {
            params[2] = tmp._l_assert;
            // cout << params[0] << ' ' << params[1] << ' ' << params[2] << ' ' << params[3] << endl;
            addMUXCNF(params[0], params[1], params[2], params[3], params[2], -1);
         }
         else if (j == n - 1)
         {

            params[3] = tmp._r_assert;
            addMUXCNF(params[0], params[1], params[2], params[3], -1, params[3]);
         }

         else
            addMUXCNF(params[0], params[1], params[2], params[3], -1, -1);
         delete[] params;
      }
   }
}

void SatSolver::addClause_PB_ineq(vec<Var> &_V, int _target, Var f_test, bool isftrue = false)
{
   DDiagram DDtest;
   vector<vector<DDnode>> pseudoDDnodetest;
   int k_tmp = _target, N_tmp = _V.size();
   if (k_tmp > N_tmp)
   {
      cerr << "in addClause_PB_ineq : "
           << "_target > _V.size()" << endl;
      exit(0);
      return;
   }
   else if (k_tmp == N_tmp)
      return addClause_PB_eq(_V, _target);
   else if (!_target)
      return;
   for (int i = 0; i < k_tmp; ++i) // k
   {
      vector<DDnode> tmp;
      for (int j = 0; j < N_tmp - k_tmp + 1; ++j) // N - k + 1
      {
         tmp.push_back(DDnode(-1));
      }
      pseudoDDnodetest.push_back(tmp);
   }
   buildDiagram_ineq(_V, pseudoDDnodetest, k_tmp);
   // cout << "BDD size = " << pseudoDDnodetest[0].size() << endl;
   // for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
   // {
   //    for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
   //    {
   //       cout << pseudoDDnodetest[i][j]._pi << ' ' << pseudoDDnodetest[i][j]._l << ' ' << pseudoDDnodetest[i][j]._r << ' ' << pseudoDDnodetest[i][j]._l_assert << ' '
   //            << pseudoDDnodetest[i][j]._r_assert << '/';
   //    }
   //    cout << endl;
   // }

   if (isftrue)
      assertProperty(f_test, true);
   // assertProperty(f_test, false);
   if (_target == 1)
      addMUXCNF(f_test, pseudoDDnodetest[0][0]._x, pseudoDDnodetest[0][0]._l_assert, pseudoDDnodetest[0][0]._r);
   else
      addMUXCNF(f_test, pseudoDDnodetest[0][0]._x, pseudoDDnodetest[0][0]._l, pseudoDDnodetest[0][0]._r);
   for (int i = 0, N = pseudoDDnodetest.size(); i < N; ++i)
   {
      for (int j = 0, n = pseudoDDnodetest[i].size(); j < n; ++j)
      {
         if (!i && !j)
            continue;
         // cout << "i + j = " << i + j << endl;
         DDnode &tmp = pseudoDDnodetest[i][j];
         Var *params = new Var[4];
         params[0] = tmp._pi; // parent's Var
         params[1] = tmp._x;  // selector
         params[2] = tmp._l;  // left child's Var
         params[3] = tmp._r;  // right child's Var
         if (i == N - 1 && j == n - 1)
         {
            params[2] = tmp._l_assert;
            params[3] = tmp._r_assert;
            addMUXCNF(params[0], params[1], params[2], params[3], params[2], params[3]);
         }
         else if (i == N - 1)
         {
            params[2] = tmp._l_assert;
            // cout << params[0] << ' ' << params[1] << ' ' << params[2] << ' ' << params[3] << endl;
            addMUXCNF(params[0], params[1], params[2], params[3], params[2], -1);
         }
         else if (j == n - 1)
         {
            params[3] = tmp._r_assert;
            addMUXCNF(params[0], params[1], params[2], params[3], -1, params[3]);
         }

         else
            addMUXCNF(params[0], params[1], params[2], params[3], -1, -1);
         delete[] params;
      }
   }
}
#endif // SAT_H
