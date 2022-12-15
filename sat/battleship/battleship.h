#ifndef BATTLESHIP_H
#define BATTLESHIP_H
#include "sat.h"

using namespace std;

class Board
{
public:
    vec<Var> _R; // row tally         // (x - x % I)/I
    vec<Var> _C; // column tally      // x % I
    Board(unsigned i = 0) : _gid(i) {}
    ~Board() {}

    Var getI() const { return _I; }
    void setI(const Var &v) { _I = v; }

    Var getJ() const { return _J; }
    void setJ(const Var &v) { _J = v; }

    Var getL() const { return _L; }
    void setL(const Var &v) { _L = v; }

    Var getRi(int i) { return _R[i]; }
    void setRi(const Var &v, int i) { _R[i] = v; }

    Var getCi(int i) { return _C[i]; }
    void setCi(const Var &v, int i) { _C[i] = v; }

    vec<Var> &getS() { return _S; }
    Var getSi(int i) { return _S[i]; }
    void S_push(Var _var) { _S.push(_var); };
    // void setSi(const Var &v, int i) { _S[i] = v; }
    int index(int _i, int _j)
    {
        return _i * (_J + 2) + _j;
    }

    void setLs(SatSolver &solver)
    {
        _Ls.growTo(_I * _J);
        for (int i = 0; i < _I; ++i)
            for (int j = 0; j < _J; ++j)
            {
                _Ls[i * _J + j].growTo(_L);
                for (int k = 0; k < _L; ++k)
                {
                    if (_Ls[i * _J + j][k] == -1)
                    {
                        cerr << "already == -1" << endl;
                        exit(0);
                    }
                    _Ls[i * _J + j][k] = solver.newVar();
                }
            }
    }
    vec<vec<Var>> &getLs() { return _Ls; }

private:
    unsigned _gid;     // for debugging purpose...
    Var _I;            // number of ROWs
    Var _J;            // number of Columns
    Var _L;            // max length of the ship
    vec<Var> _S;       // the number of ships that has to be placed in the grid for each sort
    vec<vec<Var>> _Ls; // for ineq's f in (6)
};

class Cell // index: 0 ~ (I + 2)(J + 2) - 1   , available : (1,1) ~ (I,J)  , i.e., 1 * (J + 2) + 1 ~ I * (J + 2) + J
{
public:
    Cell(unsigned i = 0) : _gid(i) { _initseg = -1; }
    ~Cell() {}

    Var getVar() const { return _var; }
    void setVar(const Var &v) { _var = v; }
    Var getinitseg() const { return _initseg; }
    void setinitseg(const Var &v) { _initseg = v; }

    Var geti() const { return _i; }
    void seti(const Var &v) { _i = v; }
    Var getj() const { return _j; }
    void setj(const Var &v) { _j = v; }

    vec<Var> &getXs() { return _Xs; }
    vec<Var> &getSs() { return _Ss; }
    void setCellVariable(SatSolver &solver, Board &board)
    {
        for (int i = 0; i < 7; ++i)
            _Xs.push(solver.newVar());
        for (int i = 0, n = board.getL(); i < n; ++i)
            _Ss.push(solver.newVar());
    }
    void printXs()
    {
        cout << "Xs of cell " << _var << " = ";
        for (int i = 0, n = _Xs.size(); i < n; ++i)
            cout << _Xs[i] << ' ';
        cout << endl;
    }
    void printSs()
    {
        cout << "Ss of cell " << _var << " = ";
        for (int i = 0, n = _Ss.size(); i < n; ++i)
            cout << _Ss[i] << ' ';
        cout << endl;
    }

private:
    unsigned _gid; // for debugging purpose...
    Var _var;
    Var _i;
    Var _j;
    Var _initseg;
    vec<Var> _Xs; // i*(J+2) + j
    vec<Var> _Ss; // i*(J+2) + j
};
#endif // BATTLESHIP_H