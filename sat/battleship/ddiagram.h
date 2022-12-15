#ifndef DDIAGRAM_H
#define DDIAGRAM_H
#include <vector>
#include "Solver.h"
using namespace std;

class DDnode
{
public:
    Var _x;           // selector
    Var _l;           // left child Var
    Var _r;           // right child Var
    Var _pi;          // parent Var
    DDnode *left;     // pointer to left child;
    DDnode *right;    // pointer to left child;
    DDnode *parent_l; // pointer to left parent;
    DDnode *parent_r; // pointer to right parent;
    int value;

    DDnode() : left(0), right(0), parent_l(0), parent_r(0), value(-1), _x(-1), _l(-1), _r(-1), _pi(-1){};
    DDnode(int _value) : left(0), right(0), parent_l(0), parent_r(0), value(_value), _x(-1), _l(-1), _r(-1), _pi(-1){};
};

class DDiagram_eq
{
private:
    DDnode *root;

public:
    int *height_MAX;
    DDiagram_eq() : root(0){};
    DDnode *getroot() { return root; }
    void setroot(DDnode *_root) { root = _root; }
    void buildDiagram(vec<Var> &_V, int _target);
};
void DDiagram_eq::buildDiagram(vec<Var> &_V, int _target)
{
    int len = _V.size();
    vector<vector<DDnode>> pseudoDDiagram;
    for (int i = 0; i < _target; ++i)
    {
        for (int j = 0, n = len - _target + 1; j < n; ++j)
        {
            DDnode tmp;
            tmp._x = _V[i + j];
            pseudoDDiagram[i][j] = tmp;
        }
    }
    for (int i = 0, n = len - _target + 1; i < _target; ++i)
    {
        for (int j = 0, N = n - 1; j < N; ++j)
        {
            DDnode &tmp = pseudoDDiagram[i][j];
            tmp.right = &pseudoDDiagram[i][j + 1];
            pseudoDDiagram[i][j + 1].parent_r = &tmp;
        }
        DDnode &tmp = pseudoDDiagram[i][i + n - 1];
        tmp._r = 0;
    }
}
#endif // DDIAGRAM_H