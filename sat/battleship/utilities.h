#ifndef UTILITIES_H
#define UTILITIES_H
#include <string>
#include <iostream>
#include <bits/stdc++.h>
#include <vector>
#include "sat.h"
#include "battleship.h"

using namespace std;

void split(string _s, vec<Var> &_vi, char _splitchar)
{
    stringstream ss(_s);

    while (ss.good())
    {
        string substr;
        getline(ss, substr, ',');
        _vi.push(stoi(substr));
    }
}

void print(string _name, vec<Var> &_v)
{
    cout << _name << " = ";
    for (int i = 0, n = _v.size(); i < n; ++i)
        cout << _v[i] << ' ';
    cout << endl;
}

template <class T>
void printvector(string _name, vector<T> &_v)
{
    cout << _name << " = ";
    for (int i = 0, n = _v.size(); i < n; ++i)
        cout << _v[i]->getinitseg() << ' ';
    cout << endl;
}

void print_result(int _i)
{
    switch (_i)
    {
    case 0:
        cout << "~ ";
        break;
    case 1:
        cout << "\u25C0 "; // ◀
        break;
    case 2:
        cout << "\u25B6 "; // ▶
        break;
    case 3:
        cout << "\u25B2 "; // ▲
        break;
    case 4:
        cout << "\u25BC "; // ▼
        break;
    case 5:
        cout << "▄ ";
        break;
    case 6:
        cout << "● ";
        break;
    default:
        cout << "err ";
        break;
    }
}
void push_segments(vec<Var> &V, vec<Var> &_Xs)
{
    for (int i = 1; i < 7; ++i)
    {
        V.push(_Xs[i]);
    }
}

void push_segLength(vec<vec<Var>> &V, vec<Var> &_Ss)
{
    for (int i = 0, n = V.size(); i < n; ++i)
    {
        V[i].push(_Ss[i]);
    }
}
void addClause_len_6(SatSolver &solver, Board &board, vector<Cell *> &cells, int _L, int _i, int _I, int _J)
{
    vec<Var> _V;
    // cout << "J = " << _J << endl;
    // cout << "_i = " << _i << endl;
    for (int k = 1; k < _L; ++k)
    {
        int _l = k + 1;
        // cout << "len = " << _l << endl;
        _V.push(cells[_i]->getXs()[1]);
        _V.push(cells[_i + _l - 1]->getXs()[2]);
        for (int j = _i + 1, n = _i + _l - 1; j < n; ++j)
            _V.push(cells[j]->getXs()[5]);
        if ((_i + (_l - 1) * (_J + 2)) > ((_I + 2) * (_J + 2) - 1))
            continue;
        _V.push(cells[_i]->getXs()[3]);
        _V.push(cells[_i + (_l - 1) * (_J + 2)]->getXs()[4]);
        for (int j = _i + (_J + 2), n = _i + (_l - 1) * (_J + 2); j < n; j += _J + 2)
            _V.push(cells[j]->getXs()[5]);
        solver.addClause_PB_ineq(_V, _l, board.getLs()[(_i / (_J + 2) - 1) * _J + _i % (_J + 2) - 1][k]);
    }
}
#endif // UTILITIES_H
