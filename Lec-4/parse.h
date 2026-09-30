#pragma once
#include "common.h"
#include "prop.h"

class treeNode;
class parseTree;
class truthTable;

class treeNode{
    public:
    string s;
    treeNode* left;
    treeNode* right;
    treeNode(string S = "EMPTY", treeNode* Left = nullptr, treeNode* Right = nullptr);
};

class parseTree{
    treeNode* root;
    treeNode* makeTree(string& s);
    int valuateNode(unordered_map<string, bool>& assignment, treeNode* start);
    public:
    parseTree(treeNode* head = nullptr);
    parseTree(string s);
    parseTree(prop F);
    ~parseTree();
    int valuate(unordered_map<string, bool>& assignment);
    int valuate(vector<atom_prop>& assignment);
};

class truthTable {
    public:
    string formula;
    vector<string> variables;
    vector<bool> semantics;
    bool satisfiable;
    bool valid;
    truthTable(prop F);
    void print();
};