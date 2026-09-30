#pragma once
#include "common.h"

class atom_prop;
class prop;

class atom_prop{
    // Atomic propositions that will make up all logic
    public:
    string name;
    bool value;
    atom_prop();
    atom_prop(string s);
    atom_prop(string s, bool v);
    // logical connectives
    prop operator~();
    prop operator+(atom_prop q);
    prop operator*(atom_prop q);
    prop operator>(atom_prop q);
    prop operator^(atom_prop q);
    prop operator-(atom_prop q);
};

class prop{
    // A propositional formula
    unordered_set<string> getVariables(string& s);
    bool validate(string& s);
    public:
    string formula;
    bool well_formed;
    prop();
    prop(atom_prop p);
    prop(string s);
    bool validate();
    unordered_set<string> getVariables();
    // logical connectives
    prop operator~();
    prop operator+(atom_prop q);
    prop operator*(atom_prop q);
    prop operator>(atom_prop q);
    prop operator^(atom_prop q);
    prop operator-(atom_prop q);
    prop operator+(prop q);
    prop operator*(prop q);
    prop operator>(prop q);
    prop operator^(prop q);
    prop operator-(prop q);
    bool entails(prop q);
    bool semanticEquivalent(prop q);
};