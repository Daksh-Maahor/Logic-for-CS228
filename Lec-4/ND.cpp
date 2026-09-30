#include "ND.h"

vector<vector<string>> naive(vector<prop> premises, prop conclusion, bool& valid){
    vector<vector<string>> proof;
    unordered_set<string> variables;
    int n = premises.size();
    for(int i=0; i<n; i++){
        unordered_set<string> temp = premises[i].getVariables();
        variables.insert(temp.begin(), temp.end());
        proof.push_back({premises[i].formula, "Premise"});
    }
    if(conclusion.formula[0] == '('){
        valid = false;
        return {};
    }
    else{
        int n = variables.size(), k=1;
        for(auto i=variables.begin(); i != variables.end(); i++){
            if(*i == conclusion.formula){
                valid = true;
                proof.push_back({conclusion.formula, "Copy "+to_string(k)});
                return proof;
            }
        }
        valid = false;
        return {};
    }
    valid = true;
    return proof;
}