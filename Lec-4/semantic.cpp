#include "prop.h"
#include "parse.h"

bool prop::entails(prop G){
    bool entails = true;
    parseTree F_T(*this);
    parseTree G_T(G);
    unordered_set<string> vars = this->getVariables();
    unordered_set<string> G_vars = G.getVariables();
    vars.insert(G_vars.begin(), G_vars.end());
    int n = vars.size();
    int N = 1;
    for(int i=0; i<n; i++){
        N *= 2;
    }
    formula = this->formula;
    vector<string> variables(n);
    vector<atom_prop> assignment(n);
    int k = 0;
    for(auto i=vars.begin(); i!= vars.end(); i++){
        assignment[k] = atom_prop(*i, 0);
        variables[k] = *i;
        k++;
    }
    for(int i=0; i<N; i++){
        int k = i;
        for(int j=0; j<n; j++){
            assignment[j].value = k%2;
            k = k/2;
        }
        int valuation = F_T.valuate(assignment);
        if(valuation == 0){
            // F evaluates to 0
            continue;
        }
        else if(valuation == 1){
            // F evaluate to 1, check G
            int G_valuation = G_T.valuate(assignment);
            if(G_valuation != 1){
                // G evaluates to 0 when F evaluates to 1
                // F does not entail G
                return false;
            }
            // Else, loop continues
        }
        else{
            // should not be possible that F is unassigned
            return false;
        }
    }
    return true;
}

bool prop::semanticEquivalent(prop G){
    bool entails = true;
    parseTree F_T(*this);
    parseTree G_T(G);
    unordered_set<string> vars = this->getVariables();
    unordered_set<string> G_vars = G.getVariables();
    vars.insert(G_vars.begin(), G_vars.end());
    int n = vars.size();
    int N = 1;
    for(int i=0; i<n; i++){
        N *= 2;
    }
    formula = this->formula;
    vector<string> variables(n);
    vector<atom_prop> assignment(n);
    int k = 0;
    for(auto i=vars.begin(); i!= vars.end(); i++){
        assignment[k] = atom_prop(*i, 0);
        variables[k] = *i;
        k++;
    }
    for(int i=0; i<N; i++){
        int k = i;
        for(int j=0; j<n; j++){
            assignment[j].value = k%2;
            k = k/2;
        }
        int valuation = F_T.valuate(assignment), G_valuation = G_T.valuate(assignment);
        if(valuation != G_valuation){
            return false;
        }
    }
    return true;
}