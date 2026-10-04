#include "ND.h"

vector<vector<string>> ND(vector<prop> premises, prop conclusion, bool& valid){
    // 1. check if conclusion is in premises (true then done, else continue)
    // 2. check if conclusion is a literal or not (true then done, else continue)
    // 3. check if conclusion can be derived from premises with introduction
    // 4. check if elimination on one of the premises leads further
    vector<vector<string>> proof;
    unordered_set<string> variables;
    int n = premises.size();
    bool check1 = false;
    int check1_i = -1;
    for(int i=0; i<n; i++){
        if(premises[i].formula == conclusion.formula){
            check1 = true;
            check1_i = i;
        }
        unordered_set<string> temp = premises[i].getVariables();
        variables.insert(temp.begin(), temp.end());
        proof.push_back({premises[i].formula, "Premise"});
    }

    if(check1){
        // conclusion is in premises, hence done by step 1
        proof.push_back({premises[check1_i].formula, "Copy " + check1_i+1});
        return proof;
    }

    // check if it is atomic or not
    if(conclusion.formula[0] == '('){
        int brackets = 0, f_sz = conclusion.formula.size();
        for(int i=1; i<f_sz-1; i++){
            char c = conclusion.formula[i];
            if(c == '('){
                brackets++;
            }
            else if(c == ')'){
                brackets--;
            }
            else if(brackets == 0){
                if(c == '~'){
                    if(i == 1){
                        // (~phi)
                        // Try not intro with phi, else use elimination on premises
                        string phi = conclusion.formula.substr(2, f_sz-3);
                        vector<prop> new_premises = premises;
                        new_premises.push_back(prop(phi));
                        vector<vector<string>> sub_proof = ND(new_premises, prop("BOT"), valid);
                        if(valid){
                            // add sub proof to proof then return it
                            // not valid for now
                            valid = false;
                            return {};
                        }
                        // use elimination
                        // not valid for now
                        valid = false;
                        return {};
                    }
                    else{
                        // cannot happen (since formula was valid)
                    }
                }
                else if(c == '^'){
                    // (phi ^ psi)
                    // ^ intro does not exist so idk
                    // not valid for now
                    valid = false;
                    return {};
                }
                else if(c == '+'){
                    // (phi + psi)
                    // + intro from premises (one of premises is either phi or psi)
                    string phi = conclusion.formula.substr(1,i-1);
                    string psi = conclusion.formula.substr(i+1, f_sz-i-2);
                    for(int i=0; i<n; i++){
                        if(premises[i].formula == phi){
                            valid = true;
                            proof.push_back({conclusion.formula, "+i1 " + to_string(i+1)});
                            return proof;
                        }
                        if(premises[i].formula == psi){
                            valid = true;
                            proof.push_back({conclusion.formula, "+i2 " + to_string(i+1)});
                            return proof;
                        }
                    }
                    // else using elimination, else not possible (to do)
                    // not valid for now
                    valid = false;
                    return {};
                }
                else if(c == '*'){
                    // (phi * psi)
                    // * intro from premises (both phi and psi in premises)
                    string phi = conclusion.formula.substr(1,i-1);
                    string psi = conclusion.formula.substr(i+1, f_sz-i-2);
                    int phii = -1, psii = -1;
                    for(int i=0; i<n; i++){
                        if(premises[i].formula == phi){
                            phii = i+1;
                        }
                        if(premises[i].formula == psi){
                            psii = i+1;
                        }
                        if(phii != -1 && psii != -1){
                            valid = true;
                            proof.push_back({conclusion.formula, "*i " + to_string(phii) + ", " + to_string(psii)});
                            return proof;
                        }
                    }
                    // else using elimination, else not possible
                    // not valid for now
                    valid = false;
                    return {};
                }
                else if(c == '-' && i < f_sz-2 && conclusion.formula[i+1] == '>'){
                    // (phi -> psi)
                    // -> intro from premises (assuming phi, derive psi)
                    string phi = conclusion.formula.substr(1, i-1);
                    string psi = conclusion.formula.substr(i+2, f_sz-i-3);
                    vector<prop> new_premises = premises;
                    new_premises.push_back(prop(phi));
                    vector<vector<string>> sub_proof = ND(new_premises, psi, valid);
                    if(valid){
                        // append sub_proof to proof then return;
                        // not valid for now
                        valid = false;
                        return {};
                    }
                    // else use elimination, else not possible
                    // not valid for now
                    valid = false;
                    return {};
                }
                else if(
                    c == '<' && i < f_sz-3 &&
                    conclusion.formula[i+1] == '-' && conclusion.formula[i+2] == '>'
                ){
                    // (phi <-> psi) idk what to do
                    // prove phi -> psi then psi -> phi then say phi <-> psi
                    // else use elimination, else not possible
                    // not valid for now
                    valid = false;
                    return {};
                }
            }
            else if(brackets < 0){
                // not well formed
            }
        }
        if(brackets != 0){
            // not well formed
        }
    }
    else{
        // try elimination on premises to get conclusion, else not possible
    }
    valid = false;
    return {};
}