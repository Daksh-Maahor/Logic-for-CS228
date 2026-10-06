#include "ND.h"

vector<vector<string>> elimination(vector<prop>& premises, prop conclusion, bool& valid){
    // expand set of premises by elimination rules to help conclusion and return proof or not valid
    // Idea: make unordered map of premises, then for each premise check what elimination helps
    int n = premises.size();
    unordered_map<string, int> premise_map;
    vector<vector<string>> proof;
    for(int i=0; i<n; i++){
        premise_map[premises[i].formula] = i+1;
        proof.push_back({premises[i].formula, "Premise"});
    }
    // added to check if elimination increased premises or not
    bool added = false;
    for(int j=0; j<n; j++){
        // check premise[j]'s formula for elimination
        string P_i = premises[j].formula;
        // check if it is atomic or not
        if(P_i[0] == '('){
            int brackets = 0, f_sz = P_i.size();
            for(int i=1; i<f_sz-1; i++){
                char c = P_i[i];
                if(c == '('){
                    brackets++;
                }
                else if(c == ')'){
                    brackets--;
                }
                else if(brackets == 0){
                    if(c == '~'){
                        if(i == 1){
                            // (~phi), ~elimination (derived, need ~~elim instead)
                            if(P_i[3] == '~'){
                                //(~(~phi))
                                string phi = P_i.substr(4, P_i.size() - 6);
                                if(premise_map.find(phi) == premise_map.end()){
                                    proof.push_back({phi, "~~e " + to_string(j+1)});
                                    premises.push_back(prop(phi));
                                    added = true;
                                }
                            }
                        }
                        else{
                            // cannot happen (since formula was valid)
                        }
                    }
                    else if(c == '^'){
                        // (phi ^ psi)
                        // ^elim does not exist idk
                    }
                    else if(c == '+'){
                        // (phi + psi)
                        // +elim {F+G, F->H, G->H, H}, let H be conclusion
                        string phi = P_i.substr(1,i-1);
                        string psi = P_i.substr(i+1, f_sz-i-2);

                        // skip if phi or psi are already premises (obvious)
                        if((premise_map.find(phi) != premise_map.end())||(premise_map.find(psi) != premise_map.end())){
                            continue;
                        }
                        // try to prove conclusion from phi
                        vector<prop> new_premises1 = premises;
                        new_premises1.push_back(phi);
                        vector<vector<string>> subProof1 = ND(new_premises1, conclusion, valid);
                        if(!valid){
                            continue;
                        }
                        
                        // try to prove conclusion from psi
                        vector<prop> new_premises2 = premises;
                        new_premises2.push_back(psi);
                        vector<vector<string>> subProof2 = ND(new_premises2, conclusion, valid);
                        if(!valid){
                            continue;
                        }

                        // It worked
                        added = true;
                        proof.push_back({phi, "Assumption1"});
                        int x1 = proof.size();
                        proof.insert(proof.end(), subProof1.begin() + proof.size(), subProof1.end());
                        proof.push_back({psi, "Assumption2"});
                        int x2 = proof.size();
                        proof.insert(proof.end(), subProof2.begin() + x1, subProof2.end());
                        proof.push_back({conclusion.formula, "+e " + to_string(j+1) + ", " + to_string(x1) + "-" + to_string(x2-1) + ", " + to_string(x2) + "-" + to_string(proof.size())});
                        
                        premises.push_back(conclusion);
                        return proof;
                    }
                    else if(c == '*'){
                        // (phi * psi)
                        // * elim
                        string phi = P_i.substr(1,i-1);
                        string psi = P_i.substr(i+1, f_sz-i-2);
                        if(premise_map.find(phi) == premise_map.end()){
                            proof.push_back({phi, "*e1 " + to_string(j+1)});
                            premises.push_back(prop(phi));
                            added = true;
                        }
                        if(premise_map.find(psi) == premise_map.end()){
                            proof.push_back({psi, "*e2 " + to_string(j+1)});
                            premises.push_back(prop(psi));
                            added = true;
                        }
                    }
                    else if(c == '-' && i < f_sz-2 && P_i[i+1] == '>'){
                        // (phi -> psi)
                        // -> elim
                        string phi = P_i.substr(1, i-1);
                        string psi = P_i.substr(i+2, f_sz-i-3);
                        // M.P. : check if phi is in premises then say psi
                        if(premise_map.find(phi) != premise_map.end()){
                            proof.push_back({psi, "MP " + to_string(premise_map[phi]) + ", " + to_string(j+1)});
                            premises.push_back(prop(psi));
                            added = true;
                        }
                        // M.T. : check if (~psi) is in premises then say (~phi)
                        if(premise_map.find("(~" + psi + ")") != premise_map.end()){
                            proof.push_back({"(~" + phi + ")", "MT " + to_string(premise_map["(~" + psi + ")"]) + ", " + to_string(j+1)});
                            premises.push_back(prop("(~" + phi + ")"));
                            added = true;
                        }
                    }
                    else if(
                        c == '<' && i < f_sz-3 &&
                        P_i[i+1] == '-' && P_i[i+2] == '>'
                    ){
                        // (phi <-> psi) idk what to do
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
            // if bot, then bot elim to get conclusion and return early (since done)
            if(P_i == "BOT"){
                valid = true;
                proof.push_back({conclusion.formula, "BOTe " + to_string(j+1)});
                premises.push_back(prop(conclusion.formula));
                return proof;
            }
            // else, normal atomic prop, no elimination possible.
        }
    }
    // No elimination implies not possible
    if(!added){
        valid = false;
        return {};
    }
    valid = true;
    return proof;
}

vector<vector<string>> ND(vector<prop> premises, prop conclusion, bool& valid){
    // 1. check if conclusion is in premises (true then done, else continue)
    // 2. check if conclusion is a literal or not (true then done, else continue)
    // 3. check if conclusion can be derived from premises with introduction
    // 4. check if elimination on one of the premises leads further
    valid = false;
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
        valid = true;
        proof.push_back({premises[check1_i].formula, "Copy " + to_string(check1_i+1)});
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
                            proof.push_back({phi, "Assumption"});
                            proof.insert(proof.end(), sub_proof.begin() + n + 1, sub_proof.end());
                            proof.push_back({conclusion.formula, "~i " + to_string(n+1) + "-" + to_string(proof.size())});
                            return proof;
                        }
                        // use elimination
                        proof = elimination(premises, conclusion, valid);
                        if(!valid){
                            return {};
                        }
                        // More derived premises and extended proof
                        if(proof[proof.size()-1][0] == conclusion.formula){
                            // done, early exit
                            return proof;
                        }
                        vector<vector<string>> final_proof = ND(premises, conclusion, valid);
                        proof.insert(proof.end(), final_proof.begin() + proof.size(), final_proof.end());
                        return proof;
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
                    // + intro from premises (one of premises is either phi or psi or they are derivable by ND)
                    string phi = conclusion.formula.substr(1,i-1);
                    string psi = conclusion.formula.substr(i+1, f_sz-i-2);
                    
                    // early exist if premise
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

                    vector<vector<string>> sub_proof1 = ND(premises, phi, valid);
                    if(valid){
                        proof.insert(proof.end(), sub_proof1.begin() + n, sub_proof1.end());
                        proof.push_back({conclusion.formula, "+i1 " + to_string(proof.size())});
                        return proof;
                    }

                    vector<vector<string>> sub_proof2 = ND(premises, psi, valid);
                    if(valid){
                        proof.insert(proof.end(), sub_proof2.begin() + n, sub_proof2.end());
                        proof.push_back({conclusion.formula, "+i2 " + to_string(proof.size())});
                        return proof;
                    }

                    // else using elimination, else not possible
                    proof = elimination(premises, conclusion, valid);
                    if(!valid){
                        return {};
                    }
                    if(proof[proof.size()-1][0] == conclusion.formula){
                        // done, early exit
                        return proof;
                    }
                    vector<vector<string>> final_proof = ND(premises, conclusion, valid);
                    proof.insert(proof.end(), final_proof.begin() + proof.size(), final_proof.end());
                    return proof;
                }
                else if(c == '*'){
                    // (phi * psi)
                    // * intro from premises (both phi and psi in premises)
                    string phi = conclusion.formula.substr(1,i-1);
                    string psi = conclusion.formula.substr(i+1, f_sz-i-2);
                    
                    // early finding phi and psi in premises
                    int foundPhi = -1, foundPsi = -1;
                    for(int i=0; i<n; i++){
                        if(premises[i].formula == phi){
                            foundPhi = i+1;
                        }
                        if(premises[i].formula == psi){
                            foundPsi = i+1;
                        }
                        if(foundPhi != -1 && foundPsi != -1){
                            valid = true;
                            proof.push_back({conclusion.formula, "*i " + to_string(foundPhi) + ", " + to_string(foundPsi)});
                            return proof;
                        }
                    }

                    if(foundPhi != -1 && foundPsi == -1){
                        vector<vector<string>> sub_proof = ND(premises, psi, valid);
                        if(valid){
                            proof.insert(proof.end(), sub_proof.begin() + n, sub_proof.end());
                            proof.push_back({conclusion.formula, "*i " + to_string(foundPhi) + ", " + to_string(proof.size())});
                            return proof;
                        }
                    }
                    else if(foundPhi == -1 && foundPsi != -1){
                        vector<vector<string>> sub_proof = ND(premises, phi, valid);
                        if(valid){
                            proof.insert(proof.end(), sub_proof.begin() + n, sub_proof.end());
                            proof.push_back({conclusion.formula, "*i " + to_string(proof.size()) + ", " +  to_string(foundPsi)});
                            return proof;
                        }
                    }
                    else{
                        vector<vector<string>> sub_proof1 = ND(premises, phi, valid);
                        if(valid){
                            vector<vector<string>> sub_proof2 = ND(premises, psi, valid);
                            if(valid){
                                proof.insert(proof.end(), sub_proof2.begin() + n, sub_proof2.end());
                                proof.insert(proof.end(), sub_proof1.begin() + n, sub_proof1.end());
                                proof.push_back({conclusion.formula, "*i " + to_string(proof.size() - sub_proof2.size()) + ", " + to_string(proof.size())});
                                return proof;
                            }
                        }
                    }
                    
                    // else using elimination, else not possible
                    proof = elimination(premises, conclusion, valid);
                    if(!valid){
                        return {};
                    }
                    if(proof[proof.size()-1][0] == conclusion.formula){
                        // done, early exit
                        return proof;
                    }
                    vector<vector<string>> final_proof = ND(premises, conclusion, valid);
                    proof.insert(proof.end(), final_proof.begin() + proof.size(), final_proof.end());
                    return proof;
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
                        proof.push_back({phi, "Assumption"});
                        proof.insert(proof.end(), sub_proof.begin() + n + 1, sub_proof.end());
                        proof.push_back({conclusion.formula, "->i " + to_string(n+1) + ", " + to_string(proof.size())});
                        return proof;
                    }
                    // else use elimination, else not possible
                    proof = elimination(premises, conclusion, valid);
                    if(!valid){
                        return {};
                    }
                    if(proof[proof.size()-1][0] == conclusion.formula){
                        // done, early exit
                        return proof;
                    }
                    vector<vector<string>> final_proof = ND(premises, conclusion, valid);
                    proof.insert(proof.end(), final_proof.begin() + proof.size(), final_proof.end());
                    return proof;
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
        // if bot, then bot intro
        if(conclusion.formula == "BOT"){
            // search for F and (~F) in premises
            unordered_map<string, int> premise_map;
            for(int i=0; i<n; i++){
                string not_F = "(~" + premises[i].formula + ")";
                if(premise_map.find(not_F) != premise_map.end()){
                    // found F and (~F), done
                    valid = true;
                    proof.push_back({"BOT", "BOTi " + to_string(i+1) + ", " + to_string(premise_map[not_F])});
                    return proof;
                }
                if(premises[i].formula.substr(0, 2) == "(~"){
                    string F = premises[i].formula.substr(2, premises[i].formula.size()-3);
                    if(premise_map.find(F) != premise_map.end()){
                        // found (~F) and F, done
                        valid = true;
                        proof.push_back({"BOT", "BOTi " + to_string(premise_map[F]) + ", " + to_string(i+1)});
                        return proof;
                    }
                }
                premise_map[premises[i].formula] = i+1;
            }
            // try elimination to get bot, else not possible
            proof = elimination(premises, conclusion, valid);
            if(!valid){
                return {};
            }
            if(proof[proof.size()-1][0] == conclusion.formula){
                // done, early exit
                return proof;
            }
            vector<vector<string>> final_proof = ND(premises, conclusion, valid);
            proof.insert(proof.end(), final_proof.begin() + proof.size(), final_proof.end());
            return proof;
        }
        // try elimination on premises to get conclusion, else not possible
        proof = elimination(premises, conclusion, valid);
        if(!valid){
            return {};
        }
        if(proof[proof.size()-1][0] == conclusion.formula){
            // done, early exit
            return proof;
        }
        vector<vector<string>> final_proof = ND(premises, conclusion, valid);
        if(valid){
            proof.insert(proof.end(), final_proof.begin() + proof.size(), final_proof.end());
            return proof;   
        }
    }
    // try deriving bot, else cooked
    proof = ND(premises, prop("BOT"), valid);
    if(valid){
        proof.push_back({conclusion.formula, "BOTe " + to_string(proof.size())});
        return proof;
    }
    valid = false;
    return {};
}