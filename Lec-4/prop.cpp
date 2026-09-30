#include "prop.h"

// atomic proposition functions
atom_prop::atom_prop(){
    name = "EMPTY";
    value = false;
}
atom_prop::atom_prop(string s){
    if(s == ""){
        name = "EMPTY";
        value = false;
    }
    else{
        name = s;
        value = true;
    }
}
atom_prop::atom_prop(string s, bool v){
    if(s == ""){
        name = "EMPTY";
        value = false;
    }
    else{
        name = s;
        value = v;
    }
}

// logical connectives for atomic propositions
prop atom_prop::operator~(){
    prop neg_p;
    neg_p.formula = "(~"+name+")";
    neg_p.well_formed = true;
    return neg_p;
}
prop atom_prop::operator+(atom_prop q){
    prop pORq;
    pORq.formula = "("+name+"+"+q.name+")";
    pORq.well_formed = true;
    return pORq;
}
prop atom_prop::operator*(atom_prop q){
    prop pANDq;
    pANDq.formula = "("+name+"*"+q.name+")";
    pANDq.well_formed = true;
    return pANDq;
}
prop atom_prop::operator>(atom_prop q){
    prop pIMPq;
    pIMPq.formula = "("+name+"->"+q.name+")";
    pIMPq.well_formed = true;
    return pIMPq;
}
prop atom_prop::operator^(atom_prop q){
    prop pXORq;
    pXORq.formula = "("+name+"^"+q.name+")";
    pXORq.well_formed = true;
    return pXORq;
}
prop atom_prop::operator-(atom_prop q){
    prop pIFFq;
    pIFFq.formula = "("+name+"<->"+q.name+")";
    pIFFq.well_formed = true;
    return pIFFq;
}

// functions for propositional formulae
prop::prop(){
    formula = "";
    well_formed = false;
}
prop::prop(atom_prop p){
    formula = p.name;
    well_formed = true;
}
prop::prop(string s){
    formula = s;
    well_formed = validate();
}
unordered_set<string> prop::getVariables(string& s){
    // reuse validate's recursion
    // Adds propositions in s to set "variables"
    int f_sz = s.size();
    unordered_set<string> variables;
    if(f_sz == 0){
        // "" not allowed
        return variables;
    }
    if(s[0] == '('){
        if(s[f_sz-1] == ')'){
            // logic part (connective)
            int brackets = 0;
            for(int i=1; i<f_sz-1; i++){
                char c = s[i];
                if(c == '('){
                    brackets++;
                }
                else if(c == ')'){
                    brackets--;
                }
                else if(brackets == 0){
                    if(c == '~'){
                        if(i == 1){
                            // check inner prop
                            string p = s.substr(2, f_sz-3);
                            if(validate(p)){
                                unordered_set<string> new_var = getVariables(p);
                                variables.insert(new_var.begin(),new_var.end());
                            }
                            return variables;
                        }
                        else{
                            return variables;
                        }
                    }
                    else if(c == '^' || c == '+' || c == '*'){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+1, f_sz-i-2);
                        if(validate(p) && validate(q)){
                            unordered_set<string> new_var = getVariables(p);
                            variables.insert(new_var.begin(),new_var.end());
                            new_var = getVariables(q);
                            variables.insert(new_var.begin(),new_var.end());
                        }
                        return variables;
                    }
                    else if(c == '-' && i < f_sz-2 && s[i+1] == '>'){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+2, f_sz-i-3);
                        if(validate(p) && validate(q)){
                            unordered_set<string> new_var = getVariables(p);
                            variables.insert(new_var.begin(),new_var.end());
                            new_var = getVariables(q);
                            variables.insert(new_var.begin(),new_var.end());
                        }
                        return variables;
                    }
                    else if(
                        c == '<' && i < f_sz-3 &&
                        s[i+1] == '-' && s[i+2] == '>'
                    ){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+3, f_sz-i-4);
                        if(validate(p) && validate(q)){
                            unordered_set<string> new_var = getVariables(p);
                            variables.insert(new_var.begin(),new_var.end());
                            new_var = getVariables(q);
                            variables.insert(new_var.begin(),new_var.end());
                        }
                        return variables;
                    }
                }
                else if(brackets < 0){
                    return variables;
                }
            }
            if(brackets != 0){
                return variables;
            }
        }
        else{
            return variables;
        }
    }
    else{
        // check no connectives
        for(int i=0; i<f_sz; i++){
            char c = s[i];
            if(
                c == ')' || c == '(' || c == '~' ||
                c == '+' || c == '*' || c == '^' ||
                (c == '-' && i < f_sz - 1 && s[i+1] == '>') ||
                (c == '<' && i < f_sz - 2 && s[i+1] == '-' && s[i+2] == '>')
            ){
                return variables;
            }
        }
        variables.insert(s);
        return variables;
    }
    return variables;
}
unordered_set<string> prop::getVariables(){
    // call helper function on formula
    return getVariables(formula);
}
bool prop::validate(string& s){
// Determines well_formed iff string belongs to Prop
    int f_sz = s.size();
    if(f_sz == 0){
        // "" not allowed
        return false;
    }
    if(s[0] == '('){
        if(s[f_sz-1] == ')'){
            // logic part (connective)
            int brackets = 0;
            for(int i=1; i<f_sz-1; i++){
                char c = s[i];
                if(c == '('){
                    brackets++;
                }
                else if(c == ')'){
                    brackets--;
                }
                else if(brackets == 0){
                    if(c == '~'){
                        if(i == 1){
                            // check inner prop
                            string p = s.substr(2, f_sz-3);
                            return validate(p);
                        }
                        else{
                            return false;
                        }
                    }
                    else if(c == '^' || c == '+' || c == '*'){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+1, f_sz-i-2);
                        return validate(p) && validate(q);
                    }
                    else if(c == '-' && i < f_sz-2 && s[i+1] == '>'){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+2, f_sz-i-3);
                        return validate(p) && validate(q);
                    }
                    else if(
                        c == '<' && i < f_sz-3 &&
                        s[i+1] == '-' && s[i+2] == '>'
                    ){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+3, f_sz-i-4);
                        return validate(p) && validate(q);
                    }
                }
                else if(brackets < 0){
                    return false;
                }
            }
            if(brackets != 0){
                return false;
            }
        }
        else{
            return false;
        }
    }
    else{
        // check no connectives
        for(int i=0; i<f_sz; i++){
            char c = s[i];
            if(
                c == ')' || c == '(' || c == '~' ||
                c == '+' || c == '*' || c == '^' ||
                (c == '-' && i < f_sz - 1 && s[i+1] == '>') ||
                (c == '<' && i < f_sz - 2 && s[i+1] == '-' && s[i+2] == '>')
            ){
                return false;
            }
        }
        return true;
    }
    return false;
}
bool prop::validate(){
    // return validate helper function called on formula
    return validate(formula);
}

// logical connectives for propositional formulae
prop prop::operator~(){
    prop neg_F;
    neg_F.formula = "(~"+formula+")";
    neg_F.well_formed = well_formed;
    return neg_F;
}
prop prop::operator+(atom_prop q){
    prop pORq;
    pORq.formula = "("+formula+"+"+q.name+")";
    pORq.well_formed = well_formed;
    return pORq;
}
prop prop::operator*(atom_prop q){
    prop pANDq;
    pANDq.formula = "("+formula+"*"+q.name+")";
    pANDq.well_formed = well_formed;
    return pANDq;
}
prop prop::operator>(atom_prop q){
    prop pIMPq;
    pIMPq.formula = "("+formula+"->"+q.name+")";
    pIMPq.well_formed = well_formed;
    return pIMPq;
}
prop prop::operator^(atom_prop q){
    prop pXORq;
    pXORq.formula = "("+formula+"^"+q.name+")";
    pXORq.well_formed = well_formed;
    return pXORq;
}
prop prop::operator-(atom_prop q){
    prop pIFFq;
    pIFFq.formula = "("+formula+"<->"+q.name+")";
    pIFFq.well_formed = well_formed;
    return pIFFq;
}
prop prop::operator+(prop q){
    prop pORq;
    pORq.formula = "("+formula+"+"+q.formula+")";
    pORq.well_formed = well_formed && q.well_formed;
    return pORq;
}
prop prop::operator*(prop q){
    prop pANDq;
    pANDq.formula = "("+formula+"*"+q.formula+")";
    pANDq.well_formed = well_formed && q.well_formed;
    return pANDq;
}
prop prop::operator>(prop q){
    prop pIMPq;
    pIMPq.formula = "("+formula+"->"+q.formula+")";
    pIMPq.well_formed = well_formed && q.well_formed;
    return pIMPq;
}
prop prop::operator^(prop q){
    prop pXORq;
    pXORq.formula = "("+formula+"^"+q.formula+")";
    pXORq.well_formed = well_formed && q.well_formed;
    return pXORq;
}
prop prop::operator-(prop q){
    prop pIFFq;
    pIFFq.formula = "("+formula+"<->"+q.formula+")";
    pIFFq.well_formed = true;
    return pIFFq;
}