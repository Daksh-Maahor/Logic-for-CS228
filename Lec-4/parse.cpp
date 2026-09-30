#include "parse.h"

treeNode::treeNode(string S, treeNode* Left, treeNode* Right){
    if(S == ""){
        s = "EMPTY";
    }
    else{
        s = S;
    }
    left = Left;
    right = Right;
}

parseTree::parseTree(treeNode* head){
    root = head;
}

treeNode* parseTree::makeTree(string& s){
    // return a pointer to newly made root
    // to the tree of string s
    treeNode* newRoot = nullptr;
    // code similar to prop::validate()
    int f_sz = s.size();
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
                            // inner prop is left
                            string p = s.substr(2, f_sz-3);
                            newRoot = new treeNode("~", makeTree(p));
                            return newRoot;
                        }
                        else{
                            return newRoot;
                        }
                    }
                    else if(c == '^' || c == '+' || c == '*'){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+1, f_sz-i-2);
                        newRoot = new treeNode(string(1, c), makeTree(p), makeTree(q));
                        return newRoot;
                    }
                    else if(c == '-' && i < f_sz-2 && s[i+1] == '>'){
                        // check inner props
                        string p(s.substr(1, i-1));
                        string q(s.substr(i+2, f_sz-i-3));
                        newRoot = new treeNode("->", makeTree(p), makeTree(q));
                        return newRoot;
                    }
                    else if(
                        c == '<' && i < f_sz-3 &&
                        s[i+1] == '-' && s[i+2] == '>'
                    ){
                        // check inner props
                        string p = s.substr(1, i-1);
                        string q = s.substr(i+3, f_sz-i-4);
                        newRoot = new treeNode("<->", makeTree(p), makeTree(q));
                        return newRoot;
                    }
                }
                else if(brackets < 0){
                    return newRoot;
                }
            }
            if(brackets != 0){
                return newRoot;
            }
        }
        else{
            return newRoot;
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
                return newRoot;
            }
        }
        newRoot = new treeNode(s);
        return newRoot;
    }
    return nullptr;
}

parseTree::parseTree(string s){
    // set root to new parsetree from string s if well formed
    // else nullptr
    root = makeTree(s);
}

parseTree::parseTree(prop F){
    // set root to new parsetree from formula of F
    root = makeTree(F.formula);
}

parseTree::~parseTree(){
    if(!root){
        return;
    }
    if(root->left){
        delete root->left;
    }
    if(root->right){
        delete root->right;
    }
    delete root;
}

int parseTree::valuateNode(unordered_map<string, bool>& assignment, treeNode* start){
    // map name to value then solve recursively
    // return -1 if assignment not valid
    if(!start){
        // should not be possible
        return -1;
    }
    if(!start->left && !start->right){
        // node must be a prop itself
        if(assignment.find(start->s) != assignment.end()){
            return assignment[start->s];
        }
        return -1;
    }
    if(!start->left){
        // should not be possible
        return -1;
    }
    if(!start->right){
        // Only case is Not operator
        if(start->s == "~"){
            int left_val = valuateNode(assignment, start->left);
            return (left_val == -1) ? -1 : 1 - left_val;
        }
        return -1;
    }
    // binary connectives possible, else not possible (-1)
    int left_val = valuateNode(assignment, start->left), right_val = valuateNode(assignment, start->right);
    if(left_val == -1 || right_val == -1){
        return -1;
    }
    bool left_bool = left_val, right_bool = right_val;
    if(start->s == "+"){
        return left_bool || right_bool;
    }
    else if(start->s == "*"){
        return left_bool && right_bool;
    }
    else if(start->s == "^"){
        return left_bool ^ right_bool;
    }
    else if(start->s == "->"){
        return (!left_bool)||right_bool;
    }
    else if(start->s == "<->"){
        return left_bool == right_bool;
    }
    return -1;
}

int parseTree::valuate(unordered_map<string, bool>& assignment){
    // using recursion on nodes starting from root
    return valuateNode(assignment, root);
}

int parseTree::valuate(vector<atom_prop>& assignment){
    // convert assignment to unordered_map of name to value
    // then solve using upper definition
    unordered_map<string, bool> map;
    int n = assignment.size();
    for(int i=0; i<n; i++){
        map[assignment[i].name] = assignment[i].value;
    }
    return valuate(map);
}

truthTable::truthTable(prop F){
    // use parseTree valuate for every assignment
    unordered_set<string> vars = F.getVariables();
    parseTree F_T(F);
    int n = vars.size();
    int N = 1;
    for(int i=0; i<n; i++){
        N *= 2;
    }
    formula = F.formula;
    semantics = vector<bool>(N);
    variables = vector<string>(n);
    satisfiable = false;
    valid = true;
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
        semantics[i] = valuation;
        if(!satisfiable && valuation == 1){
            satisfiable = true;
        }
        if(valid && valuation == 0){
            valid = false;
        }
    }
}

void truthTable::print(){
    int n = semantics.size(), m = variables.size();
    cout<<"| ";
    for(auto i=variables.begin(); i!=variables.end(); i++){
        cout<<*i<<" | ";
    }
    cout<<formula<<" |\n";
    for(int i=0; i<n; i++){
        int k = i;
        cout<<"| ";
        for(int j=0; j<m; j++){
            cout<< k%2 << " | ";
            k = k/2;
        }
        cout<<semantics[i]<<" |\n";
    }
}