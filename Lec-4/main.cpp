#include "common.h"
#include "prop.h"
#include "parse.h"
#include "ND.h"

int main(){
    int t;
    cout<<"Enter number of premises: \n";
    cin>>t;
    vector<prop> premises;
    for(int i=0; i<t; i++){
        cout<<"Enter a premise: \n";
        string s;
        cin>>s;
        prop F(s);
        if(!F.well_formed){
            cout<<"Formula not well-formed! Try again. \n";
            i--;
            continue;
        }
        premises.push_back(F);
    }
    cout<<"Enter a conclusion: \n";
    string s;
    cin>>s;
    prop G(s);
    if(!G.well_formed){
        cout<<"Formula not well-formed!\n";
    }
    else{
        bool valid;
        vector<vector<string>> proof = naive(premises, G, valid);
        if(valid){
            cout<<"Sequent is valid. Proof: \n";
            int n = proof.size();
            for(int i=0; i<n; i++){
                cout<<i+1<<". "<<proof[i][0]<<"   "<<proof[i][1]<<'\n';
            }
        }
        else{
            cout<<"Sequent not valid.";
        }
    }
    return 0;
}