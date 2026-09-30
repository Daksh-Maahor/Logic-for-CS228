#include "common.h"
#include "prop.h"
#include "parse.h"

int main(){
    int t;
    cout<<"Enter number of pairs of formulae:\n";
    cin>>t;
    for(int i=0; i<t; i++){
        string f, g;
        cout<<"Enter a formula:\n";
        cin>>f;
        prop F(f);
        if(!F.well_formed){
            cout<<"Formula not well-formed!\n";
            continue;
        }
        cout<<"Enter another formula:\n";
        cin>>g;
        prop G(g);
        if(!G.well_formed){
            cout<<"Formula not well-formed!\n";
            continue;
        }
        cout<<"Truth table of first formula F:\n";
        truthTable F_T(F);
        F_T.print();
        cout<<"Truth table of second formula G:\n";
        truthTable G_T(G);
        G_T.print();
        cout<<"F|=G: ";
        (F.entails(G)) ? cout<<"YES\n" : cout<<"NO\n";
        cout<<"G|=F: ";
        (G.entails(F)) ? cout<<"YES\n" : cout<<"NO\n";
        cout<<"F==G: ";
        (F.semanticEquivalent(G)) ? cout<<"YES\n" : cout<<"NO\n";
    }
    return 0;
}