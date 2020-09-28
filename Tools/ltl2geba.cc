// Author: Yong Li (liyong@ios.ac.cn)

#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <fstream>

#include <spot/tl/formula.hh>
#include <spot/tl/print.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/ltlf.hh>
#include <spot/tl/relabel.hh>
#include <spot/tl/simplify.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/remprop.hh>


/*
Translate a LTL formula to a universal co-Buchi automaton
If the input is \phi then construct a universal co-Buchi automaton for \exists O'. \phi(O'/O) -> \phi 
We thus need to obtain the Buchi automaton for the formula \exists O' \phi(O'/O) \land ! \phi
*/
using namespace spot;
using namespace std;

void
ltlf2geba(const char *ltlf, const char* outs)
{
    //spot::bdd_dict_ptr dict = spot::make_bdd_dict();
    auto pf1 = spot::parse_infix_psl(ltlf);
    if (pf1.format_errors(std::cerr))
    {
        std::cerr << "error: " << ltlf << std::endl;
        exit(-1);
    }
    //cout << "parsed formula: " << endl;
    spot::formula f = pf1.f;
    //std::cout << "Input formula is " << spot::str_psl(f, true) << std::endl;
    spot::tl_simplifier simpl;
    f = simpl.simplify(f);
    //std::cout << "Simplified formula is " << spot::str_psl(f, true) << std::endl;

    relabeling_map m;
    vector<string> out_aps;
    string ins = outs;
    std::stringstream ss(ins);
    std::string token;
    while (getline(ss, token, ',')) 
    {
        if(! token.empty())
        {
            out_aps.push_back(token);
            //cout << "output ap: " << token << endl;
            string p = token + "_";
            m[formula::ap(token)] = formula::ap(p);
        }
    }
    
    // create formula \phi(O'/O)
    formula fprime = relabel_apply(f, &m);
    //cout << "Duplicated formula is " << fprime << endl;

    // create formula \phi(O'/O) \land ! \phi
    formula r = formula::And({fprime, formula::Not(f)});

    //cout << "Resulted formula is " << r << endl;
    
    // translation
    spot::translator trans;
    trans.set_type(spot::postprocessor::BA);
    trans.set_pref(spot::postprocessor::Small);
    spot::twa_graph_ptr nba = trans.run(r);

    // quantify out all O' variables
    spot::remove_ap rem;
    for(string out_ap : out_aps)
    {
        string p = out_ap + "_";
        rem.add_ap(p.c_str());
    }
    nba = rem.strip(nba);

    // simplify automaton if possible
    spot::postprocessor post;
    post.set_type(spot::postprocessor::BA);
    post.set_pref(spot::postprocessor::Deterministic);
    nba = post.run(nba);

    print_hoa(std::cout, nba) << '\n';
}

int main(int argc, char **argv)
{
    if (argc < 1 || argc > 3)
        std::cout << "Please input formula file and outputs" << std::endl;
    //std::string ltlf = argv[1];
    ltlf2geba(argv[1], argv[2]);
    return 0;
}