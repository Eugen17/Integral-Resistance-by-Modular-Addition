#include <iostream>
#include <cstdint>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <tuple>
#include <algorithm>
#include <utility>
#include <stdlib.h>     
#include "BCData.hpp"
#include "configBC.hpp"

using namespace std;
typedef unsigned int uint;

//Here are example functions on how to reproduce results
//From the name of the function, it is clear which case is tested
//Decreasing number of rounds than given most probably will lead that IR will be not proven
//Note that for now, code is given more for verification of our bounds than for actual use, as in this case code becomes understandable for reader.

void prove_integral_resistance_modular_addition_t_1_skinny() {
	string outputFile = "Skinny_t_1.txt";
	if (ifstream(outputFile)) {
		remove(outputFile.c_str());
	}
	for (uint r = 11; r <= 12; r++) {
		ofstream out(outputFile, ios::app);
		out << endl << endl;
		out << "Checking integral resistance for t=1 for " << r << " rounds, i.e. looking just one division trail from 01...1 to 10...0" << endl;
		out.close();
		auto BCD = genDataSkinny64(r);
		auto iok = BCD.improvedDynamicSearch(0, 0, outputFile);

	}
}

void prove_integral_resistance_modular_addition_t_1_present() {
	string outputFile = "Present_t_1.txt";
	if (ifstream(outputFile)) {
		remove(outputFile.c_str());
	}
	for (uint r = 10; r <= 12; r++) {
		ofstream out(outputFile, ios::app);
		out << endl << endl;
		out << "Checking integral resistance for t=1 for " << r << " rounds, i.e. looking just one division trail from 01...1 to 10...0" << endl;
		out.close();
		auto BCD = genDataPRESENT(r, false);
		auto iok = BCD.improvedDynamicSearch(0, 0, outputFile);

	}
}

void prove_integral_resistance_modular_addition_t_1_gift() {
	string outputFile = "Gift_t_1.txt";
	if (ifstream(outputFile)) {
		remove(outputFile.c_str());
	}
	for (uint r = 9; r <= 11; r++) {
		ofstream out(outputFile, ios::app);
		out << endl << endl;
		out << "Checking integral resistance for t=1 for " << r << " rounds, i.e. looking just one division trail from 01...1 to 10...0" << endl;
		out.close();
		auto BCD = genDataGIFT(r);
		auto iok = BCD.improvedDynamicSearch(0, 0, outputFile);
	}
}

void prove_integral_resistance_modular_addition_t_2_present() {
	string outputFile = "Present_t_2.txt";
	if (ifstream(outputFile)) {
		remove(outputFile.c_str());
	}
	for (uint r = 10; r <= 12; r++) {
		ofstream out(outputFile, ios::app);
		out << endl << endl;
		out << "Checking integral resistance for t=2 for " << r << " rounds, i.e. building integral resistant matrix " << endl;
		out << "I(E) is of dimension 4*4, where rows are some key patterns, inputs are u_{js+1} for output e_{is+1}, where s=n/t is the length of word and i,j = 0...t-1" << endl;
		out.close();
		auto BCD = genDataPRESENT(r, false);
		BCD.searchIntegralResistanceModularAddition(2,outputFile);
	}
}

void prove_integral_resistance_modular_addition_t_2_skinny() {
	string outputFile = "Skinny_t_2.txt";
	if (ifstream(outputFile)) {
		remove(outputFile.c_str());
	}
	for (uint r = 11; r <= 12; r++) {
		ofstream out(outputFile, ios::app);
		out << endl << endl;
		out << "Checking integral resistance for t=2 for " << r << " rounds, i.e. building integral resistant matrix " << endl;
		out << "I(E) is of dimension 4*4, where rows are some key patterns, inputs are u_{js+1} for output e_{is+1}, where s=n/t is the length of word and i,j = 0...t-1" << endl;
		out.close();
		auto BCD = genDataSkinny64(r);
		BCD.searchIntegralResistanceModularAddition(2, outputFile);
	}
}

void prove_integral_resistance_modular_addition_t_2_gift() {
	string outputFile = "Gift_t_2.txt";
	if (ifstream(outputFile)) {
		remove(outputFile.c_str());
	}
	for (uint r = 10; r <= 11; r++) {
		ofstream out(outputFile, ios::app);
		out << endl << endl;
		out << "Checking integral resistance for t=2 for " << r << " rounds, i.e. building integral resistant matrix " << endl;
		out << "I(E) is of dimension 4*4, where rows are some key patterns, inputs are u_{js+1} for output e_{is+1}, where s=n/t is the length of word and i,j = 0...t-1" << endl;
		out.close();
		auto BCD = genDataGIFT(r);
		BCD.searchIntegralResistanceModularAddition(2, outputFile);
	}
}

int main(){
	
	prove_integral_resistance_modular_addition_t_1_gift();
	prove_integral_resistance_modular_addition_t_1_skinny();
	prove_integral_resistance_modular_addition_t_1_present();
	prove_integral_resistance_modular_addition_t_2_gift();
	prove_integral_resistance_modular_addition_t_2_skinny();
	prove_integral_resistance_modular_addition_t_2_present();	
}
