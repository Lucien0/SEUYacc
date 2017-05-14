
/*  myyacc.txt
*/
#include <vector>
#include <stack>
#include <string>
#include "symTable.h"
using namespace std;

int yylval;


void execAction(vector<int> s, int p, symTable& sym_table, stack<int>& semantStack){
int tmp;
switch(p){
case 22:
	sym_table.setValue(s[0],s[2]);
	break;
case 34:
	tmp =(s[0]==s[2]);
	semantStack.push(tmp);
	break;
case 36:
	tmp =s[0]+s[2];
	semantStack.push(tmp);
	break;
case 38:
	tmp =s[0]-s[2];
	semantStack.push(tmp);
	break;
case 40:
	tmp =s[0]*s[2];
	semantStack.push(tmp);
	break;
case 42:
	tmp =s[0]/s[2];
	semantStack.push(tmp);
	break;
case 44:
	tmp =s[0]%s[2];
	semantStack.push(tmp);
	break;
case 46:
	tmp =s[1];
	semantStack.push(tmp);
	break;
case 48:
	tmp =0-s[2];
	semantStack.push(tmp);
	break;
case 50:
	tmp =sym_table.getValue(s[0]);
	semantStack.push(tmp);
	break;
case 52:
	tmp =yylval;
	semantStack.push(tmp);
	break;
}
}
