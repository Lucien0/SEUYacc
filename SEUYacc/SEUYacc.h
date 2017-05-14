#pragma once
#include <iostream>
#include <fstream>
#include <iomanip>
#include <string>
#include <cstring>
#include <vector>
#include <set>
#include <map>
#include <cstdlib>
#include <queue>
#include <cstddef>
using namespace std;

#define EPSLONG		-1		//产生式为空
#define ACCEPT		 0		//接受状态（可规约）
#define BEGIN		 1		//Yacc段开始标记
#define LAYER_ID	 3		//检测到下一个Yacc段
#define HEADER_BEGIN 4		//Yacc文件的开始
#define HEADER_END   5		//Yacc文件的结束
#define ERROR        6		//Yacc文件出错
#define TOKEN        7		//Yacc文件中定义的标识符
#define LEFT         8		//Yacc文件中定义的具有左结合性的运算符
#define RIGHT        9		//Yacc文件中定义的具有右结合性的运算符
#define TERMINAL     10000	//终结符,从该值开始到NONTERMIANL间为终结符的编码区间
#define NONTERMINAL  20000	//非终结符，从该值开始到START(包括START)为非终结符的编码范围
#define START		 29999	//扩展文法的开始符，属于非终结符


struct producer {
	int left;//产生式左部
	vector<int> right;//产生式右部
};//存储Yacc文件中的产生式

vector<producer> producerTable;//产生式集合
set<int> leftTable;//存储具有左结合性的运算符
set<int> rightTable;//存储具有右结合性的运算符
map<int, int> precedenceTable;//优先级表
vector<int> producerPreTable;//产生式的优先级表，和上面的优先级表联合使用
							 /*为终结符和非终结符建立映射表，便于后续查表程序处理词法分析结果*/
map<string, int> tsymTable;//建立终结符的映射表
map<string, int> ntsymTable;//建立非终结符的映射表
map<int, vector<int> > hpSet;//存储以某一非终结符为左部的所有产生式集合,便于后续LR1项集算法的生成
map<int, string> semantAction;//产生式的语义动作

struct item {
	int producerTerm;//item对应的产生式索引
	int dotpos;//item中的dot
	set<int> predict;//item的可规约预测符
	void move() { dotpos++; }//移动dot点到下一个符号
	int getCurSym() {
		/*需判断dotpos是否是否已到产生式尾部,若已到产生式尾部，则可以进行规约*/
		if (dotpos < producerTable[producerTerm].right.size())
			return producerTable[producerTerm].right[dotpos];
		else
			return -1;
	}//该函数用于帮助求项集的闭包
	int getNextSym() {
		dotpos++;
		int tmp = getCurSym();
		dotpos--;
		return tmp;
	}//该函数用于帮助求item项的预测符predict
	bool equal(const item i) {
		if (i.producerTerm == this->producerTerm && i.dotpos == this->dotpos && i.predict == this->predict)
			return true;
		else
			return false;
	}
	bool equalLALR(const item i) {
		if (i.producerTerm == this->producerTerm && i.dotpos == this->dotpos)
			return true;
		else
			return false;
	}
	friend bool operator < (const item& a, const item& b)
	{
		if (a.producerTerm == b.producerTerm)
			return a.dotpos < b.dotpos;
		else
			return a.producerTerm == b.producerTerm;
	}
};//PDA项集中的基本组成项

struct ItemSet {
	vector<item> iSet;//存储项集中的所有项
	set<item> rSet;//可规约项集合
	item* isInSet(item it) {
		for (size_t i = 0; i < iSet.size(); i++) {
			if (it.producerTerm == iSet[i].producerTerm && it.dotpos == iSet[i].dotpos) {
				return &(iSet[i]);
			}
		}
		return NULL;
	}//判断item项it是否在该项集中
	bool contains(item it) {
		for (size_t i = 0; i<iSet.size(); i++) {
			if (it.equal(this->iSet[i]))
				return true;
		}
		return false;
	}//判断item项it是否在项集中
	bool containsLALR(item it) {
		for (size_t i = 0; i<iSet.size(); i++) {
			if (it.equalLALR(this->iSet[i]))
				return true;
		}
		return false;
	}//判断item项it是否在项集中
	bool isEqual(const ItemSet is) {
		if (this->iSet.size() != is.iSet.size())
			return false;
		else {
			for (size_t i = 0; i <is.iSet.size(); i++) {
				if (!this->contains(is.iSet.at(i)))
					return false;
			}
			return true;
		}
	}
	bool isEqualLALR(const ItemSet is) {
		if (this->iSet.size() != is.iSet.size())
			return false;
		else {
			for (size_t i = 0; i <is.iSet.size(); i++) {
				if (!this->containsLALR(is.iSet.at(i)))
					return false;
			}
			return true;
		}
	}
	void addPredict(item it) {
		for (size_t i = 0; i<iSet.size(); i++) {
			if (it.equalLALR(this->iSet[i]))
				for (set<int>::iterator iterator1 = it.predict.begin(); iterator1 != it.predict.end(); ++iterator1) {
					this->iSet[i].predict.insert(*iterator1);
				}
		}
	}
};//PDA项集

struct PDA {
	vector<ItemSet> itemSets;//PDA中的所有项集
	vector<map<int, int> > nextItemMap;//PDA中项集的DFA,向量下标表示出发项集,map.first表示经过的边,map.second表示目的项集
};//下推自动机

PDA LR1, LALR;//LR1下推自动机和LALR自动机


			  //函数定义
int checkSpecSign(char c);//判断转义字符/后的符号类型
bool analysProducer(string product);//分析并存储产生式
void genHashProducer();//生成hpSet
void createPDA();//创建LR1项集族
void closure(ItemSet& src);//求项集src的闭包
set<int> First(int n, bool& isEp);//求非终结符的First项集
int getLR1Item(int edge, ItemSet is);//判定LR1是否有经边edge到达项集is的,若已有则返回目的项集的编号，否则返回-1

void LR2LALR();
void printresult(const PDA grammar);

void printPredictTable();

struct parse_table_item {
	map<int, vector<int>>& GetAction() { return action; }
	map<int, int>& GetGoto() { return gotos; }
	void AddtoAction(int ter, vector<int> rs) {
		//action.insert(make_pair(ter,rs));
		if (!action.insert(make_pair(ter, rs)).second) {
			cout << "There is conflict in" << this->state << "\t" << ter << endl;
			if (producerPreTable[rs[1]] > precedenceTable[ter]) {
				action.erase(ter);
				action.insert(make_pair(ter, rs));
				cout << "produce > operate" << endl;
			}
			else if (producerPreTable[rs[1]] == precedenceTable[ter]) {
				if (leftTable.count(ter)) {
					action.erase(ter);
					action.insert(make_pair(ter, rs));
					cout << "left table find" << endl;
				}
			}
		}
	}
	void AddtoGoto(int nonter, int s) {
		gotos.insert(make_pair(nonter, s));
	}
	void create(ItemSet x) {
		for (map<int, int>::iterator iterator1 = LALR.nextItemMap[state].begin(); iterator1 != LALR.nextItemMap[state].end(); ++iterator1) {
			if (iterator1->first >= 10000 && iterator1->first<20000) {          //是终结符
				vector<int> temp;
				temp.push_back(1);
				temp.push_back(iterator1->second);
				AddtoAction(iterator1->first, temp);
			}
			if (iterator1->first >= 20000 && iterator1->first<30000) {          //是非终结符
				AddtoGoto(iterator1->first, iterator1->second);
			}
		}
		for (vector<item>::iterator iterator2 = x.iSet.begin(); iterator2 != x.iSet.end(); ++iterator2) {
			if (iterator2->getCurSym() == -1) {
				for (set<int>::iterator iterator3 = iterator2->predict.begin(); iterator3 != iterator2->predict.end(); ++iterator3) {
					if (producerTable[iterator2->producerTerm].left == 29999) {
						vector<int> temp;
						temp.push_back(0);
						AddtoAction(*iterator3, temp);
					}
					else {
						vector<int> temp;
						temp.push_back(-1);
						temp.push_back(iterator2->producerTerm);
						AddtoAction(*iterator3, temp);
					}
				}
			}
		}
	}
	parse_table_item(int st) { state = st; }

	int state;
	map<int, vector<int>> action;
	map<int, int> gotos;
};
vector<parse_table_item> parseTable;

void createParseTable();
void genSemantprogram();

void writeTerminalTable();
void writeProducers();//生成产生式文件
