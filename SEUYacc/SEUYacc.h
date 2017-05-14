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

#define EPSLONG		-1		//����ʽΪ��
#define ACCEPT		 0		//����״̬���ɹ�Լ��
#define BEGIN		 1		//Yacc�ο�ʼ���
#define LAYER_ID	 3		//��⵽��һ��Yacc��
#define HEADER_BEGIN 4		//Yacc�ļ��Ŀ�ʼ
#define HEADER_END   5		//Yacc�ļ��Ľ���
#define ERROR        6		//Yacc�ļ�����
#define TOKEN        7		//Yacc�ļ��ж���ı�ʶ��
#define LEFT         8		//Yacc�ļ��ж���ľ��������Ե������
#define RIGHT        9		//Yacc�ļ��ж���ľ����ҽ���Ե������
#define TERMINAL     10000	//�ս��,�Ӹ�ֵ��ʼ��NONTERMIANL��Ϊ�ս���ı�������
#define NONTERMINAL  20000	//���ս�����Ӹ�ֵ��ʼ��START(����START)Ϊ���ս���ı��뷶Χ
#define START		 29999	//��չ�ķ��Ŀ�ʼ�������ڷ��ս��


struct producer {
	int left;//����ʽ��
	vector<int> right;//����ʽ�Ҳ�
};//�洢Yacc�ļ��еĲ���ʽ

vector<producer> producerTable;//����ʽ����
set<int> leftTable;//�洢���������Ե������
set<int> rightTable;//�洢�����ҽ���Ե������
map<int, int> precedenceTable;//���ȼ���
vector<int> producerPreTable;//����ʽ�����ȼ�������������ȼ�������ʹ��
							 /*Ϊ�ս���ͷ��ս������ӳ������ں�����������ʷ��������*/
map<string, int> tsymTable;//�����ս����ӳ���
map<string, int> ntsymTable;//�������ս����ӳ���
map<int, vector<int> > hpSet;//�洢��ĳһ���ս��Ϊ�󲿵����в���ʽ����,���ں���LR1��㷨������
map<int, string> semantAction;//����ʽ�����嶯��

struct item {
	int producerTerm;//item��Ӧ�Ĳ���ʽ����
	int dotpos;//item�е�dot
	set<int> predict;//item�Ŀɹ�ԼԤ���
	void move() { dotpos++; }//�ƶ�dot�㵽��һ������
	int getCurSym() {
		/*���ж�dotpos�Ƿ��Ƿ��ѵ�����ʽβ��,���ѵ�����ʽβ��������Խ��й�Լ*/
		if (dotpos < producerTable[producerTerm].right.size())
			return producerTable[producerTerm].right[dotpos];
		else
			return -1;
	}//�ú������ڰ�������ıհ�
	int getNextSym() {
		dotpos++;
		int tmp = getCurSym();
		dotpos--;
		return tmp;
	}//�ú������ڰ�����item���Ԥ���predict
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
};//PDA��еĻ��������

struct ItemSet {
	vector<item> iSet;//�洢��е�������
	set<item> rSet;//�ɹ�Լ���
	item* isInSet(item it) {
		for (size_t i = 0; i < iSet.size(); i++) {
			if (it.producerTerm == iSet[i].producerTerm && it.dotpos == iSet[i].dotpos) {
				return &(iSet[i]);
			}
		}
		return NULL;
	}//�ж�item��it�Ƿ��ڸ����
	bool contains(item it) {
		for (size_t i = 0; i<iSet.size(); i++) {
			if (it.equal(this->iSet[i]))
				return true;
		}
		return false;
	}//�ж�item��it�Ƿ������
	bool containsLALR(item it) {
		for (size_t i = 0; i<iSet.size(); i++) {
			if (it.equalLALR(this->iSet[i]))
				return true;
		}
		return false;
	}//�ж�item��it�Ƿ������
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
};//PDA�

struct PDA {
	vector<ItemSet> itemSets;//PDA�е������
	vector<map<int, int> > nextItemMap;//PDA�����DFA,�����±��ʾ�����,map.first��ʾ�����ı�,map.second��ʾĿ���
};//�����Զ���

PDA LR1, LALR;//LR1�����Զ�����LALR�Զ���


			  //��������
int checkSpecSign(char c);//�ж�ת���ַ�/��ķ�������
bool analysProducer(string product);//�������洢����ʽ
void genHashProducer();//����hpSet
void createPDA();//����LR1���
void closure(ItemSet& src);//���src�ıհ�
set<int> First(int n, bool& isEp);//����ս����First�
int getLR1Item(int edge, ItemSet is);//�ж�LR1�Ƿ��о���edge�����is��,�������򷵻�Ŀ����ı�ţ����򷵻�-1

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
			if (iterator1->first >= 10000 && iterator1->first<20000) {          //���ս��
				vector<int> temp;
				temp.push_back(1);
				temp.push_back(iterator1->second);
				AddtoAction(iterator1->first, temp);
			}
			if (iterator1->first >= 20000 && iterator1->first<30000) {          //�Ƿ��ս��
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
void writeProducers();//���ɲ���ʽ�ļ�
