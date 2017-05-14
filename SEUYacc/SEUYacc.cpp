// SEUYacc.cpp : �������̨Ӧ�ó������ڵ㡣
//

#include "stdafx.h"
#include "SeuYacc.h"
#include <cstdlib>
ifstream ifile;
ofstream ofile, ofile1;

int main() {
	string srcFile = "myyacc.txt";//Yacc�ļ�
	ifile.open(srcFile.c_str(), ios::in);
	ofile.open("myyacc.h", ios::out);
	if (!ifile.is_open()) {
		cerr << "Open file error!" << endl;
		exit(1);
		int a;
	}
	char c = ifile.get();
	int state = checkSpecSign(c);
	if (state != HEADER_BEGIN) {
		cerr << "The input file has no coorect formation,Please try again!\n";
		exit(1);
	}

	while (!ifile.eof() && state != HEADER_END) {
		c = ifile.get();
		if (c == '%') {
			state = checkSpecSign(c);
			if (state == ERROR) {
				cerr << "There is an error in file!" << endl;
				exit(1);
			}
			continue;
		}
		ofile.put(c);
	}//������ɶ԰���ͷ�ļ���ɨ��

	int priority = 1;//���ڱ���ս���ŵ����ȼ�
	state = BEGIN;//��ʾ������һ��ɨ��
	while (!ifile.eof() && state != LAYER_ID) {
		c = ifile.get();
		if (c == '%') {
			state = checkSpecSign(c);
			if (state == ERROR) {
				cerr << "There is an error in file!" << endl;
				exit(1);
			}
			if (state == TOKEN) {
				string nonTerList;
				string nonTerm;
				pair<string, int> tp;
				getline(ifile, nonTerList);//��ȡTOKEN��һ���Դ�����
				size_t start = 0;//����ͷβ�����±�����,���ڴ�nonTerList����subStr������ֳ�����Token
				size_t end = nonTerList.find(' ', start);
				//���濪ʼ�������е�����Token����뵽�ս������
				while (end != string::npos) {
					nonTerm = nonTerList.substr(start, end - start);
					tp.first = nonTerm;
					tp.second = TERMINAL + tsymTable.size();
					tsymTable.insert(tp);
					start = end + 1;
					end = nonTerList.find(' ', start);
				}
				//���潫�����е����һ��Token����뵽�ս������
				nonTerm = nonTerList.substr(start, nonTerList.size() - start);
				tp.first = nonTerm;
				tp.second = TERMINAL + tsymTable.size();
				tsymTable.insert(tp);
			}
			if (state == LEFT || state == RIGHT) {
				string nonTerList;
				string nonTerm;
				pair<string, int> tp;
				getline(ifile, nonTerList);
				size_t start = 0;
				size_t end = nonTerList.find(' ', start);
				while (end != string::npos) {
					nonTerm = nonTerList.substr(start + 1, end - start - 2);
					tp.first = nonTerm;
					tp.second = TERMINAL + tsymTable.size();
					tsymTable.insert(tp);
					if (state == LEFT)
						leftTable.insert(tp.second);
					else
						rightTable.insert(tp.second);
					pair<int, int> p;
					p.first = tp.second;
					p.second = priority;
					precedenceTable.insert(p);
					start = end + 1;
					end = nonTerList.find(' ', start);
				}
				nonTerm = nonTerList.substr(start + 1, nonTerList.size() - start - 2);
				tp.first = nonTerm;
				tp.second = TERMINAL + tsymTable.size();
				tsymTable.insert(tp);
				if (state == LEFT)
					leftTable.insert(tp.second);
				else
					rightTable.insert(tp.second);
				pair<int, int> p;
				p.first = tp.second;
				p.second = priority;
				precedenceTable.insert(p);
				priority++;
			}
		}
	}//��������˶Զ���ε�ɨ��

	producer ap;
	ap.left = START;
	producerTable.push_back(ap);//����չ�ķ���ʼ����ʽ���뵽����ʽ������
	producerPreTable.push_back(0);

	state = BEGIN;
	char buf[BUFSIZ];//�洢ÿ���������ʽ�Ļ�����
	int pos;//��ȡɨ��������ʽ�Ķ�ͷ
	while (!ifile.eof() && state != LAYER_ID) {
		c = ifile.get();
		if (c == '%') {
			state = checkSpecSign(c);
			if (state == ERROR) {
				cerr << "There is an error in file!" << endl;
				exit(1);
			}
			continue;
		}
		if (c == '\t' || c == '\n' || c == ' ') continue;//�����س��������Լ��ո�
		pos = 0;//����ͷ��������,׼�������µĹ������ʽ
		while (c != ';') {
			buf[pos] = c;
			pos++;
			c = ifile.get();
			if (c == '\'') {
				for (size_t i = 0; i < 3; i++) {
					buf[pos] = c;
					pos++;
					c = ifile.get();
				}
			}
			if (c == '{') {
				while (c != '}') {
					buf[pos] = c;
					pos++;
					c = ifile.get();
				}
			}
		}
		buf[pos] = c;//�������һ��';'
		buf[++pos] = '\0';//���봮β�Ա�ת����string����
		string produce(buf);
		if (!analysProducer(produce)) {
			cerr << "There is an error in regular phase!" << endl;
			exit(1);
		}//�������洢����ʽ
	}//��������˹���ε�ɨ��

	producerTable[0].right.push_back(producerTable[1].left);//�����չ�ķ��ĵ�һ������ʽ
	pair<string, int> tp;
	tp.first = "$";//���������$
	tp.second = NONTERMINAL - 1;
	tsymTable.insert(tp);
	//���������չ�ķ������������ں�������LR1���

	genHashProducer();
	createPDA();//����LR1���

	LR2LALR();

	printresult(LALR);
	createParseTable();
	genSemantprogram();
	writeTerminalTable();
	writeProducers();//���ɲ���ʽ�ļ�
	printPredictTable();
}

int checkSpecSign(char c) {
	char nextc = ifile.get();
	switch (nextc) {
	case '%':
		return LAYER_ID;
	case '{':
		return HEADER_BEGIN;
	case '}':
		return HEADER_END;
	case 't':
	case 'l':
	case 'r': {
		char buf[10];
		int pos = 1;
		buf[0] = nextc;
		nextc = ifile.get();
		while (nextc != ' ' && nextc != '\t' && nextc != '\n') {
			buf[pos] = nextc;
			nextc = ifile.get();
			pos++;
		}
		buf[pos] = '\0';
		string bbuf(buf);
		string t1("token");
		string t2("left");
		string t3("right");
		if (bbuf == t1) return TOKEN;
		if (bbuf == t2) return LEFT;
		if (bbuf == t3) return RIGHT;
		else return ERROR;
	}
	default:
		ifile.unget();
		return ERROR;
	}
}

bool analysProducer(string product) {
	/*����������ͷ�����ڲ����ȡ����ʽ*/
	int pos = 0;
	int tpos = 0;

	int priority = 0;//���ڱ�ʾ����ʽ�����ȼ�

	producer tmp;//���ڴ洢����ʽ����ʱ����

	char c = product[pos];
	while (c != ' ' && c != '\t' && c != '\n' && c != '\r') {
		tpos++;
		c = product[tpos];
	}
	string left = product.substr(pos, tpos - pos);//��ȡ����ʽ��

	if (tsymTable.count(left)) {
		cout << "NonTerminatedSym define error!" << endl;
		return false;
	}//����ʽ��˲��ܳ����ս��

	if (!ntsymTable.count(left)) {
		pair<string, int> ntp;
		ntp.first = left;
		ntp.second = NONTERMINAL + ntsymTable.size();
		ntsymTable.insert(ntp);
	}//������ʽ��Ϊ�µķ��ս�������������ս������

	pos = tpos;
	while (c == ' ' || c == '\n' || c == '\t' || c == '\r') {
		pos++;
		c = product[pos];
	}//�����޹��ַ���׼����ȡ����ʽ�Ҳ�

	if (c != ':') {
		cout << "Producer formation Error!" << endl;
		return false;
	}//����ʽ���Ҳ�����'��'Ϊ�ָ�

	tmp.left = ntsymTable[left];//�������ʽ��
	while (1) {
		pos++;
		c = product[pos];
		tmp.right.clear();//��ʼ������ղ���ʽ�Ҳ�
		priority = 0;
		while (c == ' ' || c == '\n' || c == '\t' || c == '\r') {
			pos++;
			c = product[pos];
		}//�����޹��ַ�

		string action;//yacc���嶯��
		int lastTsym = 0;
		while (c != '|' && c != ';') {//δ������һ������ʽ������β
			tpos = pos;
			if (c == '{') {
				pos++;
				c = product[pos];
				while (c != '}') {
					action += c;
					pos++;
					c = product[pos];
				}
				pos++;
				c = product[pos];
				break;
			}
			bool opeFlag = false;//��־������Ϊtrueʱ��ʾ�����˷��ţ���Ҫ�����ս���Ĵ���
			if (c == '\'') opeFlag = true;//��ʾ�����˲�����
			while (c != ' ' && c != '\n' && c != '\t' && c != '\r') {
				tpos++;
				c = product[tpos];
			}
			string str;
			if (opeFlag) {
				str = product.substr(pos + 1, tpos - pos - 2);//��ȡ������
				if (!tsymTable.count(str)) {
					pair<string, int> tp;
					tp.first = str;
					tp.second = TERMINAL + tsymTable.size();
					tsymTable.insert(tp);
				}//���ò�������ż��뵽�ս����
				tmp.right.push_back(tsymTable[str]);
				lastTsym = tsymTable[str];
			}
			else {
				str = product.substr(pos, tpos - pos);
				//���str�������ս�����ֲ��ڷ��ս�������ж�Ϊ�µķ��ս����������Ӧ����
				if (!tsymTable.count(str)) {
					if (!ntsymTable.count(str)) {
						pair<string, int> ntp;
						ntp.first = str;
						ntp.second = NONTERMINAL + ntsymTable.size();
						ntsymTable.insert(ntp);
					}
					tmp.right.push_back(ntsymTable[str]);
				}
				else {
					tmp.right.push_back(tsymTable[str]);
					lastTsym = tsymTable[str];
				}
			}
			pos = tpos;
			while (c == ' ' || c == '\n' || c == '\t' || c == '\r') {
				pos++;
				c = product[pos];
			}
		}
		if (precedenceTable.count(lastTsym))
			priority = precedenceTable[lastTsym];
		producerTable.push_back(tmp);
		producerPreTable.push_back(priority);
		if (action != "") {
			pair<int, string> yact;
			yact.first = producerTable.size() - 1;
			yact.second = action;
			semantAction.insert(yact);
		}
		if (c == ';') return true;
	}//��ɨ���㷨��ȱ�����ڲ���ɨ��մ�����ʽ
}

void genHashProducer() {
	pair<int, vector<int> > tmp;
	for (int i = 0; i < producerTable.size(); i++) {
		hpSet[producerTable[i].left].push_back(i);
	}
}

void createPDA() {
	item start;//��ʼitem��������ɳ�ʼ�I0
	start.producerTerm = 0;
	start.dotpos = 0;
	start.predict.insert(tsymTable["$"]);

	//auto indexCount = 0;
	ItemSet I0;//��ʼ�I0
	I0.iSet.push_back(start);
	closure(I0);//���ʼ��ıհ�

	queue<ItemSet> q;//���ù�ȱ��������������
	LR1.itemSets.push_back(I0);
	q.push(I0);
	auto index = 0;//������¼��ǰ������������
	//int srcIndex = 1;//������¼LR1.iSet���Ѿ�����հ����������
	auto desItemIndex = 1;//������¼LR1.iSet�е��������ɵ��������
	while (!q.empty()) {
		ItemSet is = q.front();//ȡ��q�е�������������µ��
		q.pop();
		set<int> edgeSet;//������¼���ԴӸ���������ı�
		vector<ItemSet> tmpPDA;//���������ɵ��������LR1�����е���ظ�������tmpPDA���Ƚ��������չ
		int tmpIndex = 0;
		map<int, int> edges;//������¼��һ������ɵ����������ʱ���ϣ��ü�����Ҫ�����ж��Ƿ�����LR1��������ظ�����
							//�����ҳ��is�е�ȫ��edge
		for (size_t i = 0; i < is.iSet.size(); i++) {
			int edge = is.iSet[i].getCurSym();
			if (edge == -1) continue;
			else if (!edgeSet.count(edge)) {
				edgeSet.insert(edge);
				edges.insert(make_pair(edge, tmpIndex));
				tmpIndex++;
				ItemSet newIS;
				tmpPDA.push_back(newIS);//Ϊ��һ�����������ռ�
			}
		}
		if (!edges.empty()) {
			for (size_t i = 0; i < is.iSet.size(); i++) {
				int edge = is.iSet[i].getCurSym();
				if (edge == -1) continue;
				else {
					item t = is.iSet[i];
					t.move();
					tmpPDA[edges.at(edge)].iSet.push_back(t);
				}//���is�е�ÿ�����ڿɹ�Լ״̬��item�����move����,����is�����п����������ӵ���Ӧ����ߵļ�����
			}
			for (auto k = edges.begin(); k != edges.end(); k++) {
				closure(tmpPDA[k->second]);//����������ıհ�
				int des = getLR1Item(k->first, tmpPDA[k->second]);//�ж������ɵ���Ƿ��Ѵ�����LR1�У����Ѵ���Ҫ����ʱ���DFA������
				if (des >= 0) k->second = des;
				else {
					LR1.itemSets.push_back(tmpPDA[k->second]);
					k->second = desItemIndex;
					q.push(LR1.itemSets[desItemIndex]);
					desItemIndex++;
				}
			}
		}
		LR1.nextItemMap.push_back(edges);
		index++;
	}
}

void closure(ItemSet &src) {
	queue<item> q;//����q ���ڹ�ȱ���src�е��������ɱհ���
				  //��src�е�Item�����η��������
	for (size_t i = 0; i < src.iSet.size(); i++) q.push(src.iSet[i]);
	//���濪ʼ��ȱ��������е�Ԫ��
	while (!q.empty()) {
		item it = q.front();
		q.pop();
		int curSym = it.getCurSym();//��ȡ����ʽ��dotpos�Ҳ����ڵ��ַ�
									//���dotpos�Ѵ����ʽβ��,��˵���ɹ�Լ,��¼���ÿɹ�Լ��
		if (curSym == -1) { src.rSet.insert(it); }
		//���curSym�Ƿ��ս��
		if (NONTERMINAL <= curSym && curSym <= START) {
			vector<int> *ps = &(hpSet.at(curSym));//��������Է��ս��curSymΪ����ʽ��ʽ�Ĳ���ʽ����
			int nextSym = it.getNextSym();
			for (size_t i = 0; i < ps->size(); i++) {
				item tmp;
				tmp.producerTerm = ps->at(i);
				tmp.dotpos = 0;
				//�ж���tmp�Ƿ������src�У���������򴴽���src�м�����tmp,����tmp��Ԥ�������
				//����ֱ�ӽ����Ԥ�����ֱ�Ӽ��뵽�������predict��
				item *tmp2 = src.isInSet(tmp);
				if (tmp2 == NULL) {
					if (nextSym == -1) {
						tmp.predict = it.predict;
					}//tmp��predict�̳���it��predict
					else if (TERMINAL <= nextSym && nextSym < NONTERMINAL) {
						tmp.predict.insert(nextSym);
					}//���nextSym���ս��,�򽫸��ս���ӵ�tmp��predict��
					else {
						bool isEp = false;
						set<int> p = First(nextSym, isEp);
						for (auto j = p.begin(); j != p.end(); j++) tmp.predict.insert(*j);
						while (isEp) {
							isEp = false;
							item tmp3 = it;
							tmp3.move();
							int nextSym2 = tmp3.getNextSym();
							if (nextSym2 == -1) {
								for (auto j = it.predict.begin(); j != it.predict.end(); j++) tmp.predict.insert(*j);
							}
							else if (TERMINAL <= nextSym2 && nextSym2 < NONTERMINAL) {
								tmp.predict.insert(nextSym2);
							}
							else {
								p = First(nextSym2, isEp);
								for (auto j = p.begin(); j != p.end(); j++) tmp.predict.insert(*j);
							}
						}
					}//���nextSym�Ƿ��ս��,����First(nextSym),�����÷��ս�����е���ȫ���뵽tmp��predict��
					q.push(tmp);
					src.iSet.push_back(tmp);//��tmp�����src
				}
				else {
					if (nextSym == -1) {
						for (auto j = it.predict.begin(); j != it.predict.end(); j++)
							tmp2->predict.insert(*j);
					}
					else if (TERMINAL <= nextSym && nextSym < NONTERMINAL) {
						tmp2->predict.insert(nextSym);
					}
					else {
						bool isEp = false;
						set<int> p = First(nextSym, isEp);
						for (auto j = p.begin(); j != p.end(); j++) tmp2->predict.insert(*j);
						while (isEp) {
							isEp = false;
							item tmp3 = it;
							tmp3.move();
							int nextSym2 = tmp3.getNextSym();
							if (nextSym2 == -1) {
								for (auto j = it.predict.begin(); j != it.predict.end(); j++)
									tmp2->predict.insert(*j);
							}
							else if (TERMINAL <= nextSym2 && nextSym2 < NONTERMINAL) {
								tmp2->predict.insert(nextSym2);
							}
							else {
								p = First(nextSym2, isEp);
								for (auto j = p.begin(); j != p.end(); j++) tmp2->predict.insert(*j);
							}
						}
					}
				}
			}
		}
	}
}

set<int> First(int n, bool &isEp) {
	vector<int> ps = hpSet[n];
	set<int> res;
	for (size_t i = 0; i < ps.size(); i++) {
		if (producerTable[ps[i]].right.size() == 0)
			isEp = true;
	}
	for (size_t i = 0; i < ps.size(); i++) {
		if (producerTable[ps[i]].right.size()) {
			int pre = producerTable[ps[i]].right[0];
			if (TERMINAL <= pre && pre < NONTERMINAL)
				res.insert(pre);
			if (NONTERMINAL <= pre && pre <= START) {
				set<int> tmp;
				if (pre == n) {
					if (isEp) {
						if (producerTable[ps[i]].right.size() <= 1) {
							cerr << "Error in rule!";
							exit(1);
						}
						else {
							int pre2 = producerTable[ps[i]].right[1];
							bool isEp2 = false;
							tmp = First(pre2, isEp2);
						}
					}
					else
						continue;
				}
				else {
					tmp = First(pre, isEp);
				}
				for (auto j = tmp.begin(); j != tmp.end(); j++) res.insert(*j);
			}
		}
	}
	return res;
}

int getLR1Item(int edge, ItemSet is) {
	set<int> desItemSet;//Ŀ����ĺ�ѡ�
						//����LR1���������DFA,���ҳ����о���edge�ɵ�����
	for (size_t i = 0; i < LR1.nextItemMap.size(); i++) {
		if (LR1.nextItemMap[i].count(edge)) {
			int tempvalue = LR1.nextItemMap[i].at(edge);
			desItemSet.insert(tempvalue);
		}
	}
	for (auto i = desItemSet.begin(); i != desItemSet.end(); i++) {
		ItemSet tmp = LR1.itemSets[*i];
		if (is.isEqual(tmp))
			return *i;
	}
	return -1;
}

void LR2LALR() {

	int* combain = new int[LR1.itemSets.size()];
	for (int l = 0; l < LR1.itemSets.size(); ++l) {
		combain[l] = -1;
	}
	int cnt = -1;
	ItemSet temp;
	for (int i = 0; i < LR1.itemSets.size(); i++) {
		if (combain[i] == -1) {
			cnt++;
			combain[i] = cnt;
			temp = LR1.itemSets[i];
			for (int j = i + 1; j < LR1.itemSets.size(); ++j) {
				if (combain[j] == -1 && LR1.itemSets[i].isEqualLALR(LR1.itemSets[j])) {
					combain[j] = cnt;
					for (int k = 0; k < LR1.itemSets[j].iSet.size(); ++k) {
						temp.addPredict(LR1.itemSets[j].iSet[k]);
					}
				}
			}
			LALR.itemSets.push_back(temp);
		}
	}
	map<int, int> tempmap;
	for (int n = 0; n < cnt + 1; ++n) {
		LALR.nextItemMap.push_back(tempmap);
	}
	for (int m = 0; m < LR1.itemSets.size(); ++m) {
		for (map<int, int>::iterator iterator1 = LR1.nextItemMap[m].begin(); iterator1 != LR1.nextItemMap[m].end(); ++iterator1) {
			LALR.nextItemMap[combain[m]].insert(make_pair(iterator1->first, combain[iterator1->second]));
			//tempmap.insert(make_pair(iterator1->first,combain[iterator1->second]));
		}
	}
	cout << "There is LALR " << cnt << endl;
	delete[]combain;
}

void printresult(const PDA grammar) {
	//�������
	for (auto i = tsymTable.begin(); i != tsymTable.end(); i++) {
		cout << i->first << ' ' << i->second << endl;
	}
	cout << "NonTerminal:" << endl;
	for (auto i = ntsymTable.begin(); i != ntsymTable.end(); i++) {
		cout << i->first << ' ' << i->second << endl;
	}
	cout << "Producer:" << endl;
	for (auto i = producerTable.begin(); i != producerTable.end(); i++) {
		cout << i->left << "-->";
		for (size_t j = 0; j < i->right.size(); j++)
			cout << (i->right).at(j) << ' ';
		cout << endl;
	}
	cout << "hpSet:" << endl;
	for (auto i = hpSet.begin(); i != hpSet.end(); i++) {
		cout << i->first << "-->";
		for (size_t j = 0; j < i->second.size(); j++)
			cout << (i->second).at(j) << ' ';
		cout << endl;
	}
	cout << "LALR:" << endl;
	for (size_t i = 0; i < grammar.itemSets.size(); i++) {
		cout << 'I' << i << ':' << endl;
		for (auto j = grammar.itemSets[i].iSet.begin(); j != grammar.itemSets[i].iSet.end(); j++) {
			cout << "Producer:" << j->producerTerm << " Dotpos:" << j->dotpos << " Predict:";
			for (auto k = j->predict.begin(); k != j->predict.end(); k++)
				cout << *k << '/';
			cout << endl;
		}
		cout << "Recruable State:";
		if (grammar.itemSets[i].rSet.empty())
			cout << "False" << endl;
		else {
			cout << "True" << endl;
			cout << "Recurable Item:";
			for (auto j = grammar.itemSets[i].rSet.begin(); j != grammar.itemSets[i].rSet.end(); j++) {
				cout << j->producerTerm << ' ';
			}
			cout << endl;
		}
		if (!grammar.nextItemMap[i].empty()) {
			cout << "Connect:" << endl;
			for (auto j = grammar.nextItemMap[i].begin(); j != grammar.nextItemMap[i].end(); j++) {
				cout << '(' << j->first << ", " << j->second << ')' << endl;
			}
		}
	}
}

void printPredictTable() {
	ofstream predictTale("PredictTable.txt", ios::out);
	map<int, vector<int>>::iterator actionit;
	map<int, int>::iterator gotoit;
	if (!predictTale.is_open()) {
		cerr << "PredictTable.txt can't open" << endl;
		exit(1);
	}
	predictTale << parseTable.size() << endl;
	for (int i = 0; i<parseTable.size(); i++) {
		predictTale << parseTable[i].state << '\t';
		actionit = parseTable[i].action.begin();
		gotoit = parseTable[i].gotos.begin();
		predictTale << "action" << '\t';
		predictTale << parseTable[i].action.size() << '\t';
		for (int j = 0; j<parseTable[i].action.size(); j++, actionit++)
		{
			predictTale << (*actionit).first << '\t';
			switch (actionit->second[0]) {
			case -1:
				predictTale << 'r' << actionit->second[1] << '\t';
				break;
			case 1:
				predictTale << 's' << actionit->second[1] << '\t';
				break;
			case 0:
				predictTale << "acc" << '\t';
				break;
			default:
				break;
			}
		}
		predictTale << "goto" << '\t';
		predictTale << parseTable[i].gotos.size() << '\t';
		for (int k = 0; k<parseTable[i].gotos.size(); k++, gotoit++)
		{
			predictTale << (*gotoit).first << '\t' << (*gotoit).second << '\t';
		}
		//cout<<endl;
		predictTale << endl;

	}
	predictTale.close();
}

void createParseTable() {
	for (int i = 0; i < LALR.itemSets.size(); ++i) {
		parse_table_item it(i);
		it.create(LALR.itemSets[i]);
		parseTable.push_back(it);
	}
}

void writeTerminalTable() {
	ofile1.open("terminal.txt", ios::out);
	int size = tsymTable.size();
	ofile1 << size << endl;
	for (auto i = tsymTable.begin(); i != tsymTable.end(); i++) {
		ofile1 << i->first << '\t' << i->second << '\n';
	}
	ofile1.close();
}

void writeProducers() {
	ofile1.open("producer.txt", ios::out);
	int size = producerTable.size();
	ofile1 << size << endl;
	for (int i = 0; i < size; i++) {
		ofile1 << producerTable[i].left << '\t';
		int s = producerTable[i].right.size();
		ofile1 << s << '\t';
		for (int j = 0; j < s; j++) {
			ofile1 << producerTable[i].right[j] << '\t';
		}
		ofile1 << endl;
	}
	ofile1.close();
}

void genSemantprogram() {
	ofile << endl;
	ofile << "void execAction(vector<int> s, int p, symTable& sym_table, stack<int>& semantStack){" << endl;
	ofile << "int tmp;" << endl;
	ofile << "switch(p){" << endl;
	for (auto i = semantAction.begin(); i != semantAction.end(); i++) {
		ofile << "case " << i->first << ':' << endl;
		if (i->second.find("$$") != string::npos) {
			ofile << "\ttmp " << i->second.substr(2, i->second.size() - 2) << endl;
			ofile << "\tsemantStack.push(tmp);" << endl;
		}
		else {
			ofile << '\t' << i->second << endl;
		}
		ofile << "\tbreak;" << endl;
	}
	ofile << "}\n}" << endl;
}