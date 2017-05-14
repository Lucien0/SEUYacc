// SEUYacc.cpp : 定义控制台应用程序的入口点。
//

#include "stdafx.h"
#include "SeuYacc.h"
#include <cstdlib>
ifstream ifile;
ofstream ofile, ofile1;

int main() {
	string srcFile = "myyacc.txt";//Yacc文件
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
	}//以上完成对包含头文件的扫描

	int priority = 1;//用于标记终结符号的优先级
	state = BEGIN;//表示进入下一段扫描
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
				getline(ifile, nonTerList);//读取TOKEN的一行以待分析
				size_t start = 0;//设置头尾两个下标索引,便于从nonTerList中用subStr函数拆分出单个Token
				size_t end = nonTerList.find(' ', start);
				//下面开始将该行中的所有Token项加入到终结符表中
				while (end != string::npos) {
					nonTerm = nonTerList.substr(start, end - start);
					tp.first = nonTerm;
					tp.second = TERMINAL + tsymTable.size();
					tsymTable.insert(tp);
					start = end + 1;
					end = nonTerList.find(' ', start);
				}
				//下面将改行中的最后一个Token项加入到终结符表中
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
	}//以上完成了对定义段的扫描

	producer ap;
	ap.left = START;
	producerTable.push_back(ap);//将扩展文法开始产生式加入到产生式集合中
	producerPreTable.push_back(0);

	state = BEGIN;
	char buf[BUFSIZ];//存储每个规则产生式的缓冲区
	int pos;//读取扫描规则产生式的读头
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
		if (c == '\t' || c == '\n' || c == ' ') continue;//跳过回车、换行以及空格
		pos = 0;//将读头移至串首,准备解析新的规则产生式
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
		buf[pos] = c;//读入最后一个';'
		buf[++pos] = '\0';//输入串尾以便转换成string类型
		string produce(buf);
		if (!analysProducer(produce)) {
			cerr << "There is an error in regular phase!" << endl;
			exit(1);
		}//解析并存储产生式
	}//以上完成了规则段的扫描

	producerTable[0].right.push_back(producerTable[1].left);//完成括展文法的第一个产生式
	pair<string, int> tp;
	tp.first = "$";//定义结束符$
	tp.second = NONTERMINAL - 1;
	tsymTable.insert(tp);
	//以上完成扩展文法的修正，便于后续生成LR1项集族

	genHashProducer();
	createPDA();//创建LR1项集族

	LR2LALR();

	printresult(LALR);
	createParseTable();
	genSemantprogram();
	writeTerminalTable();
	writeProducers();//生成产生式文件
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
	/*定义两个读头，用于拆分提取产生式*/
	int pos = 0;
	int tpos = 0;

	int priority = 0;//用于表示产生式的优先级

	producer tmp;//用于存储产生式的临时变量

	char c = product[pos];
	while (c != ' ' && c != '\t' && c != '\n' && c != '\r') {
		tpos++;
		c = product[tpos];
	}
	string left = product.substr(pos, tpos - pos);//读取产生式左部

	if (tsymTable.count(left)) {
		cout << "NonTerminatedSym define error!" << endl;
		return false;
	}//产生式左端不能出现终结符

	if (!ntsymTable.count(left)) {
		pair<string, int> ntp;
		ntp.first = left;
		ntp.second = NONTERMINAL + ntsymTable.size();
		ntsymTable.insert(ntp);
	}//若产生式左部为新的非终结符，则将其存入非终结符表中

	pos = tpos;
	while (c == ' ' || c == '\n' || c == '\t' || c == '\r') {
		pos++;
		c = product[pos];
	}//跳过无关字符，准备读取产生式右部

	if (c != ':') {
		cout << "Producer formation Error!" << endl;
		return false;
	}//产生式左右部间以'：'为分割

	tmp.left = ntsymTable[left];//输入产生式左部
	while (1) {
		pos++;
		c = product[pos];
		tmp.right.clear();//初始化，清空产生式右部
		priority = 0;
		while (c == ' ' || c == '\n' || c == '\t' || c == '\r') {
			pos++;
			c = product[pos];
		}//跳过无关字符

		string action;//yacc语义动作
		int lastTsym = 0;
		while (c != '|' && c != ';') {//未读到下一个产生式或规则结尾
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
			bool opeFlag = false;//标志变量，为true时表示读到了符号，需要进行终结符的处理
			if (c == '\'') opeFlag = true;//表示读到了操作符
			while (c != ' ' && c != '\n' && c != '\t' && c != '\r') {
				tpos++;
				c = product[tpos];
			}
			string str;
			if (opeFlag) {
				str = product.substr(pos + 1, tpos - pos - 2);//获取操作符
				if (!tsymTable.count(str)) {
					pair<string, int> tp;
					tp.first = str;
					tp.second = TERMINAL + tsymTable.size();
					tsymTable.insert(tp);
				}//将该操作符编号加入到终结符表
				tmp.right.push_back(tsymTable[str]);
				lastTsym = tsymTable[str];
			}
			else {
				str = product.substr(pos, tpos - pos);
				//如果str即不在终结符表又不在非终结符表，则判定为新的非终结符，进行相应处理
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
	}//该扫描算法的缺陷在于不能扫描空串产生式
}

void genHashProducer() {
	pair<int, vector<int> > tmp;
	for (int i = 0; i < producerTable.size(); i++) {
		hpSet[producerTable[i].left].push_back(i);
	}
}

void createPDA() {
	item start;//初始item项，用于生成初始项集I0
	start.producerTerm = 0;
	start.dotpos = 0;
	start.predict.insert(tsymTable["$"]);

	//auto indexCount = 0;
	ItemSet I0;//初始项集I0
	I0.iSet.push_back(start);
	closure(I0);//求初始项集的闭包

	queue<ItemSet> q;//利用广度遍历产生所有项集族
	LR1.itemSets.push_back(I0);
	q.push(I0);
	auto index = 0;//用来记录当前处理的项集的索引
	//int srcIndex = 1;//用来记录LR1.iSet中已经求完闭包的项集的索引
	auto desItemIndex = 1;//用来记录LR1.iSet中的最新生成的项集的索引
	while (!q.empty()) {
		ItemSet is = q.front();//取出q中的项集，用于生成新的项集
		q.pop();
		set<int> edgeSet;//用来记录可以从该项集中引出的边
		vector<ItemSet> tmpPDA;//由于新生成的项集可能与LR1中已有的项集重复，故在tmpPDA上先进行项集的拓展
		int tmpIndex = 0;
		map<int, int> edges;//用来记录从一个项集生成的所有项集的临时集合，该集合需要后续判定是否有与LR1中已有项集重复的项
							//下面找出项集is中的全部edge
		for (size_t i = 0; i < is.iSet.size(); i++) {
			int edge = is.iSet[i].getCurSym();
			if (edge == -1) continue;
			else if (!edgeSet.count(edge)) {
				edgeSet.insert(edge);
				edges.insert(make_pair(edge, tmpIndex));
				tmpIndex++;
				ItemSet newIS;
				tmpPDA.push_back(newIS);//为下一个可能项集申请空间
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
				}//对项集is中的每个不在可规约状态的item项进行move操作,并将is中所有可以移入的项加到对应移入边的集合中
			}
			for (auto k = edges.begin(); k != edges.end(); k++) {
				closure(tmpPDA[k->second]);//求新生成项集的闭包
				int des = getLR1Item(k->first, tmpPDA[k->second]);//判断新生成的项集是否已存在于LR1中，若已存在要对临时的项集DFA做修正
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
	queue<item> q;//队列q 用于广度遍历src中的项以生成闭包集
				  //将src中的Item项依次放入队列中
	for (size_t i = 0; i < src.iSet.size(); i++) q.push(src.iSet[i]);
	//下面开始广度遍历队列中的元素
	while (!q.empty()) {
		item it = q.front();
		q.pop();
		int curSym = it.getCurSym();//获取产生式中dotpos右侧相邻的字符
									//如果dotpos已达产生式尾部,则说明可规约,记录将该可规约项
		if (curSym == -1) { src.rSet.insert(it); }
		//如果curSym是非终结符
		if (NONTERMINAL <= curSym && curSym <= START) {
			vector<int> *ps = &(hpSet.at(curSym));//获得所有以非终结符curSym为产生式左式的产生式集合
			int nextSym = it.getNextSym();
			for (size_t i = 0; i < ps->size(); i++) {
				item tmp;
				tmp.producerTerm = ps->at(i);
				tmp.dotpos = 0;
				//判断项tmp是否已在项集src中，如果不在则创建在src中加入项tmp,并求tmp的预测符集，
				//否则直接将求的预测符集直接加入到已有项的predict中
				item *tmp2 = src.isInSet(tmp);
				if (tmp2 == NULL) {
					if (nextSym == -1) {
						tmp.predict = it.predict;
					}//tmp的predict继承自it的predict
					else if (TERMINAL <= nextSym && nextSym < NONTERMINAL) {
						tmp.predict.insert(nextSym);
					}//如果nextSym是终结符,则将该终结符加到tmp的predict中
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
					}//如果nextSym是非终结符,则求First(nextSym),并将该非终结符集中的项全加入到tmp的predict中
					q.push(tmp);
					src.iSet.push_back(tmp);//将tmp加入项集src
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
	set<int> desItemSet;//目标项集的候选项集
						//遍历LR1中已有项集的DFA,先找出所有经边edge可到达的项集
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
	//输出测试
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