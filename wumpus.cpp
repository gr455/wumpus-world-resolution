#include <bits/stdc++.h>

using namespace std;

int randint(int rmax) {
	return rand() / (RAND_MAX / rmax);
}

// Each token literal in prop logic
// ex [0, 0]W, [0, 1]¬W
class Token {
public:
	bool negation;
	/**
	 * tokenChar
	 * S -> Safe
	 * B -> Breeze
	 * R -> Stink
	 * W -> Wumpus
	 * P -> Pit
	 * U -> Unknown // only used in states matrix
	 * T -> Traversable (S/B/R) // only used in states matrix
	 * */
	char tokenChar;
	int x;
	int y;

	Token(bool neg, char tokenChar, int x, int y)
	: negation(neg), tokenChar(tokenChar), x(x), y(y)
	{}

	string str_() {
		return "[" + to_string(x) + "," + to_string(y) + "]" + ((string)"(" + (negation ? "¬" : "") + tokenChar + ")" );
	}

	// Checks if current token is equivalent to t2
	bool match(Token t2) {
		return this->negation == t2.negation && this->tokenChar == t2.tokenChar && this->x == t2.x && this->y == t2.y;
	}

	// Checks if current token is the negation of t2
	bool isNegation(Token t2) {
		return this->negation == !t2.negation && this->tokenChar == t2.tokenChar && this->x == t2.x && this->y == t2.y;
	}
};

// A single disjunction term in CNF
// ex [0, 0]W ∨ [0, 1]¬W
class DisjunctiveLiteral {
public:
	vector<Token> tokenArray;

	string str_() {
		string s = "";
		for (auto tok: this->tokenArray) {
			s += tok.str_();
			s += "∨";
		}

		if (s.length() > 0) s.pop_back();
		return s;
	}

	// Checks if current DJ literal is equivalent to disj
	bool match(DisjunctiveLiteral disj) {
		vector<Token> thisTokenArray = this->tokenArray;
		vector<Token> thatTokenArray = disj.tokenArray;
		// cout << "before " << thisTokenArray.size() << " " << thatTokenArray.size() << endl;
		if (thisTokenArray.size() != thatTokenArray.size()) return false;

		int i = 0;
		while (i < thisTokenArray.size()) {
			int j = 0;
			while (j < thatTokenArray.size()) {
				if (thisTokenArray[i].match(thatTokenArray[j])) {
					thisTokenArray.erase(thisTokenArray.begin() + i);
					thatTokenArray.erase(thatTokenArray.begin() + j);

					i = 0; j = 0;
					continue;
				} 

				j++;
			}

			i++;
		}

		// cout << "after " << thisTokenArray[0].str_() << " " << thatTokenArray[0].str_() << endl;

		return thisTokenArray.size() == 0;
	}
};

class Knowledge {
public:
	vector<DisjunctiveLiteral> conjunctionArray;
	vector<vector<char>> states; // internal representation of the world
	bool arrowUsed;
	int n;

	Knowledge(int n) {
		this->arrowUsed = false;
		this->n = n;
		this->states = vector<vector<char>>(this->n, vector<char>(this->n, 'U'));
		// Starting square is safe
		Token init = Token(false, 'S', 0, 0);
		DisjunctiveLiteral initD = DisjunctiveLiteral();
		initD.tokenArray.push_back(init);

		this->conjunctionArray.push_back(initD);

	}

	string str_() {
		string s = "";
		for (auto dis: this->conjunctionArray) {
			s += "(";
			s += dis.str_();
			s += ")";
			s += "∧";
		}

		if (s.length() > 0) s.pop_back();
		return s;
	}

	// Add safe state: Adds to propositional logic and states matrix. Rejects other states
	// Sets surrounding states safe
	void addSafeState(int x, int y) {
		// This state is safe
		Token thisStateIsSafe = Token(false, 'S', x, y);
		DisjunctiveLiteral thisStateD = DisjunctiveLiteral();
		thisStateD.tokenArray.push_back(thisStateIsSafe);
		this->conjunctionArray.push_back(thisStateD);
		this->rejectOtherStates(x, y, 'S');
		this->states[x][y] = 'S';

		// Its surrounding states are safe
		if (x + 1 < n) {
			this->addWalkableState(x + 1, y);
		}
		if (x - 1 >= 0) {
			this->addWalkableState(x - 1, y);
		}
		if (y + 1 < n) {
			this->addWalkableState(x, y + 1);
		}
		if (y - 1 >= 0) {
			this->addWalkableState(x, y - 1);
		}
	}

	// Add breeze state: Adds to propositional logic and states matrix. Rejects other states
	// Adds propositional logic for pit in surrounding states
	void addBreezeState(int x, int y) {
		// This state has breeze
		Token thisStateIsSafe = Token(false, 'B', x, y);
		DisjunctiveLiteral thisStateD = DisjunctiveLiteral();
		thisStateD.tokenArray.push_back(thisStateIsSafe);
		this->conjunctionArray.push_back(thisStateD);
		this->rejectOtherStates(x, y, 'B');
		this->states[x][y] = 'B';

		// Atleast one of the surrounding states has a pit
		// Safe states are ignored. Since safety overrides pit and wumpus
		DisjunctiveLiteral surroundingStatesD = DisjunctiveLiteral();
		if (x + 1 < n && this->states[x + 1][y] != 'S') {
			Token thisStateHasPit = Token(false, 'P', x + 1, y);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}
		if (x - 1 >= 0 && this->states[x - 1][y] != 'S') {
			Token thisStateHasPit = Token(false, 'P', x - 1, y);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}
		if (y + 1 < n && this->states[x][y + 1] != 'S') {
			Token thisStateHasPit = Token(false, 'P', x, y + 1);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}
		if (y - 1 >= 0 && this->states[x][y - 1] != 'S') {
			Token thisStateHasPit = Token(false, 'P', x, y - 1);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}

		this->conjunctionArray.push_back(surroundingStatesD);

	}

	// Add stench state: Adds to propositional logic and states matrix. Rejects other states
	// Adds propositional logic for wumpus in surrounding states
	void addStenchState(int x, int y) {
		// This state has stench
		Token thisStateIsSafe = Token(false, 'R', x, y);
		DisjunctiveLiteral thisStateD = DisjunctiveLiteral();
		thisStateD.tokenArray.push_back(thisStateIsSafe);
		this->conjunctionArray.push_back(thisStateD);
		this->rejectOtherStates(x, y, 'R');
		this->states[x][y] = 'R';

		// Atleast one of the surrounding states has a wumpus
		// Safe states are ignored. Since safety overrides pit and wumpus
		DisjunctiveLiteral surroundingStatesD = DisjunctiveLiteral();
		if (x + 1 < n && this->states[x + 1][y] != 'S') {
			Token thisStateHasPit = Token(false, 'W', x + 1, y);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}
		if (x - 1 >= 0 && this->states[x - 1][y] != 'S') {
			Token thisStateHasPit = Token(false, 'W', x - 1, y);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}
		if (y + 1 < n && this->states[x][y + 1] != 'S') {
			Token thisStateHasPit = Token(false, 'W', x, y + 1);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}
		if (y - 1 >= 0 && this->states[x][y - 1] != 'S') {
			Token thisStateHasPit = Token(false, 'W', x, y - 1);
			surroundingStatesD.tokenArray.push_back(thisStateHasPit);
		}

		this->conjunctionArray.push_back(surroundingStatesD);

	}

	// Adds a S/B/R state to KB
	void addWalkableState(int x, int y) {
		Token thisStateIsSafe = Token(false, 'S', x, y);
		Token thisStateHasBreeze = Token(false, 'B', x, y);
		Token thisStateHasStench = Token(false, 'R', x, y);
		Token thisStateIsNotWumpus = Token(true, 'W', x, y);
		Token thisStateIsNotPit = Token(true, 'P', x, y);
		DisjunctiveLiteral thisStateD = DisjunctiveLiteral();
		thisStateD.tokenArray.push_back(thisStateIsSafe);
		thisStateD.tokenArray.push_back(thisStateHasBreeze);
		thisStateD.tokenArray.push_back(thisStateHasStench);


		DisjunctiveLiteral thisStateIsNotPitD = DisjunctiveLiteral();
		thisStateIsNotPitD.tokenArray.push_back(thisStateIsNotPit);

		DisjunctiveLiteral thisStateIsNotWumpusD = DisjunctiveLiteral();
		thisStateIsNotWumpusD.tokenArray.push_back(thisStateIsNotWumpus);

		this->conjunctionArray.push_back(thisStateD);
		this->conjunctionArray.push_back(thisStateIsNotPitD);
		this->conjunctionArray.push_back(thisStateIsNotWumpusD);

		if (this->states[x][y] == 'U') this->states[x][y] = 'T';
	}

	// Set all other states except exceptState as false for given cell
	void rejectOtherStates(int x, int y, char exceptState) {
		char possibleStates[] = {'W', 'P', 'S', 'R', 'B'};
		for (auto st: possibleStates) {
			if (st == exceptState) continue;
			Token thisStateIsNot = Token(true, st, x, y);
			DisjunctiveLiteral thisStateD = DisjunctiveLiteral();
			thisStateD.tokenArray.push_back(thisStateIsNot);
			this->conjunctionArray.push_back(thisStateD);
		}
	}

	// Run resolution on the entire KB. If any of the resolutions result in a single token
	// that token state is added to this->states.
	// This is where the magic happens
	void resolveKB() {
		int i = 0;
		while (i < this->conjunctionArray.size()) {
			int j = i + 1;
			while (j < this->conjunctionArray.size()) {
				// resolve
				DisjunctiveLiteral resolved = this->computeResolution(this->conjunctionArray[i], this->conjunctionArray[j]);
				// If resolution results in tautology (tokenarray.size == 0), cannot conclude anything
				if (resolved.tokenArray.size() == 0)   {
					j++;
					continue;
				}

				if (!this->disjLiteralExists(resolved)) this->conjunctionArray.push_back(resolved);
				// If resolution results in single literal, do state change.
				if (resolved.tokenArray.size() == 1) {
					// cout << resolved.str_() << endl;
					Token stateInference = resolved.tokenArray[0];
					if (!stateInference.negation) this->states[stateInference.x][stateInference.y] = stateInference.tokenChar;
				}

				j++;
			}

			i++;
		}
	}

	// Computes resolution of two given disjunctive literals. Returns empty DisjunctiveLiteral if
	// the resolution results in a tautology
	DisjunctiveLiteral computeResolution(DisjunctiveLiteral lit1, DisjunctiveLiteral lit2) {
		DisjunctiveLiteral resolved = DisjunctiveLiteral();
		for (int i = 0; i < lit1.tokenArray.size(); i++) {
			for(int j = 0; j < lit2.tokenArray.size(); j++) {
				if (lit1.tokenArray[i].isNegation(lit2.tokenArray[j])) {
					vector<Token> merged = lit1.tokenArray;
					merged.insert(merged.end(), lit2.tokenArray.begin(), lit2.tokenArray.end());
					merged.erase(merged.begin() + i);
					merged.erase(merged.begin() + i + j);

					this->simplifyDisjunction(merged);
					resolved.tokenArray = merged;
					// cout << "res: "<< resolved.str_() << endl; 

					return resolved;
				}
			}
		}

		return resolved;
	}

	// Removes duplicates and returns empty array if tautology (P V ~P)
	void simplifyDisjunction(vector<Token>& tokenArray) {
		int i = 0;
		while (i < tokenArray.size()) {
			int j = i + 1;

			while (j < tokenArray.size()) {

				// if matching token is found, then remove duplicate (P V P = P) 
				if (tokenArray[i].match(tokenArray[j])) {
					tokenArray.erase(tokenArray.begin() + j);
					j--;
				}

				// if negation, then just return empty array since tautology
				else if (tokenArray[i].isNegation(tokenArray[j])) {
					tokenArray.clear();
					return;
				}

				j++;
			}

			i++;
		}
	}

	// Checks if a certain disjunctive literal exists in KB
	bool disjLiteralExists(DisjunctiveLiteral disj) {
		for (auto lit: this->conjunctionArray) {
			if (lit.match(disj)) return true;
		}

		return false;
	}
};

// Returns the world n_width x n_width in size
vector<vector<char>> getenv(int n_width) {
	vector<vector<char>> env = vector<vector<char>>(n_width, vector<char>(n_width, 'S'));

	int block_x = 4;
	int block_y = n_width - 2; // randint(n_width - 1);

	env[block_x][block_y] = 'W';
	if (block_x + 1 < n_width) env[block_x + 1][block_y] = 'R';
	if (block_x - 1 >= 0) env[block_x - 1][block_y] = 'R';
	if (block_y + 1 < n_width) env[block_x][block_y + 1] = 'R';
	if (block_y - 1 >= 0) env[block_x][block_y - 1] = 'R';

	block_x = 3;
	block_y = n_width - 4;

	env[block_x][block_y] = 'P';
	if (block_x + 1 < n_width) env[block_x + 1][block_y] = 'B';
	if (block_x - 1 >= 0) env[block_x - 1][block_y] = 'B';
	if (block_y + 1 < n_width) env[block_x][block_y + 1] = 'B';
	if (block_y - 1 >= 0) env[block_x][block_y - 1] = 'B';


	return env;
}

void printenv(vector<vector<char>>& env) {
	for (auto e: env) {
		for (auto a: e) cout << a << " ";
		cout << endl;
	}
}

// DFS. Agent visits any walkable node that it can
// At each visit, percept is taken and added to the KB and KB is resolved
int dfs(vector<vector<char>>& env, Knowledge * knowledge, bool visited[][20], int this_x, int this_y, int fin_x, int fin_y, int n) {
	if (this_x == fin_x && this_y == fin_y) {
		knowledge->addSafeState(this_x, this_y);
		return 1;
	}
	// Perceive this state
	char thisState = env[this_x][this_y];
	// Add this to KB
	if (thisState == 'S') knowledge->addSafeState(this_x, this_y);
	else if (thisState == 'B') knowledge->addBreezeState(this_x, this_y);
	else if (thisState == 'R') knowledge->addStenchState(this_x, this_y);

	// cout << "Agent at: (" << this_x << ", " << this_y << ")" << endl; 
	// cout << "==== STATES ====" << endl;
	// printenv(knowledge->states);
	// cout << endl;
	// printenv(env);
	// cout << "================" << endl;

	// Run resolution on entire KB
	knowledge->resolveKB();
	visited[this_x][this_y] = true;
	// Print current state knowledge
	cout << "Agent at: (" << this_x << ", " << this_y << ")" << endl; 
	cout << "==== STATES ====" << endl;
	printenv(knowledge->states);
	cout << "================" << endl;

	// Move to a new SBR state in either of the 4 directions
	if (this_x + 1 < n && !visited[this_x + 1][this_y]
		&& (knowledge->states[this_x + 1][this_y] == 'S' ||
		knowledge->states[this_x + 1][this_y] == 'B' ||
		knowledge->states[this_x + 1][this_y] == 'R' ||
		knowledge->states[this_x + 1][this_y] == 'T')) {
		int done = dfs(env, knowledge, visited, this_x + 1, this_y, fin_x, fin_y, n);
		if (done == 1) return done;
	}

	if (this_x - 1 >= 0 && !visited[this_x - 1][this_y]
		&& (knowledge->states[this_x - 1][this_y] == 'S' ||
		knowledge->states[this_x - 1][this_y] == 'B' ||
		knowledge->states[this_x - 1][this_y] == 'R' ||
		knowledge->states[this_x - 1][this_y] == 'T')) {
		int done = dfs(env, knowledge, visited, this_x - 1, this_y, fin_x, fin_y, n);
		if (done == 1) return done;
	}

	if (this_y + 1 < n && !visited[this_x][this_y + 1]
		&& (knowledge->states[this_x][this_y + 1] == 'S' ||
		knowledge->states[this_x][this_y + 1] == 'B' ||
		knowledge->states[this_x][this_y + 1] == 'R' ||
		knowledge->states[this_x][this_y + 1] == 'T')) {
		int done = dfs(env, knowledge, visited, this_x, this_y + 1, fin_x, fin_y, n);
		if (done == 1) return done;
	}

	if (this_y - 1 >= 0 && !visited[this_x][this_y - 1] && 
		(knowledge->states[this_x][this_y - 1] == 'S' ||
		knowledge->states[this_x][this_y - 1] == 'B' ||
		knowledge->states[this_x][this_y - 1] == 'R' ||
		knowledge->states[this_x][this_y - 1] == 'T')) {
		int done = dfs(env, knowledge, visited, this_x, this_y - 1, fin_x, fin_y, n);
		if (done == 1) return done;
	}

	return 0;
}

int main() {
	srand(0);

	int n;
	int start_x, start_y, fin_x, fin_y;

	string legend = "* S -> Safe\n"
	 "* B -> Breeze\n"
	 "* R -> Stench\n"
	 "* W -> Wumpus\n"
	 "* P -> Pit\n"
	 "* U -> Unknown\n"
	 "* T -> Traversable (S/B/R)";

	cin >> n >> start_x >> start_y >> fin_x >> fin_y;

	vector<vector<char>> env = getenv(n);
	Knowledge * knowledge = new Knowledge(n);
	// printenv(env);
	
	for (int times = 0; times < n * n; times++) {
		bool visited[20][20] = { false };
		int done = dfs(env, knowledge, visited, start_x, start_y, fin_x, fin_y, n);
		if (done == 1) {
			cout << "DONE!" << endl << endl;
			cout << "Legend:" << endl;
			cout << legend << endl;
			cout << "World:" << endl;
			printenv(env);
			return 0;
		}
	}

	cout << "There is no solution to this world" << endl;

	return 0;
}