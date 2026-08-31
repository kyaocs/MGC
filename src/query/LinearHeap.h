#ifndef _LINEAR_HEAP_H_
#define _LINEAR_HEAP_H_

#include "Utility.h"

class ListLinearHeap {
private:
	ui n;
	ui key_cap;

	ui min_key;
	ui max_key;

	ui *key_s;

	ui *head_s;

	ui *pre_s;
	ui *next_s;

public:
	ListLinearHeap(ui _n, ui _key_cap) {
		n = _n;
		key_cap = _key_cap;

		min_key = max_key = key_cap;

		head_s = key_s = pre_s = next_s = nullptr;
	}

	~ListLinearHeap() {
		if(head_s != nullptr) {
			delete[] head_s;
			head_s = nullptr;
		}
		if(pre_s != nullptr) {
			delete[] pre_s;
			pre_s = nullptr;
		}
		if(next_s != nullptr) {
			delete[] next_s;
			next_s = nullptr;
		}
		if(key_s != nullptr) {
			delete[] key_s;
			key_s = nullptr;
		}
	}

	void init(ui _n, ui _key_cap, ui *_id_s, ui *_key_s) {
		if(key_s == nullptr) key_s = new ui[n];
		if(pre_s == nullptr) pre_s = new ui[n];
		if(next_s == nullptr) next_s = new ui[n];
		if(head_s == nullptr) head_s = new ui[key_cap+1];


		min_key = max_key = _key_cap;
		for(ui i = 0;i <= _key_cap;i ++) head_s[i] = n;

		for(ui i = 0;i < _n;i ++) {
			ui id = _id_s[i];
			ui key = _key_s[id];


			key_s[id] = key; pre_s[id] = n; next_s[id] = head_s[key];
			if(head_s[key] != n) pre_s[head_s[key]] = id;
			head_s[key] = id;

			if(key < min_key) min_key = key;
		}
	}

	ui get_key(ui id) { return key_s[id]; }

	void get_ids(ui *vs, ui &vs_size) {
		for(ui i = min_key;i <= max_key;i ++) {
			for(ui id = head_s[i];id != n;id = next_s[id]) {
				vs[vs_size ++] = id;
			}
		}
	}

	bool get_min(ui &id, ui &key) {
		while(min_key <= max_key&&head_s[min_key] == n) ++ min_key;
		if(min_key > max_key) return false;

		id = head_s[min_key];
		key = min_key;


		return true;
	}

	bool pop_min(ui &id, ui &key) {
		while(min_key <= max_key&&head_s[min_key] == n) ++ min_key;
		if(min_key > max_key) return false;

		id = head_s[min_key];
		key = min_key;

		key_s[id] = key_cap+1;


		head_s[min_key] = next_s[id];
		if(head_s[min_key] != n) pre_s[head_s[min_key]] = n;
		return true;
	}

	ui decrement(ui id, ui dec) {

		if(key_s[id] > key_cap) return 0;

		if(pre_s[id] == n) {

			head_s[key_s[id]] = next_s[id];
			if(next_s[id] != n) pre_s[next_s[id]] = n;
		}
		else {
			ui pid = pre_s[id];
			next_s[pid] = next_s[id];
			if(next_s[id] != n) pre_s[next_s[id]] = pid;
		}

		ui &key = key_s[id];
		key -= dec; pre_s[id] = n; next_s[id] = head_s[key];
		if(head_s[key] != n) pre_s[head_s[key]] = id;
		head_s[key] = id;

		if(key < min_key) min_key = key;
		return key;
	}
};

#endif
