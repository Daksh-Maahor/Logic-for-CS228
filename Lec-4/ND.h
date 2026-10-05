#pragma once
#include "common.h"
#include "prop.h"

vector<vector<string>> elimination(vector<prop>& premises, prop conclusion, bool& valid);
vector<vector<string>> ND(vector<prop> premises, prop conclusion, bool& valid);