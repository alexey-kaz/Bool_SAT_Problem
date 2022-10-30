import copy
import pathlib


def read_file(filename):
    clauses = set()
    variables = set()
    with open(filename) as f:
        lines = [x.strip().split() for x in f.readlines() if (not (x.startswith('c')) and x != '\n')]
    for line in lines[1:]:
        cl = frozenset(map(int, line[:-1]))
        clauses.add(cl)
        variables.update(map(abs, cl))
    return [list(x) for x in clauses], len(variables)


def resolve(ante, lis, x):
    merge = lis + ante
    merge.remove(x)
    merge.remove(-1 * x)
    res = []
    for i in merge:
        if i not in res:
            res.append(i)
    return res


class CDCL:
    def __init__(self, filename):
        self.filename = filename
        self.cfn, self.num_var = read_file(filename)
        self.v = []
        self.antecedent_clause = {}
        self.var = []
        self.total = [x + 1 for x in range(self.num_var)]
        self.decision_level = 0
        self.implications_count = 0
        self.conflict_count = 0
        self.literal_freq = [0] * self.num_var
        self.literal_polarisation = [0] * self.num_var
        self.orig_lit_freq = None

    def solve(self):
        for item in self.cfn:
            self.add_unary(item)
        self.pre_del()
        if not self.cfn:
            return True, {}
        for clause in self.cfn:
            self.update_freq_polar(clause)
        self.orig_lit_freq = copy.deepcopy(self.literal_freq)
        if self.detect_conflict():
            return False, {}
        while self.var != self.total:
            self.preprocess()
            while self.detect_conflict():
                self.conflict_count += 1
                backtrack_lvl, learnt_clause = self.analise_conflict()
                if learnt_clause not in self.cfn:
                    self.cfn.append(learnt_clause)
                if backtrack_lvl < 0:
                    return False, {}
                else:
                    self.decision_level = self.backtrack(backtrack_lvl)
                    self.add_unary(learnt_clause)
                    self.update_freq_polar(learnt_clause)
            self.update_variables()
        return True, self.antecedent_clause

    def add_unary(self, item):
        if len(item) == 1:
            mult = -1 if item[0] < 0 else 1
            x = mult * int(item[0])
            self.v.append([x, int(item[0] >= 0), 0])
            self.antecedent_clause[mult * x] = -1

    def pre_del(self):
        rem = []
        for i in self.v:
            z = int(i[0])
            if i[1] == 0:
                z = -1 * z
            for lis in self.cfn:
                if z in lis and len(lis) != 1 and lis not in rem:
                    rem.append(lis)
        for i in rem:
            self.cfn.remove(i)

    def update_freq_polar(self, clause):
        for literal in clause:
            mult = 1 if literal > 0 else -1
            self.literal_freq[mult * literal - 1] = self.literal_freq[mult * literal - 1] + 1
            self.literal_polarisation[mult * literal - 1] = self.literal_polarisation[mult * literal - 1] + mult * 1

    def detect_conflict(self):
        eq_copy = copy.deepcopy(self.cfn)
        for i in self.v:
            z = (-1) ** (i[1] == 1) * int(i[0])
            index = -1
            for lis in eq_copy:
                index += 1
                if -1 * z in lis:
                    lis = [-1 * z]
                if z in lis:
                    lis.remove(z)
                self.is_var(index, lis, z)
                if len(lis) == 0:  # conflict
                    self.antecedent_clause[0] = index
                    return True
        return False

    def is_var(self, index, lis, z):
        if len(lis) == 1:
            x = lis[0]
            y = self.find_literal(x)
            if y and lis[0] != -1 * z:
                self.implications_count += 1
                self.antecedent_clause[x] = index

    def find_literal(self, x):
        z = (-1) ** (int(x < 0)) * x
        for j in self.v:
            if j[0] == z:
                if (x < 0 and j[1] == 0) or (x > 0 and j[1] == 1):
                    return False
        self.v.append([z, int(x >= 0), self.decision_level])
        return True

    def decide(self):
        for i in self.var:
            if self.literal_freq[i - 1] != -1:
                self.literal_freq[i - 1] = -1
        self.decay_freq()
        var = self.literal_freq.index(max(self.literal_freq))
        sign = int(self.literal_polarisation[var] > 0)
        return var + 1, sign

    def decay_freq(self):
        if self.conflict_count > 100:
            self.conflict_count = self.conflict_count % 100
            for i in range(self.num_var):
                self.orig_lit_freq[i] = self.orig_lit_freq[i] / 2
                if self.literal_freq[i] != -1:
                    self.literal_freq[i] = self.literal_freq[i] / 2

    def analise_conflict(self):
        antecedent_copy = copy.deepcopy(self.cfn[self.antecedent_clause[0]])
        conflict_lvl = self.find_conflict_lvl(antecedent_copy)
        if conflict_lvl == 0:
            return -1, []
        while True:
            count, resol = self.find_uip(antecedent_copy, conflict_lvl)
            if count == 1:
                break
            ante = self.cfn[self.antecedent_clause[-1 * resol]]
            antecedent_copy = resolve(ante, antecedent_copy, resol)
        assert_lvl = self.find_assert_lvl(antecedent_copy, conflict_lvl)
        return assert_lvl, antecedent_copy

    def find_conflict_lvl(self, antecedent_copy):
        conflict_lvl = 0
        for i in antecedent_copy:
            for j in self.v:
                if j[0] == abs(i) and conflict_lvl < j[2]:
                    conflict_lvl = j[2]
        return conflict_lvl

    def find_assert_lvl(self, antecedent_copy, conf_l):
        assert_lvl = 0
        for item in antecedent_copy:
            for i in self.v:
                if i[0] == abs(item) and conf_l > i[2] > assert_lvl:
                    assert_lvl = i[2]
        return assert_lvl

    def find_uip(self, antecedent_copy, conf_l):
        count, resol = 0, 0
        for i in antecedent_copy:
            for j in self.v:
                if j[0] == abs(i) and j[2] == conf_l:
                    count += 1
                    if self.antecedent_clause[-1 * i] != -1:
                        resol = i
        return count, resol

    def backtrack(self, b):
        rmv_lst = self.var_gr8_decision_lvl(b)
        self.remover(rmv_lst)
        return b

    def remover(self, rmv_lst):
        for j in rmv_lst:
            self.v.remove(j)
            self.literal_freq[j[0] - 1] = self.orig_lit_freq[j[0] - 1]
        del self.antecedent_clause[0]

    def var_gr8_decision_lvl(self, b):
        rmv_lst = []
        for i in self.v:
            x = i[0]
            if i[1] == 0:
                x = -1 * x
            if i[2] >= b:
                rmv_lst.append(i)
                if x in self.antecedent_clause.keys():
                    del self.antecedent_clause[x]
        return rmv_lst

    def update_variables(self):
        var = []
        for i in self.v:
            if i[0] not in var:
                var.append(i[0])
        self.var = sorted(var)

    def preprocess(self):
        self.decision_level += 1
        new_var, sign = self.decide()
        self.antecedent_clause[(-1) ** (int(sign == 0)) * new_var] = -1
        self.v.append([new_var, sign, self.decision_level])


if __name__ == "__main__":
    input_files = pathlib.Path('./tests')
    for file in sorted(input_files.iterdir()):
        print(file)
        output, dct = CDCL(file).solve()
        print(("UN" * (not output) + 'SAT'))
        if output:
            print({abs(i): int(i >= 0) for i in sorted(dct, key=abs)})
        print()
