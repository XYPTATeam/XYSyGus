compare_op = ['<', '<=', '>=', '>']
arithmetic_op = ['+', '-', '*', '/', 'mod']
logic_op = ['and', 'or', 'not', 'imply']


def sort_productions(productions, types):
    for start_name in productions:
        production_list = productions[start_name]
        production_type = types[start_name]

        if production_type == 'Int':
            new_list = []
            pending_list = []
            for expr in production_list:
                if isinstance(expr, list):
                    pending_list.append(expr)
                else:
                    new_list.append(expr)

            for expr in pending_list:
                new_list.append(expr)
            productions[start_name] = new_list

        elif production_type == 'Bool':
            new_list = []
            pending_list = []
            for expr in production_list:
                if isinstance(expr, list):
                    op = expr[0]
                    if op in logic_op:
                        pending_list.append(expr)
                    else:
                        new_list.append(expr)
                else:
                    new_list.append(expr)

            for expr in pending_list:
                new_list.append(expr)
            productions[start_name] = new_list


def format_expr(expr):
    if isinstance(expr, tuple):
        expr = str(expr[1])
    return expr


def contain_func(l, func_name):
    for i in l:
        if isinstance(i, list):
            if contain_func(i, func_name):
                return True
        else:
            if i == func_name:
                return True
    return False


class Hint:
    def __init__(self):
        self.parent_list = []
        self.func_list = []
        self.st = None

        self.hint_list = []
        self.hint_cond_list = []  # type: tuple(cond, expr)
        self.hint_compare = []
        self.hint_const = []

    def build_parent_list(self, l):
        for i in l:
            if isinstance(i, list):
                self.parent_list.append((i, l))
                self.build_parent_list(i)

    def get_form_parent_list(self, l):
        for t in self.parent_list:
            if t[0] == l:
                return t[1]
        return None

    def translate_expr(self, expr):
        if isinstance(expr, str):
            if expr not in self.st.TransTable:
                return None

            ret_str = self.st.TransTable[expr]
            return ret_str

        elif isinstance(expr, list):
            for idx in range(len(expr)):
                e = expr[idx]
                ret_str = self.translate_expr(e)
                if ret_str is not None:
                    expr[idx] = ret_str

        return None

    def hint_from_constraints(self, hinted_constraints, func_list, st):
        self.func_list = func_list
        self.st = st

        # check function list
        for constraint in hinted_constraints:
            self.translate_expr(constraint)
            if isinstance(constraint, list):
                self.check_i(constraint)

    def check_i(self, l):
        target_len = len(self.func_list)
        l_len = len(l)
        may_be_func = True
        has_func = -1
        for i in range(l_len):
            context = l[i]
            if isinstance(context, list):
                may_be_func = False
                result = self.check_i(context)
                if result:
                    has_func = i

        if has_func > 0:
            op = l[0]
            if op == '=':
                other_expr = None
                if has_func == 1:
                    other_expr = l[2]
                elif has_func == 2:
                    other_expr = l[1]
                other_expr = format_expr(other_expr)

                if other_expr is not None:
                    parent = self.get_form_parent_list(l)
                    if parent is None:
                        self.hint_list.append(other_expr)
                    else:
                        parent_op = parent[0]
                        if parent_op == 'and' or parent_op == '=>':
                            cond_expr = None
                            if parent[1] == l:
                                cond_expr = parent[2]
                            elif parent[2] == l:
                                cond_expr = parent[1]
                            if cond_expr is not None:
                                self.hint_cond_list.append((cond_expr, other_expr))
                        elif parent_op == 'or':
                            self.hint_list.append(other_expr)
            elif op in compare_op:
                pass
            else:
                pass

        if not may_be_func:
            return False

        for i in range(target_len):
            if l[i] != self.func_list[i]:
                return False
        return True
