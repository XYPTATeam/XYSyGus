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


def contain_func(expr, func_name):
    if isinstance(expr, list):
        for i in expr:
            if contain_func(i, func_name):
                return True
    else:
        if expr == func_name:
            return True
    return False


class Hint:
    def __init__(self):
        self.parent_list = []
        self.func_list = []
        self.st = None

        self.hint_list = []
        self.hint_cond_list = []  # type: tuple(cond, expr)
        self.hint_compare = []  # type: tuple(op, expr)
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

    def build_hint_from_constraints(self, hinted_constraints, func_list, st):
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

                if other_expr is not None and not contain_func(other_expr, self.func_list[0]):
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
                        else:
                            self.hint_list.append(other_expr)
            elif op in compare_op:
                op = l[0]
                other_expr = None
                if has_func == 1:
                    other_expr = l[2]
                elif has_func == 2:
                    other_expr = l[1]
                    # flap op
                    if op.startswith('<'):
                        op = op.replace('<', '>')
                    else:
                        op = op.replace('>', '<')
                if other_expr is not None:
                    other_expr = format_expr(other_expr)
                    self.hint_compare.append((op, other_expr))

        if not may_be_func:
            return False

        is_const = True
        arg_list = []
        for i in range(1, target_len):
            expr = l[i]
            expr = format_expr(expr)
            if expr.isdigit():
                arg_list.append(expr)
            else:
                is_const = False
                break

        if is_const:
            parent = self.get_form_parent_list(l)
            if parent is not None:
                parent_op = parent[0]
                if parent_op == '=':
                    other_expr = None
                    if parent[1] == l:
                        other_expr = parent[2]
                    elif parent[2] == l:
                        other_expr = parent[1]
                    if other_expr is not None:
                        other_expr = format_expr(other_expr)
                        self.hint_const.append((arg_list, other_expr))

        for i in range(target_len):
            if l[i] != self.func_list[i]:
                return False

        return True

    def gen_stmt_from_cond(self, early_stop=True):
        new_list = []
        cur_list = new_list

        len_cond_list = len(self.hint_cond_list)
        if early_stop:
            stop = len_cond_list - 1
        else:
            stop = len_cond_list
        if len_cond_list > 0:
            for idx in range(stop):
                t_cond = self.hint_cond_list[idx]
                cond = t_cond[0]
                expr = t_cond[1]
                cur_list.append('ite')
                cur_list.append(cond)
                cur_list.append(expr)
                next_list = []
                cur_list.append(next_list)
                cur_list = next_list

        return new_list, cur_list

    def gen_stmt_from_compare(self, early_stop=True):
        new_list = []
        cur_list = new_list

        len_compare = len(self.hint_compare)
        if len_compare > 0:
            if early_stop:
                stop = len_compare - 1
            else:
                stop = len_compare
            for idx in range(stop):
                t_cmp = self.hint_compare[idx]
                cond = []
                expr = t_cmp[1]

                cur_cond = cond
                cond_cnt = 0
                for cidx in range(len_compare):
                    if cidx == idx:
                        continue
                    ct_cmp = self.hint_compare[cidx]

                    if cond_cnt != stop - 1:
                        new_cond = [ct_cmp[0], expr, ct_cmp[1]]
                        cur_cond.append('and')
                        cur_cond.append(new_cond)
                        next_cond = []
                        cur_cond.append(next_cond)
                        cur_cond = next_cond
                    else:
                        cur_cond.append(ct_cmp[0])
                        cur_cond.append(expr)
                        cur_cond.append(ct_cmp[1])
                    cond_cnt += 1

                cur_list.append('ite')
                cur_list.append(cond)
                cur_list.append(expr)
                next_list = []
                cur_list.append(next_list)
                cur_list = next_list

        return new_list, cur_list

    def gen_stmt_from_const(self, early_stop=True):
        new_list = []
        cur_list = new_list

        len_const = len(self.hint_const)
        if len_const > 0:
            if early_stop:
                stop = len_const - 1
            else:
                stop = len_const

            for idx in range(stop):
                t_const = self.hint_const[idx]
                arg_list = t_const[0]
                len_arg_list = len(arg_list)
                expr = t_const[1]

                cond = []
                cur_cond = cond
                cond_cnt = 0
                for cidx in range(len_arg_list):
                    if cond_cnt != len_arg_list - 1:
                        new_cond = ['=', self.func_list[cidx + 1], arg_list[cidx]]
                        cur_cond.append('and')
                        cur_cond.append(new_cond)
                        next_cond = []
                        cur_cond.append(next_cond)
                        cur_cond = next_cond
                    else:
                        cur_cond.append('=')
                        cur_cond.append(self.func_list[cidx + 1])
                        cur_cond.append(arg_list[cidx])
                    cond_cnt += 1

                cur_list.append('ite')
                cur_list.append(cond)
                cur_list.append(expr)
                next_list = []
                cur_list.append(next_list)
                cur_list = next_list

        return new_list, cur_list

    def gen_stmt_from_hint(self):
        ret_list = None
        ret_cur_list = None

        len_cond = len(self.hint_cond_list)
        len_compare = len(self.hint_compare)
        len_const = len(self.hint_const)
        len_list = len(self.hint_list)
        if len_cond > 0:
            if len_compare > 0 or len_const > 0:
                new_list, cur_list = self.gen_stmt_from_cond(early_stop=False)
            else:
                new_list, cur_list = self.gen_stmt_from_cond(early_stop=True)
                t_cond = self.hint_cond_list[-1]
                cur_list.append(t_cond[1])

            ret_cur_list = cur_list
            if ret_list is None:
                ret_list = new_list

        if len_compare > 0:

            if len_cond > 0:
                new_list, cur_list = self.gen_stmt_from_compare(early_stop=False)
            else:
                new_list, cur_list = self.gen_stmt_from_compare(early_stop=True)
                t_cmp = self.hint_compare[-1]
                cur_list.append(t_cmp[1])

            if ret_cur_list is not None:
                ret_cur_list.append(new_list[:])
            ret_cur_list = cur_list
            if ret_list is None:
                ret_list = new_list

        if len_const > 0:
            if len_list > 0:
                new_list, cur_list = self.gen_stmt_from_const(early_stop=False)
                ret_cur_list = cur_list
            else:
                new_list, cur_list = self.gen_stmt_from_const(early_stop=True)
                t_const = self.hint_const[-1]
                cur_list.append(t_const[1])

            if ret_cur_list is not None:
                ret_cur_list.append(new_list[:])
            ret_cur_list = cur_list
            if ret_list is None:
                ret_list = new_list

        if len_list > 0 and len_cond == 0 and len_compare == 0 and len_cond == 0:
            t_list = self.hint_list[-1]
            new_list = [t_list]

            if ret_cur_list is not None:
                ret_cur_list.append(new_list[:])
            if ret_list is None:
                ret_list = new_list

        self.hint_cond_list = []
        self.hint_compare = []
        self.hint_const = []

        return ret_list
