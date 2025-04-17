import sys
import time
sys.path.append('./')
sys.path.append('../')
import murphi
import wiseParaVerifier.concretedF as concretedF
import wiseParaVerifier.invFinder as invFinder
from z3 import *
import itertools
import subprocess
import re
from collections import defaultdict
import shutil
from murphiparser import *
import copy
from collections import Counter
import client
import lark
import psutil

# 检查是否提供了参数 -p
def get_comdpara():
    protocol_param = None
    is_combpro = False
    if len(sys.argv) > 2:
        if sys.argv[1] == '-p':
            protocol_param = sys.argv[2]  # 获取 -p 后面的参数 (mesi)
            is_combpro = True
            print(f"To enable the promotion method, the captured protocol is: {protocol_param}\n")
        else:
            print("Parameter error, unrecognized.\n")
    elif len(sys.argv) > 1:
        protocol_param = sys.argv[1]
        print(f"To find the auxiliary invariant, the captured protocol is: {protocol_param}\n")
    else:
        print("The protocol path for authentication is not provided.\n")
    
    return protocol_param, is_combpro


def call_wiseParaverifier(protocol_path, protocol_name):
    
    wiseParaverifier_inv = dict()

    # protocol_name = protocol_path.split("/")[-1]
    # print(protocol_name)

    # smv_content = str(parse_file(protocol_path + ".m", smvSelect=True))
    # with open(protocol_path + "_node3.smv", "w") as f:
    #     f.write(str(smv_content))

    # using smv as checker
    smv_content = ""
    with open(protocol_path + ".smv", "r") as file:
        smv_content = file.read()

    try:
        client.calculate_protocol_reachability(protocol_name, smv_content)
    except ValueError:
        print("calculate_protocol_reachability failed. Please check if the Server is ready for communication.\n")


    try:
        for root, dirs, files in os.walk(os.path.dirname(protocol_path)):
            for file in files:
                if file.endswith(".smv"):
                    file_path = os.path.join(root, file)
                    with open(file_path, "r") as file:
                        smv_content = file.read()
                        client.set_bmc(os.path.splitext(os.path.basename(file_path))[0], smv_content)
    except ValueError:
        print("set bmc failed. Please check if the Server is ready for communication.\n")


    open(protocol_path + "_invs.txt", 'w').close()

    s_constructF = time.time()
    c = concretedF.GetSMTformula(parse_name=protocol_path)
    # c.getInvs()
    c.get_deadlock_free()

    e_constructF = time.time()
    t_constructF = e_constructF - s_constructF

    ori_inv = defaultdict(list)
    all_ori_invs = list()
    # print("c.inv_instance:", c.inv_instance)
    for key, value in c.inv_instance.items():
        all_ori_invs.append(value)
        ori_inv[key.split("_")[0]].append(value)
    # print("ori_inv: ", ori_inv)

    str_or_inv = copy.deepcopy(all_ori_invs[0])

    invFinder.defEnum(c)

    specific_var = murphi.specific_var
    ScalarSetType_vars = []
    BooleanType_vars = []

    for var, typ in specific_var.items():
        if isinstance(typ, murphi.ScalarSetType) or isinstance(typ, murphi.RngType):
            ScalarSetType_vars.append(var)
        elif isinstance(typ, murphi.BooleanType):
            BooleanType_vars.append(var)
        elif isinstance(typ, murphi.EnumType):
            if str(var) in murphi.specific_enum_var.keys():
                invFinder.EnumType_vars[str(var)] = murphi.specific_enum_var[str(var)]
                invFinder.EnumType_vars[str(var) + "'"] = murphi.specific_enum_var[str(var)]

    for var, typ in specific_var.items():
        if var in c.all_ins_vars.keys():
            invFinder.all_vars[var] = invFinder.setKey(c.all_ins_vars[var], "", isbool=isinstance(typ, murphi.BooleanType),
                                   isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                   isenum=isinstance(typ, murphi.EnumType))
            invFinder.all_vars[var + "'"] = invFinder.setKey(c.all_ins_vars[var], "'", isbool=isinstance(typ, murphi.BooleanType),
                                         isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                         isenum=isinstance(typ, murphi.EnumType))
            invFinder.all_ins_vars.append(var)
        elif "[_]" not in var:
            invFinder.all_vars[var] = invFinder.setKey(murphi.VarExpr(name=var,typ=specific_var[var]), "", isbool=isinstance(typ, murphi.BooleanType),
                                   isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                   isenum=isinstance(typ, murphi.EnumType))
            invFinder.all_vars[var + "'"] = invFinder.setKey(murphi.VarExpr(name=var,typ=specific_var[var]), "", isbool=isinstance(typ, murphi.BooleanType),
                                   isdigit=isinstance(typ, murphi.ScalarSetType) or isinstance(typ,murphi.RngType),
                                   isenum=isinstance(typ, murphi.EnumType))
            invFinder.all_ins_vars.append(var)
            

    for const_var, const_values_typ in murphi.specific_var.items():
        downRng = 0
        upRng = 0
        sub_const_map = dict()
        if isinstance(const_values_typ, murphi.ScalarSetType):
            downRng = 1
            upRng = 1 + murphi.const_map[const_values_typ.const_name]
            for i in range(downRng,upRng):
                
                # subtyp = murphi.VarType(name=(key for key, val in murphi.digitType_map.items() if val == value))
                sub_const_map[str(i)] = murphi.VarExpr(name=str(i),typ=const_values_typ)
            invFinder.const_pmurphi_map[str(const_var)] = sub_const_map
        elif isinstance(const_values_typ, murphi.RngType):
            if const_values_typ.downRng in murphi.const_map.keys():
                downRng = int(murphi.const_map[const_values_typ.downRng])
            else:
                downRng = int(const_values_typ.downRng)
            if const_values_typ.upRng in murphi.const_map.keys():
                upRng = 1 + int(murphi.const_map[const_values_typ.upRng])
            else:
                upRng = 1 + int(const_values_typ.upRng)
            for i in range(downRng,upRng):
                sub_const_map[str(i)] = murphi.VarExpr(name=str(i),typ=const_values_typ)
            invFinder.const_pmurphi_map[str(const_var)] = sub_const_map
        
    
    start_alphabet = ord('A')
    for constType in murphi.const_map:
        invFinder.paraAlpdict[str(constType)] = [chr(start_alphabet),chr(start_alphabet + 1)]
        start_alphabet = start_alphabet + 2



    for enum_name, enum_typ in c.enum_typ_map.items():
        for enum_typ_name in enum_typ.names:
            if enum_typ_name not in invFinder.all_pmurphi.keys():
                invFinder.all_pmurphi[enum_typ_name] = murphi.EnumValExpr(enum_typ, enum_typ_name)


    auxInv_dict = dict()
    get_ori_symm_invs = False

    firstCheck = True
    s_constructF = time.time()
    while (True):
        for name, instance in c.formula_instances.items():
            current_inv = instance["inv_name"]

            # 将所有的aux_inv都当成前提


            constructF = invFinder.ConstructF(protocol_name, name, instance, protocol_path, current_inv, all_ori_invs,
                                    BooleanType_vars, c.enum_typ_map, c.typ_map, ScalarSetType_vars)


            if firstCheck:
                start_time = time.time()
                firstCheck = False


            new_inv_list, inv_name, all_invs_list = constructF.smtFormula()

            inv_name = inv_name.split("/")[-1]

            if len(new_inv_list) > 0:
                all_ori_invs.extend(all_invs_list)
                ori_inv[current_inv].extend(all_invs_list)
                for i, new_inv in enumerate(new_inv_list):
                    auxInv_dict[inv_name + '_' + str(i + 1)] = new_inv
                    if (inv_name + '_' + str(i + 1)) not in wiseParaverifier_inv:
                        wiseParaverifier_inv[inv_name + '_' + str(i + 1)] = new_inv
                        
        if len(auxInv_dict) != 0:
            first_key = next(iter(auxInv_dict))
            invFinder.search4new_auxInv(c, constructF, first_key, auxInv_dict[first_key])
            auxInv_dict.pop(first_key)
        else:
            break

    # print("wiseParaverifier_inv: ", wiseParaverifier_inv)
    return wiseParaverifier_inv

def appendCont_and_save(file_path, new_cont, new_file_path):
    with open(file_path, 'r') as file:
        content = file.read()

    updated_protocol = content + new_cont

    with open(new_file_path, 'w') as new_file:
        new_file.write(updated_protocol)

def smvform_act(form):
    if isinstance(form, murphi.NegExpr):
        smvform_act(form.expr)
    elif isinstance(form, murphi.OpExpr):
        if isinstance(form.expr1, murphi.OpExpr) | isinstance(form.expr2, murphi.OpExpr):
            if isinstance(form.expr1, murphi.OpExpr):
                smvform_act(form.expr1)
            if isinstance(form.expr2, murphi.OpExpr):
                smvform_act(form.expr2)
        else:
            if str(form.expr1) in invFinder.EnumType_vars.keys() and isinstance(form.expr2, murphi.EnumValExpr):
                form.expr2.enum_val = form.expr2.enum_val.replace(form.expr2.enum_val, form.expr2.enum_val.lower())
    return form

def call_NuBMC(check_inv, protocol_name):

    inv_to_check = str(smvform_act(copy.deepcopy(check_inv))).replace("true", "TRUE")
    inv_to_check = str(smvform_act(inv_to_check)).replace("false", "FALSE")
            
    result = client.is_inv_bmc(protocol_name, inv_to_check)
    
    return result, check_inv

def and_statements(statement):
    return " & ".join(statement)

def or_statements(statement):
    return "(" + " | ".join(statement) + ")"

def disas_formula(form, inv_split):
    if isinstance(form, murphi.NegExpr):
        disas_formula(form.expr, inv_split)
    elif isinstance(form, murphi.OpExpr):
        if form.op == "&":
            disas_formula(form.expr1, inv_split)
            disas_formula(form.expr2, inv_split)
        else:
            inv_split.append(form)
    return inv_split

def num_to_char(num):
    return chr(ord('A') + int(num) - 1)

def char_replace_num(form, issame):
    new_form = copy.deepcopy(form)
    ivy_form = None
    new_idx = None
    # print("new_form: ", new_form)
    if isinstance(new_form, murphi.OpExpr):
        if isinstance(new_form.expr1, murphi.FieldName):
            if isinstance(new_form.expr1.v, murphi.ArrayIndex) and isinstance(new_form.expr1.field, lark.lexer.Token):
                if isinstance(new_form.expr1.v.v, murphi.FieldName) and isinstance(new_form.expr1.v.idx, murphi.VarExpr):
                    if issame:
                        new_form.expr1.v.idx = murphi.VarExpr("A", new_form.expr1.v.idx.typ)
                        new_idx = "A"
                    else:
                        new_idx = num_to_char(new_form.expr1.v.idx.name)
                    ivy_form = str(new_form.expr1.v.v.v).lower() + "_" + str(new_form.expr1.v.v.field) + "_" + new_form.expr1.field + "(" + new_idx + ")" + " " + str(new_form.op) + " " + str(new_form.expr2).lower()
                elif isinstance(new_form.expr1.v.idx, murphi.VarExpr):
                    if issame:
                        new_form.expr1.v.idx = murphi.VarExpr("A", new_form.expr1.v.idx.typ)
                        new_idx = "A"
                    else:
                        new_idx = num_to_char(new_form.expr1.v.idx.name)
                    ivy_form = str(new_form.expr1.v.v).lower() + "_" + str(new_form.expr1.field) + "(" + new_idx + ")" + " " + str(new_form.op) + " " + str(new_form.expr2).lower()
            elif isinstance(new_form.expr1.v, murphi.FieldName):
                if isinstance(new_form.expr2, murphi.FieldName) and isinstance(new_form.expr2.v, murphi.FieldName):
                    ivy_form = str(new_form.expr1.v.v).lower() + "_" + str(new_form.expr1.v.field) + "_" + str(new_form.expr1.field) + " " + str(new_form.op) + " " + str(new_form.expr2.v.v).lower() + "_" + str(new_form.expr2.v.field) + "_" + str(new_form.expr2.field)
                # print(str(new_form.expr1.v.v).lower() + "_" + str(new_form.expr1.v.field) + "_" + new_form.expr1.field)
                else:
                    if isinstance(new_form.expr2, murphi.VarExpr):
                        if issame:
                            new_form.expr2 = murphi.VarExpr("A", new_form.expr2.typ)
                            new_idx = "A"
                        else:
                            new_idx = num_to_char(new_form.expr2.name)
                    ivy_form = str(new_form.expr1.v.v).lower() + "_" + str(new_form.expr1.v.field) + "_" + str(new_form.expr1.field) + " " + str(new_form.op) + " " + str(new_form.expr2).lower()
        elif isinstance(new_form.expr1, murphi.ArrayIndex):
            if isinstance(new_form.expr1.v, murphi.FieldName) and isinstance(new_form.expr1.idx, murphi.VarExpr):
                if isinstance(new_form.expr1.v.v, murphi.FieldName):
                    if issame:
                        new_form.expr1.idx = murphi.VarExpr("A", new_form.expr1.idx.typ)
                        new_idx = "A"
                    else:
                        new_idx = num_to_char(new_form.expr1.idx.name)
                    form1, form2, form3 = copy.deepcopy(new_form.expr1.v.v.v), copy.deepcopy(new_form.expr1.v.v.field), copy.deepcopy(new_form.expr1.v.field)
                    ivy_form = str(form1) + "_" + str(form2) + "_" + str(form3) + "(" + new_idx + ")" + " " + str(new_form.op) + " " + str(new_form.expr2).lower()
            else:
                if issame:
                    new_form.expr1.idx = murphi.VarExpr("A", new_form.expr1.idx.typ)
                    new_idx = "A"
                else:
                    new_idx = num_to_char(new_form.expr1.idx.name)
                ivy_form = str(new_form.expr1.v).lower() + "(" + new_idx + ")" + " " + str(new_form.op) + " " + str(new_form.expr2).lower()
        else:
            ivy_form = str(new_form.expr1).lower() + " " + str(new_form.op) + " " + str(new_form.expr2)

    # print("ivy_form1: ", ivy_form)
    return ivy_form, new_idx

def direct_promotion(inv_split):
    ivy_list = list()
    idx_list = list()

    # print("inv_split: ", inv_split)
    for inv in inv_split:
        ivy_form, new_idx = char_replace_num(inv, False)
        # print("ivy_form2: ", ivy_form)
        ivy_list.append(ivy_form)
        if new_idx != None and new_idx not in idx_list:
            idx_list.append(new_idx)
    if len(idx_list)>1:
        classifier = "forall " + ",".join(idx_list) + ". " + f"({idx_list[0]} ~= {idx_list[1]})" + " -> "
    elif len(idx_list) == 1:
        classifier = "forall " + ",".join(idx_list) + ". "
    else:
        classifier = ""
    conjecture = "conjecture " + classifier + f"~({and_statements(ivy_list)})"

    return conjecture


def categorization(form, field_dict, global_list):
    if isinstance(form, murphi.OpExpr):
        if isinstance(form.expr1, murphi.FieldName):
            if isinstance(form.expr1.v, murphi.ArrayIndex) and isinstance(form.expr1.field, lark.lexer.Token):
                if isinstance(form.expr1.v.idx, murphi.VarExpr):
                    if str(form.expr1.v.idx.name) not in field_dict.keys():
                        field_dict[str(form.expr1.v.idx.name)] = [form]
                    else:
                        field_dict[str(form.expr1.v.idx.name)].append(form)
            elif isinstance(form.expr1.v, murphi.FieldName) and isinstance(form.expr1.field, lark.lexer.Token):
                global_list.append(str(form))
        elif isinstance(form.expr1, murphi.ArrayIndex):
            if isinstance(form.expr1.idx, murphi.VarExpr):
                if str(form.expr1.idx.name) not in field_dict.keys():
                    field_dict[str(form.expr1.idx.name)] = [form]
                else:
                    field_dict[str(form.expr1.idx.name)].append(form)
        else:
            global_list.append(str(form))

def list_equal(chlist):
    all_equal = all(sublist == chlist[0] for sublist in chlist)

    return all_equal

def terms_comparison(field_dict):

    def str_replace(form):
        new_form = copy.deepcopy(form)
        if isinstance(new_form, murphi.OpExpr):
            if isinstance(new_form.expr1, murphi.FieldName):
                if isinstance(new_form.expr1.v, murphi.ArrayIndex) and isinstance(form.expr1.field, lark.lexer.Token): 
                    if isinstance(new_form.expr1.v.idx, murphi.VarExpr):
                        new_form.expr1.v.idx = murphi.VarExpr("A", new_form.expr1.v.idx.typ)
                        left_form = str(new_form.expr1)
                        right_form = str(new_form.expr2)
            elif isinstance(new_form.expr1, murphi.ArrayIndex):
                if isinstance(new_form.expr1.idx, murphi.VarExpr):
                    new_form.expr1.idx = murphi.VarExpr("A", new_form.expr1.idx.typ)
                    left_form = str(new_form.expr1)
                    right_form = str(new_form.expr2)
            else:
                pass

        return left_form, right_form

    left_forms, right_forms = list(), list()
    for k, value in field_dict.items():
        leftf, rightf = list(), list()
        for v in value:
            lf, rf = str_replace(v)
            leftf.append(lf)
            rightf.append(rf) 
        leftf.sort()
        rightf.sort()
        left_forms.append(leftf)
        right_forms.append(rightf)

    left_term = False
    right_term = False
    if list_equal(left_forms):
        left_term = True
    
    if list_equal(right_forms):
        right_term = True
    
    return left_term, right_term


def merger_promotion(inv_name, inv_split):

    field_dict = dict()
    global_list = list()
    for form in inv_split:
        categorization(form, field_dict, global_list)
    # print(field_dict)

    left_term, right_term = terms_comparison(field_dict)

    # print(left_term, right_term)

    conjecture = ''
    merge_dict = dict()
    same_ruleN = dict()
    if len(field_dict) == 1:
        same_ruleN = get_oneNInv(field_dict, global_list, inv_name, same_ruleN)
    elif left_term and right_term:
        conjecture, merge_dict = get_combpro1(field_dict, global_list)
    else:
        conjecture, merge_dict = get_combpro2(field_dict, global_list)
    
    # print(conjecture, merge_dict)

    return conjecture, merge_dict, same_ruleN


def get_combpro1(field_dict, global_list):
    first_key = next(iter(field_dict))
    ivy_list = list()
    exists_term = list()
    merge_dict = dict()

    for formula in field_dict[first_key]:
        ivy_form, new_idx = char_replace_num(formula, True)
        exists_term.append(ivy_form)
    classifier = "exists " + new_idx + ". "

    ivy_list.extend(exists_term)
    global_list.sort()
    for form in global_list:
        ivy_list.append(str(form))
    conjecture = "conjecture " + classifier + f"~({and_statements(ivy_list)})"

    merge_dict['local'] = [exists_term]
    merge_dict['global'] = global_list

    return conjecture, merge_dict

def get_combpro2(field_dict, global_list):
    # print("get_combpro3: ", field_dict, global_list)

    ivy_list = list()
    exists_term = dict()
    merge_dict = dict()

    for n, formula in field_dict.items():
        et = list()
        for form in formula:
            ivy_form, new_idx = char_replace_num(form, True)
            et.append(ivy_form)
        exists_term[n] = et
    
    classifier = "exists " + new_idx + ". "

    sub_exists = list()
    for k, v in exists_term.items():
        if "local" in merge_dict.keys():
            merge_dict["local"].append(v)
        else:
            merge_dict["local"] = [v]
        sub_exists.append(and_statements(v))
    ivy_list.append(or_statements(sub_exists))

    global_list.sort()
    for form in global_list:
        ivy_list.append(str(form))
    conjecture = "conjecture " + classifier + f"~({and_statements(ivy_list)})"

    merge_dict['global'] = global_list

    return conjecture, merge_dict

def fourth_method(tmp_merge, all_merge):
    # print(tmp_merge, all_merge)

    def subform_name(tn, an):
        if (tn in an) or (an in tn):
            return True
        else:
            return False

    def subform_form(tv, av):
        is_form = False
        tform, aform = tv[1], av[1]
        fform, reform = None, None
        if tform["global"] == aform["global"]:
            ltform = tform["local"]
            laform = aform["local"]
            for lt in ltform:
                if lt in laform:
                    is_form = True
                else:
                    is_form = False
                    break
            if not is_form:
                for la in laform:
                    if la in ltform:
                        is_form = True
                    else:
                        is_form = False
                        break
                if is_form:
                    fform = tv[0]
                    reform = av[0]
            else:
                fform = av[0]
                reform = tv[0]
        
        return is_form, fform, reform


    result = False
    conj = None
    reconj = None
    for tn, tv in tmp_merge.items():
        for an, av in all_merge.items():
            isre = subform_name(tn, an)
            # print(isre, rename)
            is_form, fform, reform = subform_form(tv, av)
            # print(is_form, fform)
            if isre and is_form:
                if (tv[0] == fform) or (av[0] == fform):
                    result = True
                    conj = fform
                    reconj = reform
                    break
    
    # print(result, conj, reconj)
    return result, conj, reconj

def get_oneNInv(field_dict, global_list, inv_name, same_ruleN):
    rule_name = str("_".join(inv_name.split("_")[-2:]))
    first_key = next(iter(field_dict))

    if rule_name in same_ruleN.keys():
        same_ruleN[rule_name].append([field_dict[first_key], global_list])
    else:
        same_ruleN[rule_name] = list([field_dict[first_key], global_list])
    
    return same_ruleN


def remove_duplicate(tmp_merge, all_merge):
    # print(tmp_merge, all_merge)
    first_key = next(iter(tmp_merge))
    var_tm = tmp_merge[first_key][1]
    result = False

    def local_same(tml, vml):
        tlocal, alocal = copy.deepcopy(tml), copy.deepcopy(vml)
        islsame = False
        # print(tlocal, alocal)
        if len(tlocal) == len(alocal) and len(alocal)>1:
            if len(tlocal[0]) == len(alocal[0]) and len(tlocal[1]) == len(alocal[1]):
                tlocal[0].sort()
                alocal[0].sort()
                new_tl0 = and_statements(tlocal[0]).replace("(B)", "(A)")
                new_al0 = and_statements(alocal[0]).replace("(B)", "(A)")
                if new_tl0 == new_al0:
                    tlocal[1].sort()
                    alocal[1].sort()
                    new_tl1 = and_statements(tlocal[1]).replace("(B)", "(A)")
                    new_al1 = and_statements(alocal[1]).replace("(B)", "(A)")
                    if new_tl1 == new_al1:
                        islsame = True
            elif len(tlocal[0]) == len(alocal[1]) and len(alocal[0]) == len(tlocal[1]):
                tlocal[0].sort()
                alocal[1].sort()
                new_tl0 = and_statements(tlocal[0]).replace("(B)", "(A)")
                new_al1 = and_statements(alocal[1]).replace("(B)", "(A)")
                if new_tl0 == new_al1:
                    tlocal[1].sort()
                    alocal[0].sort()
                    new_tl1 = and_statements(tlocal[1]).replace("(B)", "(A)")
                    new_al0 = and_statements(alocal[0]).replace("(B)", "(A)")
                    if new_tl1 == new_al0:
                        islsame = True
            else:
                pass
        elif len(tlocal) == len(alocal) and len(tlocal) == 1:
            if len(tlocal[0]) == len(alocal[0]):
                tlocal[0].sort()
                alocal[0].sort()
                if tlocal[0] == alocal[0]:
                    islsame = True
        else:
            pass

        return islsame

    for _, values in all_merge.items():
        var_am = values[1]
        if var_tm["global"] == var_am["global"]:
            result = local_same(var_tm["local"], var_am["local"])
    
    return result

def get_1NCMPInv(inv_list):
    field_list = list()
    global_list = list()
    for inv in inv_list:
        field_list.append(inv[0])
        for gvar in inv[1]:
            if gvar not in global_list:
                global_list.append(gvar)
    
    exists_term = list()

    for finv in field_list:
        et = list()
        for form in finv:
            ivy_form, new_idx = char_replace_num(form, True)
            et.append(ivy_form)
        exists_term.append(et)
    classifier = "exists " + new_idx + ". "

    sub_exists = list()
    ivy_list = list()
    for v in exists_term:
        sub_exists.append(and_statements(v))
    ivy_list.append(or_statements(sub_exists))

    for form in global_list:
        ivy_list.append(str(form))
    conjecture = "conjecture " + classifier + f"~({and_statements(ivy_list)})"

    return conjecture
            
    
    
def comb_promotion(wpInv, protocol_name, protocol_path):
    # print(wpInv)
    largnum_name = "largerN" + "_" + protocol_name
    file_path = "/".join(protocol_path.split("/")[:-1]) + "/" + largnum_name
    # print("file_path: ", file_path)
    try:
        if os.path.isfile(file_path+".smv"):
            # print(f"File '{file_path}.smv' is exist.\n")
            pass
    except FileNotFoundError:
        print(f"File '{file_path}.smv' not found.\n")

    ivy_forms = ''
    if ("german" or "flash") in protocol_name.lower():
        # print("german")
        new_cont = "axiom exists N1:node_t, N2:node_t. N1~=N2"
        ivy_forms += "\n\n" + new_cont + "\n\n"

    all_merge = dict()
    all_conj = list()
    for inv_name, inv in wpInv.items():
        check_result, _ = call_NuBMC(inv, largnum_name)
        # print("result: ", check_result)
        inv_split = list()
        inv_split = disas_formula(inv, inv_split)
        # print("inv_split: ", inv_split)
        if check_result:
            # 直接推广
            ivy_form = direct_promotion(inv_split)
            # print("ivy_form: ", ivy_form)
            ivy_forms += ivy_form + "\n"
        else:
            conjecture, merge_dict, same_ruleN = merger_promotion(inv_name, inv_split)

            tmp_merge = dict()
            tmp_merge[inv_name] = [conjecture, merge_dict]

            rdresult = remove_duplicate(tmp_merge, all_merge)

            # print(rdresult)

            if rdresult:
                pass

            else:

                result, conj, reconj = fourth_method(tmp_merge, all_merge)

                if result:
                    if conj not in all_conj:
                        all_conj.append(conj)
                    if reconj in all_conj:
                        all_conj.remove(reconj)
                else:
                    all_conj.append(conjecture)


                all_merge[inv_name] = [conjecture, merge_dict]


    if same_ruleN:
        for _, inv_list in same_ruleN.items():
            conjecture = get_1NCMPInv(inv_list)
            all_conj.append(conjecture)
    
    # print(all_conj)

    for cj in all_conj:
        ivy_forms += cj + "\n"
        
    
    appendCont_and_save(protocol_path+".ivy", ivy_forms, protocol_path+"_prove.ivy")

def get_memory_usage():
    process = psutil.Process(os.getpid())
    return process.memory_info().rss      

def DLfree_verification():
    protocol_path, is_combpro = get_comdpara()
    # sys.stdout = open(protocol_path + '_debug.log', 'w')
    try:
        if os.path.isfile(protocol_path+".m"):
            protocol_name = protocol_path.split("/")[-1]
            wpInv = call_wiseParaverifier(protocol_path, protocol_name)
            print(f"The auxiliary invariants found are stored in {protocol_path}_invs.txt")
            if is_combpro:
                comb_promotion(wpInv, protocol_name, protocol_path)
                print(f"The invariants of the merged promotion are stored in the {protocol_path}_prove.ivy")
    except FileNotFoundError:
        print(f"File '{protocol_path}.m' not found.\n")
    # sys.stdout.close()


if __name__ == "__main__":
    start_time = time.time()

    DLfree_verification()

    memory_usage = get_memory_usage()

    end_time = time.time()

    all_times = end_time - start_time

    print(f"Memory usage: {memory_usage / 1024 / 1024:.2f} MB")

    print(f"ALL TIMES: {all_times:.6f} s")
