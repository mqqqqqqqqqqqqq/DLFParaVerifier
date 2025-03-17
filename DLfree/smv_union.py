import itertools
import re
import sys
import os
sys.path.append('./')
sys.path.append('../')

import client
import murphi
from murphiparser import *
from wiseParaVerifier.invFinder import trans2IVY, run_ivy

def check_union_formula(file_path):
    # two node
    formulas = []
    # file_path = "../protocols/trans/flash_inv_node1"
    with open(file_path + '.txt', "r") as file:
        lines = file.readlines()
        for line in lines:
            # print("line: ", line)
            formulas.append(line.strip())

    # 存储结果的列表
    result_formulas = []
    count_union = []
    ori_formulas = []

    count = 0
    combinations = list(itertools.combinations_with_replacement(formulas, 2))
    # 处理公式并循环比较
    for combo in combinations:
        formula1, formula2 = combo
        # 使用正则表达式匹配括号内的公式
        match1 = re.search(r'\(([^)]+)\)', formula1)
        match2 = re.search(r'\(([^)]+)\)', formula2)

        count1 = formula1.split("!")[0]
        count2 = formula2.split("!")[0]

        if match1 and match2:
            # 提取匹配到的括号内的公式
            inner_formula1 = match1.group(1)
            inner_formula2 = match2.group(1)

            ori_formula1 = match1.group(1)
            ori_formula2 = match2.group(1)

            # 使用正则表达式将等式左边的值变为小写
            inner_formula1 = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), inner_formula1)
            inner_formula2 = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), inner_formula2)
            # print("inner_formula1: ", inner_formula1)

            # german 提取CurCmd和ExGntd的值
            # if "CurCmd" in str(inner_formula1):
            #     curcmd1 = inner_formula1.split("CurCmd = ")[1].split(" &")[0]
            # else:
            #     curcmd1 = None
            # if "ExGntd" in str(inner_formula1):
            #     exgntd1 = inner_formula1.split("ExGntd = ")[1].split(" &")[0]
            # else:
            #     exgntd1 = None
            # if "CurCmd" in str(inner_formula2):
            #     curcmd2 = inner_formula2.split("CurCmd = ")[1].split(" &")[0]
            # else:
            #     curcmd2 = None
            # if "ExGntd" in str(inner_formula2):
            #     exgntd2 = inner_formula2.split("ExGntd = ")[1].split(" &")[0]
            # else:
            #     exgntd2 = None
            

            # # 如果CurCmd和ExGntd的值相等，将这两个公式相与并只保留一个
            # if curcmd1 == curcmd2 and exgntd1 == exgntd2:
            #     count += 1
            #     settle_formula1 = re.sub(r'CurCmd = [^&]+', '', inner_formula1)
            #     settle_formula1 = re.sub("Curcmd =  &", "", settle_formula1)
            #     settle_formula1 = re.sub(r'ExGntd = [^&]+', '', settle_formula1)
            #     settle_formula1 = re.sub("ExGntd =  &", "", settle_formula1)

            #     re_formula1 = re.sub(r'CurCmd = [^&]+', '', ori_formula1)
            #     re_formula1 = re.sub("Curcmd =  &", "", re_formula1)
            #     re_formula1 = re.sub(r'ExGntd = [^&]+', '', re_formula1)
            #     re_formula1 = re.sub("ExGntd =  &", "", re_formula1)

            #     union_formula = "!(" + settle_formula1.replace("true", "TRUE").replace("false",
            #                                                                            "FALSE") + " & " + inner_formula2.replace(
            #         "true", "TRUE").replace("false", "FALSE").replace("[1]", "[2]") + ")"
            #     new_formula = re.sub(r'&\s+&', '&', union_formula)
            #     result_formulas.append(new_formula.replace("(& ", "(").replace("& )", ")").replace("&  &", "&"))

            #     re_formulas = re_formula1 + " & " + ori_formula2.replace("[1]", "[2]")
            #     old_formula = re.sub(r'&\s+&', '&', re_formulas)
            #     ori_formulas.append(old_formula.replace("(& ", "(").replace("& )", ")").replace("&  &", "&"))

            #     new_count1 = re.sub(r':\s+', '', count1)
            #     new_count2 = re.sub(r':\s+', '', count2)
            #     new_count = str("union" + str(count) + "_" + str(new_count1) + "_&_" + str(new_count2))
            #     count_union.append(new_count)

            # flash
            if "sta.Dir.Dirty" in str(inner_formula1):
                sta1 = inner_formula1.split("Sta.Dir.Dirty = ")[1].split(" &")[0]
            else:
                sta1 = None
            if "sta.Dir.Dirty" in str(inner_formula2):
                sta2 = inner_formula2.split("Sta.Dir.Dirty = ")[1].split(" &")[0]
            else:
                sta2 = None
            
            # 如果Sta.Dir.Dirty的值相等，将这两个公式相与并只保留一个
            if sta1 == sta2:
                count += 1
                settle_formula1 = re.sub(r'Sta.Dir.Dirty = [^&]+', '', inner_formula1)
                settle_formula1 = re.sub("Sta.Dir.Dirty =  &", "", settle_formula1)

                re_formula1 = re.sub(r'Sta.Dir.Dirty = [^&]+', '', ori_formula1)
                re_formula1 = re.sub("Sta.Dir.Dirty =  &", "", re_formula1)

                union_formula = "!(" + settle_formula1.replace("true", "TRUE").replace("false",
                                                                                       "FALSE") + " & " + inner_formula2.replace(
                    "true", "TRUE").replace("false", "FALSE").replace("[1]", "[2]") + ")"
                new_formula = re.sub(r'&\s+&', '&', union_formula)
                result_formulas.append(new_formula.replace("(& ", "(").replace("& )", ")").replace("&  &", "&"))

                re_formulas = re_formula1 + " & " + ori_formula2.replace("[1]", "[2]")
                old_formula = re.sub(r'&\s+&', '&', re_formulas)
                ori_formulas.append(old_formula.replace("(& ", "(").replace("& )", ")").replace("&  &", "&"))

                new_count1 = re.sub(r':\s+', '', count1)
                new_count2 = re.sub(r':\s+', '', count2)
                new_count = str("union" + str(count) + "_" + str(new_count1) + "_&_" + str(new_count2))
                count_union.append(new_count)

    # three node
    # formulas1 = []
    # formulas2 = []
    # file_path1 = "protocols/trans/inv_node1"
    # file_path2 = "protocols/trans/inv_node2"
    # with open(file_path1 + '.txt', "r") as file:
    #     lines = file.readlines()
    #     for line in lines:
    #         # print("line: ", line)
    #         formulas1.append(line.strip())
    #
    # with open(file_path2 + '.txt', "r") as file:
    #     lines = file.readlines()
    #     for line in lines:
    #         # print("line: ", line)
    #         formulas2.append(line.strip())
    #
    # # 存储结果的列表
    # result_formulas = []
    # count_union = []
    #
    # # 处理公式并循环比较
    # for i in range(len(formulas1)):
    #     formula1 = formulas1[i]
    #     for j in range(i, len(formulas2)):
    #         formula2 = formulas2[j]
    #         print("formula1: ", formula1)
    #         print("formula2: ", formula2)
    #         # 使用正则表达式匹配括号内的公式
    #         match1 = re.search(r'\(([^)]+)\)', formula1)
    #         match2 = re.search(r'\(([^)]+)\)', formula2)
    #
    #         count1 = formula1.split("!")[0]
    #         count2 = formula2.split("!")[0]
    #
    #         if match1 and match2:
    #             # 提取匹配到的括号内的公式
    #             inner_formula1 = match1.group(1)
    #             inner_formula2 = match2.group(1)
    #
    #             # 使用正则表达式将等式左边的值变为小写
    #             inner_formula1 = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), inner_formula1)
    #             inner_formula2 = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), inner_formula2)
    #             # print("inner_formula1: ", inner_formula1)
    #
    #             # 提取CurCmd和ExGntd的值
    #             if "CurCmd" in str(inner_formula1):
    #                 curcmd1 = inner_formula1.split("CurCmd = ")[1].split(" &")[0]
    #             else:
    #                 curcmd1 = None
    #             if "ExGntd" in str(inner_formula1):
    #                 exgntd1 = inner_formula1.split("ExGntd = ")[1].split(" &")[0]
    #             else:
    #                 exgntd1 = None
    #             if "CurCmd" in str(inner_formula2):
    #                 curcmd2 = inner_formula2.split("CurCmd = ")[1].split(" &")[0]
    #             else:
    #                 curcmd2 = None
    #             if "ExGntd" in str(inner_formula2):
    #                 exgntd2 = inner_formula2.split("ExGntd = ")[1].split(" &")[0]
    #             else:
    #                 exgntd2 = None
    #
    #             print("curcmd1: ", curcmd1)
    #             print("exgntd1: ", exgntd1)
    #             print("curcmd2: ", curcmd2)
    #             print("exgntd2: ", exgntd2)
    #
    #             # 如果CurCmd和ExGntd的值相等，将这两个公式相与并只保留一个
    #             if curcmd1 == curcmd2 and exgntd1 == exgntd2:
    #                 settle_formula1 = re.sub(r'CurCmd = [^&]+', '', inner_formula1)
    #                 settle_formula1 = re.sub("Curcmd =  &", "", settle_formula1)
    #                 settle_formula1 = re.sub(r'ExGntd = [^&]+', '', settle_formula1)
    #                 settle_formula1 = re.sub("ExGntd =  &", "", settle_formula1)
    #                 union_formula = "!(" + inner_formula2.replace(
    #                     "true", "TRUE").replace("false", "FALSE") + " & " + settle_formula1.replace("true", "TRUE").replace("false",
    #                                                                                        "FALSE").replace("[1]", "[3]") + ")"
    #                 new_formula = re.sub(r'&\s+&', '&', union_formula)
    #                 result_formulas.append(new_formula.replace("(& ", "(").replace("& )", ")"))
    #
    #                 new_count1 = re.sub(r':\s+', '', count1)
    #                 new_count2 = re.sub(r':\s+', '', count2)
    #                 new_count = str("union_1node_" + str(new_count1) + "_&_2node_" + str(new_count2))
    #                 count_union.append(new_count)

    return result_formulas, count_union, ori_formulas


def gene_formulas(protocol_name, formula):
    result_dict = {}  # 用于记录每个保留项的结果
    for i in range(len(formula)):
        j = 0
        tmp_str = formula[i]
        delete_formula = formula[:i] + formula[i+1:]
        # print("delete_formula: ", delete_formula)
        while j < len(delete_formula):
            # print(i, j)
            temp_formula = delete_formula[:j] + delete_formula[j+1:]  # 删除 j 项

            if temp_formula:
                # print("temp_formula: ", temp_formula)
                smv_formula = str(" & ".join(temp_formula)) + " & " + tmp_str
                smv_formula = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), smv_formula)
                smv_formula = ("!(" + smv_formula.replace("true", "TRUE").replace("false", "FALSE") + ")")
                smv_formula = smv_formula.replace("(&", "(").replace("& )", ")")
                smv_formula = re.sub(r'&\s+&', '&', smv_formula)
                # print("smv_formula: ", smv_formula)
                # smv_result = client.check_invariants(protocol_name, smv_formula)
                largerpn = "largerN" + "_" + protocol_name
                smv_result = client.is_inv_bmc(largerpn, smv_formula)
                # print("smv_result: ", smv_result, smv_formula)
                if smv_result:
                    delete_formula = temp_formula
                else:
                    j += 1
            else:
                # print("temp_formula: ", temp_formula)
                smv_formula = tmp_str
                smv_formula = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), smv_formula)
                smv_formula = ("!(" + smv_formula.replace("true", "TRUE").replace("false", "FALSE") + ")")
                smv_formula = smv_formula.replace("(&", "(").replace("& )", ")")
                smv_formula = re.sub(r'&\s+&', '&', smv_formula)
                # print("smv_formula: ", smv_formula)
                # smv_result = client.check_invariants(protocol_name, smv_formula)
                largerpn = "largerN" + "_" + protocol_name
                smv_result = client.is_inv_bmc(largerpn, smv_formula)
                # print("smv_result: ", smv_result, smv_formula)
                if smv_result:
                    delete_formula = tmp_str
                break
        if isinstance(delete_formula, list):
            if tmp_str in delete_formula:
                result_dict[len(delete_formula)] = delete_formula
            else:
                # print("delete_formula: ", delete_formula)
                # print("tmp_str: ", tmp_str)
                delete_formula.append(tmp_str)
                result_dict[len(delete_formula)] = delete_formula
        else:
            tmp_formula = list()
            tmp_formula.append(delete_formula)
            result_dict[len(tmp_formula)] = tmp_formula
            break
        # print("result_dict: ", result_dict)
    return result_dict


def select_min_key(result_dict):
    if result_dict:
        min_key = min(result_dict.keys())
        return result_dict[min_key]
    else:
        return None


def union_res(protocol_name, parse_name, file_path):

    result_formulas, count_union, ori_formulas = check_union_formula(file_path)
    # print("ori_formulas: ", ori_formulas)

    all_formulas = []
    for i in range(len(ori_formulas)):
        print(f"{count_union[i]}: {ori_formulas[i]}\n")
        split_formula = str(ori_formulas[i]).split(" & ")
        print(f"split_formula: {split_formula}\n")
        formula_dict = gene_formulas(protocol_name, split_formula)
        print(f"formula_dict: {formula_dict}\n")
        formula_list = select_min_key(formula_dict)
        re_formula = "!(" + str(" & ".join(formula_list)) + ")"
        print(f"re_formula: {re_formula}\n")
        all_formulas.append(re_formula)

    no_repeat = []
    no_repeat = list(set(all_formulas))
    with open(parse_name + "_union_invs.txt", "a") as file:
        for i in range(len(all_formulas)):
            file.write(f"{count_union[i]}:\n")
            file.write(murphi.indent(all_formulas[i], 2))
            file.write("\n")

        file.write(f"counts: {len(all_formulas)}\n")

        file.write(f"Delete duplicate inv: \n")
        for formula in no_repeat:
            file.write(murphi.indent(formula, 2))
            file.write("\n")
        file.write(f"counts: {len(no_repeat)}\n")

    count = 0
    all_formula = []
    # no generalise
    # for i in range(len(result_formulas)):
    #     print(result_formulas[i])
    #     print(client.check_invariants(protocol_name, str(result_formulas[i])))
    #     with open(parse_name + "_union_invs.txt", "a") as file:
    #         file.write(f"{count_union[i]}: {client.check_invariants(protocol_name, str(result_formulas[i]))}\n")
    #         # smv_formula = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).upper(), result_formulas[i])
    #         # smv_formula.replace("TRUE", "true").replace("FALSE", "false")
    #         file.write(murphi.indent(ori_formulas[i], 2))
    #         file.write("\n")
    #     if client.check_invariants(protocol_name, result_formulas[i]):
    #         all_formula.append(result_formulas[i])
    #         count += 1
    #
    # print("all_formula: ", all_formula)
    # with open(parse_name + "_union_invs.txt", "a") as file:
    #     file.write(f"counts: {count}\n")
    # print("counts: ", count)

def ivy_result(inv_path):
    # 转换到ivy格式并调用ivy check
    ivyselect = "#lang ivy1.7"
    trans2IVY(inv_path + "_withInductiveInvs", ivyselect)
    run_ivy(inv_path + "_withInductiveInvs" + ".ivy")


def check_noge_inv(parse_name, protocol_name):
    # two node
    formulas = []
    # file_path = "protocols/trans/flash_inv_noge_node2"
    # file_path = "protocols/trans/german_true_noge_node2"
    # file_path = "protocols/trans/german_ptr_noge_inv"
    file_path = "protocols/trans/flash_inv"
    with open(file_path + '.txt', "r") as file:
        lines = file.readlines()
        for line in lines:
            # print("line: ", line)
            formulas.append(line.strip())

    # 存储结果的列表
    result_formulas = []

    # 处理公式并循环比较
    for formula in formulas:
        # 使用正则表达式匹配括号内的公式
        match = re.search(r'\(([^)]+)\)', formula)

        if match:
            # 提取匹配到的括号内的公式
            inner_formula = match.group(1)

            # 使用正则表达式将等式左边的值变为小写
            inner_formula = re.sub(r'= (\w+)', lambda x: '= ' + x.group(1).lower(), inner_formula)
            # new_formula = "!(" + inner_formula.replace("true", "TRUE").replace("false", "FALSE").replace("[1]", "[2]") + ")"
            new_formula = "!(" + inner_formula.replace("true", "TRUE").replace("false", "FALSE") + ")"
            # print("new_formula: ", new_formula)
            result_formulas.append(new_formula)
    
    # smv_content = ""
    # with open(parse_name + "_node3.smv", "r") as file:
    #     smv_content = file.read()
    # smv_content = str(parse_file(parse_name+".m", smvSelect=True))
    # with open(parse_name + "_node3.smv", "w") as f:
    #     f.write(str(smv_content))
    # client.calculate_protocol_reachability(protocol_name, smv_content)

    for i in range(len(result_formulas)):
        largerpn = "largerN" + "_" + protocol_name
        fomu_result = client.is_inv_bmc(largerpn, result_formulas[i])
        # fomu_result = client.check_invariants(protocol_name, result_formulas[i])
        print(f"result_formulas[{i}]: ", result_formulas[i], fomu_result)
        with open(parse_name + "_23shared_invs.txt", "a") as file:
            # str_formula = formulas[i].replace("[1]", "[2]")
            str_formula = formulas[i]
            file.write(f"{fomu_result}{murphi.indent(str_formula, 2)}\n")

def check_gene_inv(protocol_name, parse_name, file_path):
    old_formulas = list()
    with open(file_path + '.txt', "r") as file:
        lines = file.readlines()
        for line in lines:
            # print("line: ", line)
            old_formulas.append(line.strip())
    
    all_formulas_dict = {}
    all_formulas_list = []
    for i in range(len(old_formulas)):
        formula_split_list = str(old_formulas[i]).split(":")
        # print(f"formula_split_list: {formula_split_list}\n")
        str_name = formula_split_list[0]
        if formula_split_list[1]:
            str_formula = formula_split_list[1].replace("!(", "").replace(")", "")
            split_formula = str(str_formula).split(" & ")
            # print(f"split_formula: {split_formula}\n")
            formula_dict = gene_formulas(protocol_name, split_formula)
            # print(f"formula_dict: {formula_dict}\n")
            formula_list = select_min_key(formula_dict)
            re_formula = "!(" + str(" & ".join(formula_list)) + ")"
            # print(f"re_formula: {re_formula}\n")
            all_formulas_dict[str_name] = re_formula
            all_formulas_list.append(re_formula)
    
    no_repeat = []
    no_repeat = list(set(all_formulas_list))
    # print(len(all_formulas_list))
    with open(file_path + "_gene.txt", "a") as file:
        count = 0
        for name,inv in all_formulas_dict.items():
            file.write(name + ":" + murphi.indent(inv, 2))
            file.write('\n')
        file.write(f"counts: {len(all_formulas_dict)}\n")
        file.write("Delete duplicate inv:\n")
        for no_re in no_repeat:
            file.write(no_re)
            file.write('\n')
        file.write(f"counts: {len(no_repeat)}\n")
        
    return no_repeat


if __name__ == "__main__":

    # sys.stdout = open("./german_withoutData_deal.log", 'w')
    # sys.stderr = open("./german_withoutData_deal.log", 'w')

    # sys.stdout = open("flash_withoutDatatest.log", 'w')
    # sys.stderr = open("flash_withoutDatatest.log", 'w')

    # parse_name = "protocols/mutualEx/mutualEx"
    # parse_name = "protocols/mutdata/mutdata"
    # parse_name = "protocols/german_withoutData/german_withoutData"
    # parse_name = "protocols/german_withoutData/german_withoutData_ptr"
    parse_name = "protocols/flash/flash"
    # parse_name = "protocols/german/german"
    # parse_name = "../NuSMV2/German"
    protocol_name = parse_name.split("/")[-1]
    
    # smv_content = ""
    # with open(parse_name + "_node2.smv", "r") as file:
    #     smv_content = file.read()
    # client.calculate_protocol_reachability(protocol_name, smv_content)

    # smv_content = str(parse_file(parse_name+".m", smvSelect=True))
    # with open(parse_name + "_node1.smv", "w") as f:
    #     f.write(str(smv_content))
    # client.calculate_protocol_reachability(protocol_name, smv_content)


    try:
        for root, dirs, files in os.walk(os.path.dirname(parse_name)):
            for file in files:
                if file.endswith(".smv"):
                    file_path = os.path.join(root, file)
                    with open(file_path, "r") as file:
                        smv_content = file.read()
                        client.set_bmc(os.path.splitext(os.path.basename(file_path))[0], smv_content)
    except ValueError:
        print("set bmc failed. Please check if the Server is ready for communication")
    
    check_noge_inv(parse_name, protocol_name)
    
    # print("check_gene_inv start!")
    # gene_file_path = "protocols/trans/german_true_noge_node1"
    # gene_file_path = "protocols/tree_branch/german_withoutdata/german_inv_method1"
    # gene_file_path = "protocols/trans/flash_23shared_false"
    # result_formula = check_gene_inv(protocol_name, parse_name, gene_file_path)
    # print("result_formula: ", result_formula)
    # print("\n\n\n\n")

    # print("union_res start!")
    # union_file_path = "protocols/trans/german_false_noge_node1"
    # union_file_path = "protocols/trans/german_ptr_inv_false"
    # union_file_path = "protocols/trans/flash_23shared_false"
    # union_res(protocol_name, parse_name, union_file_path)

    # ivy_result(parse_name)

    # sys.stdout.close()
    # sys.stderr.close()
