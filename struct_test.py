import datetime
import re
from shutil import copy
import zipfile
import os
import git
from shutil import rmtree
from shutil import copyfile
import sys
import subprocess
from subprocess import PIPE

git_repo = "https://www.cs.bgu.ac.il/~comp191/compiler"



def setup_cases(cases, target):
    zip_ref = zipfile.ZipFile(cases, 'r')
    zip_ref.extractall(target)
    zip_ref.close()


def setup_sub_workspace(target, sub_file, cases, subdir):
    if (os.path.exists(target)):
        rmtree(target)
    repo = git.Repo.clone_from(git_repo, target + subdir)
    setup_cases(cases, target)
    repo.git.execute(["git", "apply", "--reject", os.path.abspath(sub_file)])


def run_sub(cmd, tmout, crt_shell=False, err_to_out=False):

    return subprocess.run(cmd, stdout=subprocess.PIPE,
                          shell=crt_shell, stderr=(subprocess.DEVNULL if (not err_to_out) else subprocess.STDOUT),
                          timeout=tmout).stdout


def test_compiler():
    compiler_grade = 0
    timeout = 300
    notes = ""
    notes_limit = 30 * 1024
    case_count = len([f for f in os.listdir('.') if f.endswith('.scm')])
    note_limit = int(notes_limit / case_count)
    case_grade = 100/case_count
    for in_file_path in sorted([f for f in os.listdir('.') if f.endswith('.scm')], key=lambda f: int(f[:f.index(".")])):
        result = "#f"
        case = in_file_path.replace(".scm", "")
        print("\tcase_{}...".format(case), end='')
        sys.stdout.flush()
        try:
            print("make..", end='')
            sys.stdout.flush()
            make_output = ""
            make_output = run_sub("make -f ./project/Makefile {}".format(case), timeout, crt_shell=True, err_to_out=True)
            make_output = make_output.decode("utf-8").strip()
            if (re.search(r'fail', make_output) is not None) or (re.search(r'\*\*\*', make_output) is not None):
                output = "make failed\n{}".format(make_output)
            else:
                print("run..", end='')
                sys.stdout.flush()
                output = run_sub("timeout -sKILL {} ./{}".format(timeout, case), timeout, True,
                                 True)
                output = output.decode("utf-8", errors='ignore').strip()
                with open(case + ".out", 'r') as out_file:
                    with open(case + ".cmp", 'w') as cmp_file:
                        cmp_file.write("(equal? '({}) '({}))".format(output, out_file.read().strip()))

                with open(case + ".cmp", 'r') as cmp_file:
                    sys.stdout.flush()
                    print("cmp..", end='')
                    result = subprocess.run(("petite", "-q"), stdout=subprocess.PIPE, stdin=cmp_file,
                                            stderr=subprocess.DEVNULL,
                                            timeout=timeout).stdout
                    result = result.decode("utf-8").strip()

        except subprocess.TimeoutExpired as e:
            output = "Timeout after {} seconds".format(timeout)

        if (result != "#t"):

            if (len(output) > note_limit):
                print("output too long, len(output) = {}".format(len(output)))
            notes += "failed case {}. Output:\n{}\n".format(
                in_file_path.replace(".scm", ""),
                output[:note_limit] + ("..." if (len(output) > note_limit) else ""))
            notes += "\n"
            print("X...", end='')
        else:
            compiler_grade += case_grade
            print("V...", end='')
        print("done")

    if (notes != ""):
        notes += "{}pts per case\n".format(2.5)

    return compiler_grade, notes

def is_readme_valid(sub_id, subdir="."):
    readme_fname = next((f for f in os.listdir(subdir) if f == "readme.txt"), "")
    if (readme_fname == ""):
        return False
    with open(subdir + "/" + readme_fname, 'rb') as readme:
        content = readme.read().decode('ISO-8859-1')
        ids = re.findall(r'\d{7,10}', content)
        if ids is None or ids == []:
            return False
        # else return check_ids(ids, sub_id)
    return True


def grade(sub_id, sub_file, test_cases, test_format, is_final_proj=False):
    cwd = "."
    sub_grade = 0
    notes = ""
    
    # If id is not null, then build a workspace to test it in
    #        Otherwise, test the current workspace '''
    if (sub_id is not ""):
        try:
            setup_sub_workspace(sub_id, sub_file, test_cases, ("/project" if (is_final_proj) else ""))
        except git.exc.GitCommandError as e:
            if (e.status != 1):
                sub_grade = 0
                notes = "Can't run submissions. git apply {} failed with error ({}):\n{}". \
                    format(os.path.basename(sub_file), e.status, e.stderr)
                return sub_grade, notes
        cwd = os.getcwd()
        os.chdir(sub_id)

    if (is_final_proj):
        sub_grade, notes = test_compiler()
        pass
    #else:
        #sub_grade, notes = test(test_format)

    if (not is_readme_valid(sub_id,  ("./project" if (is_final_proj) else "."))):
        sub_grade = 0
        notes += "\nInvalid readme.txt"
    os.chdir(cwd)
    return sub_grade, notes


if __name__ == "__main__":
    print(os.getcwd())
    if (len(sys.argv) < 3):
        print("Comp Grader\nBatch usage:")
        print("\t{} <patch_file> <cases_zip_file>".format(sys.argv[0]))
        exit(-1)
    g, n = grade("structure_test", sys.argv[1], sys.argv[2], "", True)
    if (g < 100):
        print(g)
        print(n)
    else:
        print("OK")
