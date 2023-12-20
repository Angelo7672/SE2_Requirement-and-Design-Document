base_dir = '_RASD/Files/alloy/'

w3 = open(base_dir + "world3.txt", "r").read()
w2 = open(base_dir + "world2.txt", "r").read()

replace_with_minus = ['─']
replace_with_or = ['│']
replace_with_plus = ['┌', '┐', '└', '┘', '├', '┤', '┬', '┴', '┼']
remove_apices = ['⁰','¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹']
bring_down_minus = ['⁻']

for i in replace_with_minus:
    w3 = w3.replace(i, '-')
    w2 = w2.replace(i, '-')

for i in replace_with_or:
    w3 = w3.replace(i, '|')
    w2 = w2.replace(i, '|') 

for i in replace_with_plus:
    w3 = w3.replace(i, '+')
    w2 = w2.replace(i, '+')

for i in range(len(remove_apices)):
    w3 = w3.replace(remove_apices[i], str(i))
    w2 = w2.replace(remove_apices[i], str(i))

for i in bring_down_minus:
    w3 = w3.replace(i, '-')
    w2 = w2.replace(i, '-') 

open(base_dir + "world3_ascii.txt", "w").write(w3)
open(base_dir + "world2_ascii.txt", "w").write(w2)

