import re

ls = []
with open("./species_tree") as file:
    for line in file:
        ls.append(line)
print(ls[0])

output_string = re.sub(r'[0-9:.]+', '', ls[0])

print(output_string)