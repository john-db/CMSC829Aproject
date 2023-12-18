from median import medians
from median import rf_newicks
from phylo2vec import vecToNewick, phylovecdomain
from collections import defaultdict
from functools import reduce

def score_tree_rf(tree, trees):
    val = 0
    for newick in trees:
        val += rf_newicks(tree, newick)
    return val

#################

ls = [
    [0,0,0,0,0,0,0,0,14],
    [0,0,2,4,6,8,10,12,14],
    [0,0,0,4,0,8,0,12,14],
    [0,0,2,0,6,0,10,0,14],
    [0,0,2,4,6,8,0,0,14],
    [0,0,0,0,0,0,10,12,14]
]

trees = list(map(vecToNewick, ls))
newicks_medians = list(map(vecToNewick, medians(ls)))

def count_values(dictionary):
    value_count = defaultdict(int)

    for value in dictionary.values():
        value_count[value] += 1

    return value_count

dists = {}
for m in newicks_medians:
    dists[m] = score_tree_rf(m, trees)

bests = []
best_score = 9999
i = 0
for v in phylovecdomain(8):
    print(i / reduce(int.__mul__, range(2*(8) - 3, 0, -2)))
    i+=1
    u = v + [14]
    n = vecToNewick(u)
    score = score_tree_rf(n, trees)
    if score < best_score:
        best_score = score
        bests = []
    elif score == best_score:
        best_score = score
        bests.append(n)

for best in bests:
    print(best)
    print(best in newicks_medians)
    print(score_tree_rf(best, trees))
    


print(count_values(dists))