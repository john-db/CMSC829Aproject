from phylo2vec import newickToNaive, naivetovec, vecToNewick
from median import medians, rf_newicks


trees = []
with open("trees.txt") as file:
    for line in file:
        trees.append(line)

trees_newick = trees
trees = map(newickToNaive, trees)
trees = list(map(naivetovec, trees))

my_medians = medians(trees)
my_medians = list(map(vecToNewick, my_medians))

for s in my_medians:
    print(s)

def score_tree_rf(tree, trees):
    val = 0
    for newick in trees:
        val += rf_newicks(tree, newick)
    return val

my_med = my_medians[0]
print("our median output: " + str(score_tree_rf(my_med, trees_newick)))

astral_output = "(0,(1,((6,7),(10,((3,9),(11,((2,8),((5,(12,13)),4))))))))"
print("astral's rf score: " + str(score_tree_rf(astral_output, trees_newick)))


# scores = list(map(lambda tree: (tree, score_tree_rf(str(tree), trees_newick)), my_medians))
# my_min = min(scores, key = lambda x: x[1])
# mins = filter(lambda x: x[1] == my_min, scores)
