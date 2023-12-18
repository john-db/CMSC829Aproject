from phylo2vec import vecToNewick, sequence
import dendropy
from compare_two_trees import compare_trees

def medians(ls):
    #ls: list of phylo2vec vectors, all of length n >= 2

    most_seen = [[0], [0]]

    for i in range(2, len(ls[0])):
        occ = {}
        for j in range(0, len(ls)):
            val = ls[j][i]
            if val in occ:
                occ[val] += 1
            else:
                occ[val] = 1
        s = sorted(occ, key=occ.get, reverse=True)
        temp = [s[0]]
        for i in range(1, len(s)):
            if occ[s[0]] == occ[s[i]]:
                temp.append(s[i])
            else:
                break
        most_seen.append(temp)

    return sequence(most_seen)

def rf_newicks(n1, n2):
    taxa = dendropy.TaxonNamespace()

    tree1 = dendropy.Tree.get(data=n1 + ";",
                              schema='newick',
                              rooting='force-unrooted',
                              taxon_namespace=taxa)

    tree2 = dendropy.Tree.get(data=n2 + ";",
                              schema='newick',
                              rooting='force-unrooted',
                              taxon_namespace=taxa)
    
    temp = compare_trees(tree1, tree2)
    return temp[3] + temp[4]
    
    

