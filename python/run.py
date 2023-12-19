
import dendropy


trees = []

with open("./simulated_primates_5X.10.bootstrap.gene.tre") as file:
    for line in file:
        tree_str = "[&R] " + line + ";"
        tree = dendropy.Tree.get(
        data=tree_str,
        schema="newick")
        mrca = tree.mrca(taxon_labels=["13"])
        tree.reroot_at_edge(mrca.edge, update_bipartitions=False)
        
        temp = tree.as_string(schema='newick')[5:-2]

        trees.append(temp)

with open('trees.txt', 'w') as f:
    for line in trees:
        f.write(f"{line}\n")