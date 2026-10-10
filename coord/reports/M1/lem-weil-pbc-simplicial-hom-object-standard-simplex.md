# lem-weil-pbc-simplicial-hom-object-standard-simplex

## Worker result

Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-simplicial-hom-object-standard-simplex.json`: filled the five-step proof, proof dependencies, document proof origin, and split report; status is now `split`.
- No new nodes. All auxiliary facts are already stated by existing DAG nodes.

Attachments:

- None. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the item id, standard-simplex Hom terminology, matching-object terminology, and the blueprint tag found no sorry-free declaration (or any declaration) stating this item.

WANTED: none.

What was wrong or incomplete:

- The imported item had an empty proof and `status: unsplit`. I supplied the missing arguments from Stacks 0177, 018V, and 0186.
- No statement change was needed. I retained the existing blueprint fields and Mathlib search record.
- No source error or unfinished step was found.

## Review by M1

I read `simplicial.tex` in the local Stacks checkout `/home/ubuntu/c1-stacks-review`: Example \`Delta[n]\\`, Definition 0175, Lemma 0177 (`lemma-simplex-map`), Lemma 0186 (`lemma-formula-limit`) and Lemma 018V (`lemma-cosk-shriek`), together with the face factorization and face relations in Lemmas 0166 and 0167. I also read the existing DAG statements `def-weil-pbc-simplicial-set`, `def-weil-pbc-simplicial-object`, `def-weil-pbc-simplicial-hom-object`, `lem-weil-pbc-simplicial-matching-object`, `lem-weil-pbc-simplex-face-factorization`, `lem-weil-pbc-simplex-face-face-identity`, and `lem-weil-pbc-matching-object-proper-faces`. Each cited node says the fact used in the corresponding step.

Step 1 checks the finite nonempty sets of order-preserving maps, the characterization of nondegenerate maps as injective, and the boundary cases. The only imported notion used is the simplicial-set/degeneracy definition. I checked (n=0), (n=1), (m>n), constant maps, and the empty boundary \`partial Delta[0]\\`; these give the claimed edge cases.

Step 2 follows Stacks 0177. The simplicial-object node supplies contravariant functoriality, and the Hom-object node supplies the representing universal property. Evaluation at \`id_[n]\\` gives both existence and uniqueness of the representing morphism.

Step 3 follows the construction in Stacks 0186/018V. The face-factorization node gives \`varphi=delta_i\\circ psi\\` for a missing vertex and uniqueness for fixed (i); the face-identity node gives independence of two choices; the simplicial-object node supplies functoriality. The matching-object node (and the existing proper-face matching node used in the explicit comparison) states exactly that compatible tuples are represented by (M_n(K)). I checked the (n=1) case separately: there is no pairwise compatibility equation, and the two-choice independence argument is only used when (n\\ge2).

Step 4 constructs \`theta\\` from the universal boundary family and the matching-object universal property, constructs its inverse by extending the tuple of projections, and verifies both composites by the two universal properties. Thus the proof does not appeal to an unstated Yoneda theorem.

Step 5 uses the Hom-object universal property to define \`rho\\`. The projection equations for \`theta\\circ rho\\` and \`mu_n\\` are both (d_i), so the matching-object uniqueness clause gives the equality. I checked that the family (K(\\varphi)) is compatible by contravariant functoriality.

The item’s existing Mathlib searches were re-read: LeanSearch, LeanFinder, and Mathlib-source grep only find simplicial-set Yoneda/boundary APIs, not Hom objects into an \`SR(X)\\`-valued simplicial object or matching objects. Therefore the item is not a Mathlib leaf. No new node was created, so there are no new Mathlib leaves or unsplit statements to audit. Blueprint search for “simplicial hom object standard simplex boundary matching” found no same-as node; the split report’s blueprint entry points to the fourth paragraph of `lem-weil-pbc-hypercover-refinement`, where the restriction is identified with (K_n\\to M_n(K)).

