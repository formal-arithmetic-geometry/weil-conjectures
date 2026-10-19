# Stage-1 report: lem-coef-operadic-approximation-marked-equivalence

Files written:

- `dag/nodes/sec-six-functors/lem-coef-operadic-approximation-marked-equivalence.json` — statement, split proof, no new Mathlib leaf.
- `citations.json` — verbatim statement quotes for every proof-step citation.
- `searches.jsonl` — the required msearch.py records, including the additional queries run during this repair.

Attachments: none. No sorry-free declaration with this exact statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or the master reference source.

WANTED: Lurie, Higher Algebra (2017), Definitions 2.3.3.6 and 2.3.3.25, Lemma 2.3.3.10, Theorem 2.3.3.23(1), Proposition 2.1.4.6 and Remark 2.3.3.27, for the marked-operadic approximation theorem. The PDF is cited by the imported node but is not archived in `literature/`.

## Source error

The inherited step 7 said that the map
`Hom(Fin_*(<m>,<n>)) -> product_i Hom(Fin_*(<m>,<1>))`
is a bijection because a pointed map is determined by its colour projections. This is false as stated: arbitrary tuples of pointed maps need not have a common value on every input, whereas a single pointed map has compatible components. I corrected the argument to take the homotopy fibre over each fixed base arrow `phi`; on that fibre the displayed comparison is exactly the product of fibres over the prescribed composites `rho_i phi`, and no false surjectivity claim is used. The target statement is unchanged.

## Review by Q106

I read the item node, its unit and chapter records, the imported blueprint proof paragraph, and every statement cited by all seven steps. The item hypotheses are unchanged: an approximation is witnessed by a categorical equivalence followed by a categorical-fibration approximation with locally cocartesian inert colour projections and cartesian lifts of active edges, and the original strict unary fibre is an equivalence. I checked the edge cases `n=0`, empty colour fibres, identity approximations, nullary operations, and the empty discrete colour-projection family.

Step 1 uses the existing symmetric inert-active orthogonality statement for the coherent inert/active factorization and the existing symmetric weak-approximation-algebras statement for the exact definition of `F_g(d,alpha)` and its two required clauses. Step 2 uses the orthogonality mapping-space pullback, the cocartesian mapping criterion, the cartesian/cocartesian definitions under opposites, and the relative-cone opposite mapping identification; each cited statement supplies the corresponding mapping-space or lifting assertion. Step 3 now first verifies that `F_g(d,alpha)` is a quasicategory: the slice right-fibration node supplies the slice quasicategory, the ordered coslice left-fibration node supplies the pullback left fibration, and inner-horn filling is inherited from the base. It then uses the normalized-final-cone statement to contract the factorization category and the weak-approximation-algebras statement to conclude weak approximation. Step 4 applies precisely the algebra-category equivalence in the weak-approximation-algebras node to an arbitrary symmetric infinity operad `Q`; it explicitly distinguishes the local-projection subcategory from the all-inert marked functor subcategory. Step 5 uses the same node's ambient relative-functor equivalence, the cocartesian mapping criterion for invariance of inertness under arrow equivalence, and pointwise equivalences for natural-transformation components. Step 6 uses the categorical-pattern model-calculus Hom description, the marked product/Map-sharp definition, and symmetric-operadic fibrancy to identify the marked mapping objects with the cores of the two algebra categories. Step 7 uses pointwise equivalences for the core homotopies, the categorical-pattern weak-equivalence test, the categorical-pattern fibrancy definition, the relative-cone definition, and its constant-source test. I repaired the false base-map surjectivity assertion in this step by working over one fixed pointed map `phi` and taking its homotopy fibre; the corrected sentence uses only the cited relative-cone and mapping-space statements.

I searched the whole DAG and blueprint before retaining the two supporting nodes; both already exist on the shared DAG, so this delivery creates no new node and has no duplicate pair. I checked the two supporting statements directly, including their hypotheses and their existing reviews. The only Mathlib hits were generic model-category weak-equivalence predicates, polynomial-functor approximations, and ordinary fibre-category declarations; none states this symmetric infinity-operadic theorem. The required LeanFinder, LeanSearch, Loogle, and Mathlib-source grep searches were run through `msearch.py` and recorded verbatim. No SGA source is used.
