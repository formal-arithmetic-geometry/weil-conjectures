## Worker report

The module `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore` states
`SSet.KanQuillen.right_proper_kan_quillen_core`.  It uses the existing
`SSet.KanQuillen.weakEquivalenceStructure` from
`Sheaf.AlgebraicTopology.KanQuillenRightProper`, whose weak maps are the
realization-based `SSet.Enhanced.IsWeakHomotopyEquivalence` from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`.  The only DAG statement
dependency is `def-weil-pbc-simplicial-set`, which is the Mathlib `SSet` leaf.

The first conclusion clause is the existence of a `ModelCategory SSet.{u}`
whose fibrations, cofibrations, and weak-equivalence structure are exactly the
recorded Kan--Quillen structures.  The next two clauses are the functorial
factorizations `(trivialCofibrations, fibrations)` and
`(cofibrations, trivialFibrations)`.  The following clauses render, in order,
cofibrations as monomorphisms, fibrations as `modelCategoryQuillen.J.rlp`,
fibrant objects as exactly `KanComplex`, and trivial fibrations as
`modelCategoryQuillen.I.rlp`.  The next clause is the inclusion of
monomorphisms in transfinite composites of pushouts of coproducts of boundary
generators.  The following equality identifies trivial cofibrations with
retracts of the corresponding horn-cell composites.  The final clause binds
arbitrary `E B B' : SSet.{u}`, `p : E ⟶ B`, and `w : B' ⟶ B`; its hypotheses are
`Fibration p` and `Enhanced.IsWeakHomotopyEquivalence w`, and its conclusion
states the same weak equivalence property for `pullback.fst p w`.

The proof is postponed exactly as `sorry`, with the source argument recorded
in the declaration docstring: the cellular small-object argument gives the two
factorizations and boundary/horn descriptions; geometric realization and the
Serre model structure identify horn cells with weak equivalences; boundary
lifting gives the trivial-fibration characterization; the fibre exact
sequence and monodromy argument prove right properness for arbitrary bases.

I checked the empty simplicial set, the terminal simplicial set, dimension-zero
boundary generators (including the surjectivity condition), positive horns,
identity maps, disconnected bases, and pullbacks with empty fibres.  No
connectedness, nonemptiness, or fibrancy hypothesis was added.

Searches made:

* `msearch.py ... leanfinder "Kan Quillen model structure right proper simplicial sets core theorem"` returned Mathlib's `SSet.modelCategoryQuillen.I`, `.J`, cofibration/fibration instances, `SSet.KanComplex`, and related lifting declarations, but no full model/right-proper theorem.
* `msearch.py ... loogle "SSet modelCategoryQuillen ModelCategory right proper"` returned no match (the query parser also reported the namespace-application diagnostic).
* `msearch.py ... grep "right_proper|RightProper|ModelCategory" AlgebraicTopology/SimplicialSet` found only Mathlib's category-with-fibrations, small-object, and model-category infrastructure; no right-proper theorem.
* `rg` over `WeilConjectures` and `lean/Sheaf` found the parent
  `SSet.KanQuillen.right_proper_kan_quillen` and its canonical weak-equivalence
  structure, but no declaration of this extracted core theorem.

The module compiled cleanly with `scompile.py`; the expected postponed proof is
the only `sorry`.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently clause by clause.  The model
structure witness fixes all three structure fields to the stated canonical
instances.  Every factorization, equality, generator class, fibrancy
characterization, and the final arbitrary-base pullback implication appears in
the same order and with the same universes as the node.  The parent module is
used only for the already recorded weak-equivalence structure; no second
definition of simplicial sets, weak equivalences, boundaries, horns, or Kan
complexes is introduced.  The theorem is statement-only and has no extra
hypotheses or weakened conclusions.  No mismatch or node fault was found.

## Second reading by NG

I read the node statement, its Hovey source place, the dependency declaration, and the
module independently.  The node's objects and clauses are rendered as follows, in order:

1. The ambient object is Mathlib's `SSet.{u}`, the simplicial-set category recorded by
   `def-weil-pbc-simplicial-set`; the module uses `SSet.{u}` throughout.
2. The node's geometric-realization weak homotopy equivalences are the dependency's
   `Enhanced.IsWeakHomotopyEquivalence`; the module fixes the model witness's weak
   equivalence structure to `weakEquivalenceStructure`, whose field is exactly that
   predicate.
3. Existence of the functorial model structure is the first conjunct, with the
   `CategoryWithFibrations`, `CategoryWithCofibrations`, and weak-equivalence fields
   equal to their canonical instances and `weakEquivalenceStructure`.
4. The two functorial factorizations are rendered verbatim by the next two conjuncts:
   `(trivialCofibrations SSet) (fibrations SSet)` and
   `(cofibrations SSet) (trivialFibrations SSet)`.
5. Cofibrations are identified with degreewise injective maps by
   `cofibrations SSet = monomorphisms SSet`; in `SSet`, categorical monomorphisms are
   the degreewise injections used in Hovey Proposition 3.2.2.
6. Fibrations are maps with the right lifting property against every horn, rendered by
   `fibrations SSet = modelCategoryQuillen.J.rlp`; Mathlib's `J` is the horn family.
7. Fibrant objects are exactly Kan complexes, rendered by
   `∀ X, IsFibrant X ↔ KanComplex X`.
8. Trivial fibrations are exactly the maps with the RLP against every boundary,
   including the dimension-zero boundary, rendered by
   `trivialFibrations SSet = modelCategoryQuillen.I.rlp`.
9. Every monomorphism is a transfinite composite of pushouts of coproducts of boundary
   generators, rendered by the displayed `≤` into
   `transfiniteCompositions (coproducts I).pushouts`.
10. Trivial cofibrations are exactly retracts of transfinite composites of pushouts of
    coproducts of horn generators, rendered by the displayed equality with
    `(transfiniteCompositions (coproducts J).pushouts).retracts`.
11. For arbitrary `E B B'`, `p : E ⟶ B`, and `w : B' ⟶ B`, the hypotheses are exactly
    `Fibration p` and `Enhanced.IsWeakHomotopyEquivalence w`, and the conclusion is
    `Enhanced.IsWeakHomotopyEquivalence (pullback.fst p w)`.  No base fibrancy or
    nonemptiness hypothesis is present.

The quantifier order, conjunction order, universe `u`, and pullback orientation agree
with the node.  The source confirms the boundary/cofibration assertion (Proposition
3.2.2), generating horn and model assertions (Theorem 3.6.5), and the realization
fibration/right-proper route (Corollary 3.6.2 and Proposition 2.4.18); the node extracts
these clauses together with right properness.  The existing parent theorem
`SSet.KanQuillen.right_proper_kan_quillen` is stronger because it appends coherent
localization clauses, so it is not an exact existing declaration for this node.

Edge cases checked include the empty simplicial set and empty fibres, the terminal
simplicial set, identity maps, `n = 0` boundary generators (which enforce surjectivity),
positive horns, disconnected bases, and arbitrary characteristic (there is no ring or
characteristic hypothesis).  The statement is uniform in `u` and has no connectedness,
finiteness, nonemptiness, or fibrancy assumptions.

Searches were repeated with `msearch.py` LeanFinder and Loogle queries for a complete
Kan--Quillen model/right-proper theorem, and with `rg` over Mathlib, `WeilConjectures`,
and repository `lean/Sheaf`; they found only Mathlib's category-with-fibrations,
`SSet.modelCategoryQuillen.I/J`, the realization weak-equivalence predicate, and the
stronger parent theorem.  No exact declaration exists.  The dependency's
`weakEquivalenceStructure` and `Enhanced.IsWeakHomotopyEquivalence` were opened and
match the node's definitions.  No statement mismatch was found. The proof docstring was too compressed for H8;
I expanded it into all six node steps and named their dependencies. The Lean
signature and node were unchanged. I also added the required non-public imports
for all recorded proof dependencies (including Mathlib leaves); the parent import
remains public because it owns the canonical weak-equivalence structure.  `scompile.py` compiled the module and sandbox copy cleanly; the only postponed
proof is the declared `sorry`.

Independent search details: LeanFinder query "simplicial sets weak equivalences stable
under pullback Kan fibration functorial model category" returned the canonical
fibration/cofibration instances and general stability lemmas, but no full theorem.
Loogle query `"SSet", "ModelCategory"` returned only the canonical map classes and
`I`/`J` declarations. LeanSearch query "simplicial set Kan Quillen right proper model
structure" returned KanComplex and the same classes. Direct Mathlib `rg` searches for
`RightProper|rightProper|right_proper|instance.*ModelCategory` found generic opposite
over-category structures only. The full upstream `WeilConjectures` search for the
right-proper spellings returned no hits, and the project's search located the stronger
parent. No new nodes or dependency-module deliveries were needed.

## Maintainer review fix (cc reviewer, 2026-10-17)

The statement was correct, but the module `public import`ed the parent module
`Sheaf.AlgebraicTopology.KanQuillenRightProper` only to use `weakEquivalenceStructure`.
The parent node `lem-coef-kan-quillen-right-proper` has this core node in its
`proof_deps`, so in stage 3 the parent module must import this module (stage-2 rule 7).
That would make an import cycle. The fix removes the parent import. It installs the same
realization weak-equivalence structure in the statement with
`letI : CategoryWithWeakEquivalences SSet.{u} :=
⟨fun _ _ f ↦ Enhanced.IsWeakHomotopyEquivalence f⟩`, which is the definition of
`weakEquivalenceStructure` written out, so no new declaration is introduced. The
witness's weak-equivalence field is now compared with `inferInstance`, and the
Mathlib modules the statement uses are imported publicly. All ten clauses, the
quantifiers and the universes are unchanged. A test file checked that the parent's first
ten conjuncts give the fixed statement, and that the fixed statement gives back the
`weakEquivalenceStructure` forms. A copy of the parent module that also imports this
module compiles, so the cycle is gone.
