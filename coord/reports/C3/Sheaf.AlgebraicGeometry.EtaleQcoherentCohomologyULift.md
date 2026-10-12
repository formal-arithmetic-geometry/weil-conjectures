## What changed

The signature and existing docstring of `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift` are unchanged. Its proof now handles degree zero directly with `Sheaf.H.equiv₀` at the terminal étale object and `AddEquiv.ulift`. In positive degree it chooses `X.affineCover.finiteSubcover`, proves its opensRange family covers X and its finite intersections are affine, and applies the new lifted Čech computation. It then uses `cechComparisonMapNaturality`, `moduleCechComparison_isIso_of_affine`, `ShortComplex.mapHomologyIso`, and `etale_zariski_qcoh_comparison` to compose the desired equivalence. The last comparison uses the standard large Ext model; the proof identifies the two Ext models through `Abelian.Ext.homAddEquiv` in one common derived category. These steps all compile in real Lean.

Added `Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison`, with one positive-degree statement computing lifted étale cohomology as the homology of a specified finite-affine section complex. It does not compare two universes of sheaf cohomology. This statement isolates the geometric Čech computation; homology preservation, the unlift, the small-coefficient comparison, and the final composition are proved in the item's module. Updated the item's DAG node to record these actual proof dependencies.

Both modules compile without warnings through `lcompile.py --all`. The first reader's delivery dry run compiled them, ran the declaration/axiom probes, and printed OK. The independent second reading and repairs are recorded below.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_cohomology_ulift`, node `lem-sc-etale-qcoherent-cohomology-ulift`. No `sorry` remains in the item's module. Degree zero is proved directly without the new intermediate theorem.

Added one hole: `AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsSheaf_ulift_finiteCech_succ`, node `lem-sc-etale-qcoherent-ulift-finite-cech-comparison`, in the new module `Sheaf.AlgebraicGeometry.EtaleQcoherentULiftFiniteCechComparison`. Its whole proof is exactly `:= by sorry` and its docstring and node contain the argument. It concerns only positive-degree cohomology, and its other side is the homology of a concrete complex, rather than small étale cohomology. It is strictly the lifted geometric computation in the argument.

This is a decomposition, with one upper hole closed and one lower hole added: net zero holes. The previously stated comparison declarations used in the proof keep their existing holes; none is duplicated, changed, or newly added here. The target does not yet have a sorry-free transitive proof.

Edge cases checked against the new statement: an empty index set is possible only when X is empty, so both complexes and cohomology vanish; F=0 gives zero section complexes; for a one-affine cover positive étale acyclicity agrees with zero positive homology. Repeated cover members cause no problem: the Čech complex includes repetitions and the acyclic-cover computation still applies. Degree n=0 is H¹, not H⁰; degree zero is separately proved in the parent.

## No longer needed

Removed these proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`

The new module also omits the redundant direct imports `Mathlib.Algebra.Homology.ShortComplex.Abelian` and `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`; their declarations remain available through the statement imports. No dependency module is removed transitively.

The parent no longer directly depends on nodes `lem-weil-pbc-module-pullback-quasi-coherent`, `lem-pc-module-pullback-identity-composition`, `lem-sc-etale-affine-qcoherent-succ`, `lem-sc-etale-affine-qcoherent`, or `lem-sc-cech-spectral`; their direct replacement is the new positive lifted Čech comparison plus the existing étale–Zariski and canonical module Čech comparisons. The lifted affine, pullback, and spectral-sequence ingredients remain needed below the intermediate or existing comparison modules. In particular no whole transitive module is claimed pruned: the removed direct imports remain reachable through the comparison theorems. The small affine-succ theorem is not separately needed in the parent proof. Every original public import is retained.

## Where the brief, the DAG or earlier work was wrong

The planned step “the spectral sequence identifies H with Čech homology” is not itself a available Lean comparison declaration. Its existing spectral-sequence statement only provides pages and an abutment. Affine restriction identifications, collapse to the zeroth row, the terminal H'/H identification, and the lifted finite-product complex comparison were not supplied as compiled glue. The new positive-degree theorem makes exactly that geometric computation an explicit next item. The parent proves the algebraic homology comparison from Mathlib rather than leaving the plan's final step implicit.

The small side does not need another new Čech theorem: the already stated étale–Zariski comparison and canonical module Čech comparison supply it. The unit `sk-prop-cd` route is unchanged; this is a tool for its p-primary Artin–Schreier step. The generic canonical Čech comparison nodes are from `sk-lem-picard-cech-computes` and serve as black-box tools; they do not replace the curve unit's route.

While inspecting possible dependencies I found an unrelated unusable signature: `AlgebraicGeometry.etaleCohomologyOverOpen` currently compares global `Sheaf.H G q` on X with global cohomology on an arbitrary open U, rather than `Sheaf.H' G q (Etale.mk j)`. That is false already for H⁰: take X to be two disjoint algebraically closed points, U one summand, and G the direct image of the constant integer sheaf on the other summand. Global sections are ℤ on X and zero on U. This module is not changed by this delivery and is not cited by the new intermediate node's proof. Its incorrect signature needs separate repair. The parent uses the correctly stated étale–Zariski comparison as authorized by this stage.

Sources read: [Stacks 03P2](https://stacks.math.columbia.edu/tag/03P2), separated-case affine-cover computation; [03DW](https://stacks.math.columbia.edu/tag/03DW), part (2) and separated-case proof; [01XD](https://stacks.math.columbia.edu/tag/01XD), affine-intersection Čech comparison. The coefficient-lift elaboration follows that finite-cover computation; the source does not explicitly state a Lean universe comparison. LeanSearch returned Internal Server Error and is recorded as unavailable; LeanFinder, Loogle and grep ran and gave no matching lifted finite-affine comparison. The blueprint search also found no matching universe-lift statement.

## New nodes

`lem-sc-etale-qcoherent-ulift-finite-cech-comparison` is the positive-degree lifted étale Čech computation, stated in `lean/Sheaf/AlgebraicGeometry/EtaleQcoherentULiftFiniteCechComparison.lean`. Its right side is the homology of the image of `(cechComplexFunctor U).obj F.presheafModuleCat` under forget-scalars followed by `AddCommGrpCat.uliftFunctor`. It inherits `sec-curve-estimates` and `sk-prop-cd`, includes its source, complete proof in words and three search kinds, and has no dependency on the parent node. The old parent has no blueprint ancestor recorded (`blueprint.from.node = null`); the new record inherits this null ancestor and names the exact parent proof and unit step in `blueprint.from.place` and `via`, rather than inventing a blueprint declaration. No existing statement, definition, or public interface changed; no change record is needed.


## Second reading by C3

1. **Statements and definitions: PASS.** Compared the parent module and its node with
   the repository using `diff -u`. The original theorem signature and existing docstring
   are byte for byte unchanged; all changes in that module are proof-body or plain
   proof imports. The new module contains one theorem and no definitions. No existing
   public import was changed, no target statement was changed, and no change record is
   required. Checked the existing comparison declarations and relevant change records.
2. **Proof and trust: PASS as a decomposition.** Independently compiled both modules
   in import order through `lcompile.py --all`, without warnings. Scratch-copy
   `#print axioms` checks for both delivered declarations report exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected from the
   explicitly listed geometric hole and the existing comparison theorems. Scanned
   both modules for forbidden constructs: none. The sole remaining `sorry` is the
   complete body of the named new theorem. No data is chosen from an unproved
   existence theorem in a definition: there are no new definitions. The choices of
   comparisons in the parent occur solely inside a proof of a proposition.
3. **Split statement: PASS.** Read the complete new theorem, its docstring and node,
   the lifted affine acyclicity theorem, and the actual spectral-sequence signatures.
   Checked the separated affine-cover argument in [03P2](https://stacks.math.columbia.edu/tag/03P2),
   [03DW](https://stacks.math.columbia.edu/tag/03DW), and
   [01XD](https://stacks.math.columbia.edu/tag/01XD). The new theorem ends at homology
   of a concrete lifted section complex, whereas the original ends at unlifted
   étale cohomology; the compiled parent performs the remaining algebraic comparison.
   It is a proper geometric part of that argument, not a renamed universe-comparison
   statement. Checked empty X/empty cover, F=0, one affine member, repeated members,
   and n=0 (which means H¹). A finite affine cover already implies quasi-compactness,
   so omission of a separate CompactSpace assumption is correct. Independently
   searched with different terms via LeanFinder, Loogle, and msearch grep, and searched
   both library roots with rg. Existing Čech complex isomorphisms compare constructions
   only; they do not supply this lifted geometric computation. No matching complete
   theorem was found, and the geometric hole cannot be closed by those tools alone
   in a short repair.
4. **Route and pruning: PASS.** Read the parent's proof top down: degree zero uses
   terminal sections directly; positive degree uses a finite affine subcover, the new
   computation, the canonical module comparison, exact functor homology, and the
   existing étale–Zariski comparison. Checked the common-derived-category Ext
   identification and equivalence orientations. All five old proof dependencies are
   listed under No longer needed. Removed two redundant direct imports in the new
   module and retained its required statement imports and planned proof imports.
   Checked sk-prop-cd's statement, steps and realized record: the p-primary
   Artin–Schreier step and unit route are retained. No entire transitive module is
   claimed pruned. This remains one hole closed and one added, net zero.
5. **DAG agreement: PASS after repair.** The parent proof steps and four proof_deps
   match the compiled proof. The new node has its full statement, source, proof,
   creation, blueprint, search, chapter/unit and Lean records. Added the existing
   new-sheaf-cohomology-derived-evaluation node to proof step 2 and proof_deps,
   with its plain import. Clarified that the spectral sequence abuts to H': first
   compute that Ext group by free-abelian-Yoneda adjunction on an injective resolution,
   then use the existing terminal derived-evaluation/H comparison. Marked the finite
   product/differential/homology transport as elementary categorical algebra rather
   than a non-elementary step with an empty dependency list.

Second reading changed the new node's dependency and proof explanation, added the
plain derived-evaluation import, removed two redundant imports, clarified the new
theorem's docstring about H', and updated this report. It did not alter either theorem
statement or the parent's proof. Final delivery gates are run after these repairs.
