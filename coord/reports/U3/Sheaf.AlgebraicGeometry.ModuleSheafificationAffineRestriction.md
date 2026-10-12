## What changed

Repaired reviewer X-9171d points A and C1: added the omitted direct user
`Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology` to the change
record, and restored `lem-weil-pbc-affine-opens-basis` and
`lem-weil-pbc-sheaf-morphism-on-basis` in the first proof step and `proof_deps`.
The unused stalk dependency remains removed. No Lean source was changed in this repair.

Completed `AlgebraicGeometry.module_sheafification_iso_of_affine_restriction` with its
original signature. Repaired and finished the earlier attempt's two private helpers:
`affine_cover_dense` and `affine_module_restriction_bijective`. The latter extends
underlying abelian-group maps using Mathlib's dense-subsite hom equivalence and proves
module linearity by separatedness on the affine cover sieve.

Added the proof-only import `Mathlib.Topology.Sheaves.SheafCondition.Sites`. The three
original public imports remain necessary for the statement. Used the module
sheafification adjunction, the restriction bijection, and
`CategoryTheory.isIso_of_coyoneda_map_bijective` to prove invertibility. Parameter
naturality follows from the adjunction and injectivity of restriction. Updated the
proof docstring and the existing node's proof, proof dependencies, and proof origin
to reflect this route.

Read Stacks `sheaves.tex`, `lemma-restrict-basis-equivalence-modules` (Tag 009U) and
the module sheafification universal property (Tag 0089), using the available local
source copy. Read every original dependency's statement and Mathlib declaration.
LeanFinder, Loogle, and grep searches are recorded in `searches.jsonl`; no exact
module-valued comparison theorem was found. The unit record
`sk-thm-picard-duality` has no realized statement or steps affected by this route.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.module_sheafification_iso_of_affine_restriction`
(node `lem-sc-module-sheafification-affine-restriction`).

Both private helpers are proved. The interface-visible `open` change is recorded in
`coord/changes/ModuleSheafificationAffineRestriction.md`. No holes remain in this module, no holes were
added, and no new statements were split off. This is a proof, not a decomposition.
The unchanged theorem allows arbitrary schemes and arbitrary parameter categories;
it assumes neither affine intersections nor quasi-separatedness. The dense-sieve
argument also handles the empty open and the empty scheme by sheaf separatedness.

## No longer needed

Removed proof dependency `lem-weil-pbc-stalk-germs-on-basis`: no stalk or cofinality
argument is used. Its Mathlib stalk lemmas and their module
`Mathlib.Topology.Sheaves.Stalks` are not needed by this proof. This does not assert
that other targets cease to use them. No original imports were removed: all three
are used by the unchanged statement. No Sheaf proof-dependency modules were added.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's scalar-linearity check needed the target module type
specified explicitly, and its naturality equation had the opposite orientation.
Both are repaired. The original DAG's stalk-based invertibility step is unnecessary:
the universal property and the restriction bijection already prove invertibility.
No statement or definition was changed, and no mathematical dispute was found.

## Earlier second reading (a previous round; superseded)

The second reading is assigned to U3. The theorem signature matches the node exactly,
including all universes, arbitrary parameter category, natural isomorphism on affine
opens, and the `Nonempty` conclusion. The proof uses the unit route through affine
basis density and module sheafification; it does not assume affine intersections.
The only open hole in the original module is closed, and no new node or statement is
introduced.


## Earlier second reading (a previous round; superseded)

1. The delivered theorem signature is byte-for-byte unchanged from the repository version; the proof-only import and `open` additions do not alter declarations. Verdict: pass.
2. The file compiles cleanly with `lcompile.py`; it contains no `sorry`, unsafe declaration, or hollow definition. The proof uses only the permitted categorical and sheafification constructions. Verdict: pass.
3. The extension helper proves bijectivity using the cover-dense affine basis and local linearity; no new public theorem or split-off hole was added. The existing node statement is unchanged and the proof is strictly stronger than the old stalk route. Verdict: pass.
4. The unused stalk dependency is removed from the node proof route; all remaining imports are used by the statement or proof. Verdict: pass.
5. The unit record is unchanged and no realized unit statement or step is bypassed. Verdict: pass.

Changed during second reading: corrected the node proof and `proof_deps` to remove the unused stalk dependency, and recorded this review.

## Second reading by U3

1. Compared the delivered Lean module with the repository version. The theorem
   signature is byte-for-byte unchanged; only proof code, proof-only imports, and
   the recorded `open` command differ. Verdict: pass.
2. Compiled the module with `lcompile.py` successfully and checked for `sorry`,
   forbidden declarations, and hollow definitions. None remain. Verdict: pass.
3. Read the proof from the target downward. The affine restriction helper uses
   cover-dense extension and separatedness to establish module linearity; the
   sheafification adjunction and co-Yoneda criterion establish the isomorphism.
   No statement was split off and the target remains exactly as stated. Verdict: pass.
4. Checked pruning against the node: the stalk-germs dependency is unused and
   removed, while the affine-basis and sheaf-morphism dependencies used by the
   first proof step remain. The proof-only Sites import is required. Verdict: pass.
5. Checked the unit record and route. The unit statement and realized route are
   unchanged, and the node proof, dependencies, and origin agree with the Lean
   proof. Verdict: pass.

Changed during this reading: added this review record; no Lean declarations or
mathematical statements were changed.
