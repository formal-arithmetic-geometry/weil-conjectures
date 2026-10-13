## What changed

Completed the proof of `additiveCech_common_representative` with its original signature.
It now combines two independently stated results: alpha sends a global cycle to a
specified total cycle, and beta represents an arbitrary total homology class.
Both results have complete Lean proofs in new modules. The remaining geometric
comparison is stated separately in `EtaleAdditiveCechBetaQuasiIso`: the fixed beta
components extend to a quasi-isomorphism from the lifted coefficient complex.

The alpha proof computes both terms of the total differential. The horizontal
term cancels because the two restrictions of a global section agree, and the
vertical term vanishes by resolution-differential naturality and `iCycles_d`.
It uses `liftCycles` and `liftCycles_i` to give the exact required inclusion.

The beta representative proof takes the inverse image of an arbitrary total
homology class, lifts it through the surjection `homologyπ`, lowers the resulting
ULift cochain, constructs its ordinary coefficient cycle using `cyclesMk`, and
uses `cyclesMap_i` and `homologyπ_naturality` for the two required equations.
The target proof then applies this to the class of its alpha cycle.

All four modules compile in import order. The original covering hypothesis is
explicitly retained as a local fact in the target proof because it is not needed in this direction;
its binder remains unchanged. No existing definition or statement was changed. Only proof imports were added
to the target module. The existing target node's proof route was updated, and
three new nodes match the three new modules.

Validation: `deliver3.py Y3
Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCommonRepresentative --no-push`
printed OK for commit `b1bb37ef0d`: compilation and preflight passed, except for
the independent second-reading section that the next worker supplies. Nothing
was pushed. The explicit axiom check in `scratchpad/axioms.log` confirms that
`additiveCech_alpha_representative` uses only `propext`, `Classical.choice`, and
`Quot.sound`; the beta representative and target additionally use the expected
`sorryAx` from the sole staged beta quasi-isomorphism.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.additiveCech_common_representative`
(node `new-w2-additive-cech-common-representative`).

Also proved the new declarations:
`AlgebraicGeometry.Scheme.Modules.additiveCech_alpha_representative`
(node `new-w2-additive-cech-alpha-representative`) and
`AlgebraicGeometry.Scheme.Modules.additiveCech_beta_representative`
(node `new-w2-additive-cech-beta-representative`).

Added exactly one remaining hole:
`AlgebraicGeometry.Scheme.Modules.exists_additiveCech_beta_quasiIso`
(node `lem-pbc-additive-cech-beta-quasi-iso`). Its complete natural-language
argument, source, coordinate normalization, and edge cases are in its docstring
and DAG node. This is a decomposition with one hole closed and one hole added,
not a claim of an axiom-free proof of the original target. The remaining hole
is specifically affine beta comparison, with no alpha or global-cycle assertion.

## No longer needed

No original import was removed: `EtaleAdditiveCechNormalization` is needed for
the unchanged statement and definitions. No unused proof import is retained. The draft redundant proof import
`Mathlib.Algebra.Homology.ShortComplex.Ab` was removed because it is already
publicly imported by `Mathlib.Algebra.Homology.ConcreteCategory`. The draft
redundant public imports `Mathlib.Algebra.Category.Grp.Ulift` and
`Mathlib.Algebra.Homology.QuasiIso` were also removed from the beta comparison
module; normalization already exposes the symbols its statement uses.

Pruned from this item's direct proof route:
`lem-sc-etale-open-cech-injective-augmentation`, module
`Sheaf.AlgebraicGeometry.EtaleOpenCechInjectiveAugmentation`.
The alpha quasi-isomorphism, exact augmented injective Cech rows, and
restriction preserving injectives are unnecessary for this direction: only
alpha preserving cycles is used, and that is proved directly. This is a local
route pruning; the module may remain reachable through other target branches.

`lem-sc-etale-affine-open-cech-resolution-columns` and its module are still
needed in the remaining beta comparison plan, so they are not claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan establishes alpha as a quasi-isomorphism, which is
stronger than this statement needs. The Lean signatures of the planned row and
column theorems do not identify the concrete alpha and beta components used in
this statement: the row theorem requires an explicit augmentation and the
column theorem gives abstract homology isomorphisms. Consequently neither is a
direct substitute for the fixed augmentation equations. The revised route
proves the alpha equation directly and isolates the exact coordinate-normalized
beta comparison needed for the remainder. It does not use the reverse
cycle-realization theorem, a normalized edge equivalence, or scalar transport.

The new beta comparison is valid even without a covering condition. The new
alpha lemma needs no finiteness, affineness, covering, compactness or separatedness.
Degree zero, empty index sets, empty intersections, and repeated opens are
covered by the same proofs and comparison argument. The unit route remains
the Artin-Schreier structure-sheaf augmentation comparison inside `sk-thm-p1`.

## New nodes

`new-w2-additive-cech-alpha-representative`, in
`EtaleAdditiveCechAlphaRepresentative`, records the proved restriction-cycle
calculation for arbitrary open families and global resolution cycles.

`new-w2-additive-cech-beta-representative`, in
`EtaleAdditiveCechBetaRepresentative`, records the proved homological reduction
from the beta quasi-isomorphism to representatives of arbitrary total classes.

`lem-pbc-additive-cech-beta-quasi-iso`, in
`EtaleAdditiveCechBetaQuasiIso`, records the sole remaining geometric obligation:
the actual lifted coefficient augmentation with the prescribed beta coordinates
is a quasi-isomorphism on affine intersections. It asserts no common alpha/beta
representatives and is not a renaming of the original theorem.

## Second reading by Y3

1. **Statements and signatures.** Compared the delivered target module with the
repository version byte for byte at every declaration. The target signature and
all existing declarations are unchanged; the two added proof imports are plain
imports. Verdict: pass.

2. **Proof and axioms.** Compiled all four modules in import order with
`lcompile.py --all`. The alpha and beta representative proofs contain no
unfinished subproofs. The only `sorry` is the named theorem
`exists_additiveCech_beta_quasiIso`, whose statement is a separate public split
node with a source and proof sketch. The probe reports only the permitted three
axioms for alpha; beta and the target depend on the explicitly listed
`sorryAx` from that split theorem. No forbidden declaration or hollow definition
was found. Verdict: pass, with the documented split hole.

3. **New statements.** Checked the alpha and beta representative statements
against their definitions and the cited Stacks arguments. Alpha is strictly the
cycle equation needed by the target. Beta is the homology-class realization
needed by the target and fixes the beta coordinates. The quasi-isomorphism split
is strictly lower than the original common-representative claim and is not a
renaming of it. Edge cases (degree zero, empty families, repeated opens and
empty intersections) are covered by the same categorical identities. Verdict:
pass.

4. **Pruning and route.** The target proof uses exactly the alpha and beta
representative modules. The old injective-Cech-row dependency is no longer used
and is recorded under `No longer needed`; normalization remains the public
statement dependency. The beta comparison retains the affine-column route.
Verdict: pass.

5. **DAG and unit.** The target node's proof and `proof_deps` match the Lean
proof, and each new declaration has a matching node and report entry. The unit
record `sk-thm-p1` and its realized route are unchanged. Verdict: pass.

I changed only this second-reading report section; no Lean statement, definition,
or proof was altered during review.
