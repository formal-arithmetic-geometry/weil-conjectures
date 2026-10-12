## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.small_perfectComplex_classes_of_isAffine`
without changing its statement. The proof constructs a universe-u type `FiniteTermModel A`:
integer-indexed `FGModuleRepr A` objects, module-category differentials, and proof fields
for shape and square-zero identities. The private proved lemma `exists_finiteTermModel`
conjugates differentials along Mathlib's `FGModuleRepr.ofFiniteEquiv` and constructs a
complex isomorphism with `HomologicalComplex.Hom.isoOfComponents`.

The final proof maps these models to the ambient derived skeleton. Its range is small.
The composite of the two full-subcategory inclusions induces an injective map on
skeletons. Every perfect class belongs to the range by its finite-term presentation,
so `small_of_injective` proves the original result. No local smallness of derived
morphism spaces and no relation between universes u and w is used.

Added `Sheaf.AlgebraicGeometry.PerfectAffineFinitePresentation`. Its auxiliary public
`affineModuleComplexFunctor` is an explicit termwise tilde/pushforward construction,
with its zero-map obligation proved. Its one theorem isolates the geometric presentation
step for arbitrary affine Y. This is strictly part of the original argument: it states
an actual module-complex presentation, with no type-smallness or skeleton assertion.
The remaining encoding and full-subcategory argument is proved here.

Mathlib's finite module representatives are constructed from **proved** finite-module
quotient equivalences. No definition selects data from the new unproved presentation
theorem. That theorem's witness is used only within the proof of smallness.

Both delivered modules compile cleanly through lcompile.py, in import order. The item
retains its original public imports. Added proof-only imports of the presentation module
and Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.small_perfectComplex_classes_of_isAffine`
(node `lem-pc-perfect-affine-classes-small`). No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.exists_affine_finite_module_presentation`
(node `lem-pc-perfect-affine-finite-presentation`). Its proof is exactly `by sorry`.
Its docstring and node give the affine-isomorphism transport, including restriction,
finite free retractions, quasi-coherence, and derived localization comparisons, followed
by the existing `perfect_iff_affine_bounded_projective`.

This is a decomposition: one hole closed and one added, net zero. The finite-term
encoding, conjugation of differentials, and skeleton injection are complete Lean proofs.
The imported `AlgebraicGeometry.perfect_iff_affine_bounded_projective` is unchanged
and remains a separate existing item; its hole is not added by this delivery.

## No longer needed

Removed the item's direct proof-only imports of
`Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective` and
`Sheaf.AlgebraicGeometry.DerivedCategory`.
The former remains a planned proof dependency of the new geometric presentation lemma;
the latter's definitions remain available through the unchanged public PerfectComplex
import. Neither module is globally pruned by this delivery.

The smallness proof does not require bounds on degrees, projectivity, idempotent matrices,
or an encoding of direct summands. It uses the larger small family of all complexes with
finite terms. No existing dedicated node or module for these discarded encoding details
was imported, so no other existing node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The existing affine bounded-projective criterion is stated only for literal Spec A,
whereas this item quantifies over arbitrary affine Y. The missing derived and perfectness
transport is not an application by definitional equality. The new presentation lemma
isolates precisely this geometric gap and retains the existing criterion as its input.
No existing definition or statement was changed, and no statement is disputed.

The unit record `sk-thm-picard-duality` has empty realized statement and step lists.
The route through the affine perfect criterion is retained; no binding unit node is
bypassed. The old proof's finiteness argument can be enlarged to arbitrary finite-term
complexes: integer-indexed data remain universe-u small, so boundedness is unnecessary
for that encoding, although it remains in the geometric source criterion.

The local literature/stacks-project/perfect.tex file is absent on this machine. The
source was read at https://stacks.math.columbia.edu/tag/08EB; the delivery uses the
existing recorded source and expands its affine-isomorphism transport. Blueprint searches
for 'perfect affine' and '08EB' found no separate arbitrary-affine presentation statement;
the existing bounded-projective node was checked. Mathlib and upstream source greps
found no perfect-affine presentation result. LeanFinder returned only morphism-property
isomorphism-invariance results, and LeanSearch reported Internal Server Error.

## New nodes

`lem-pc-perfect-affine-finite-presentation` records the only new hole: every perfect
quasi-coherent object on an arbitrary affine scheme has a finite-term module-complex
presentation under the specified functor. Small cases include the zero ring, zero
complex, and empty affine scheme; there is no nonzero, nonempty or degree-bound
assumption. For the zero complex choose P = 0; for an empty affine scheme the sheaf
category is the zero category and this same presentation applies. The literal Spec A
case follows from the existing bounded finite projective criterion and the canonical
isomorphism functor comparison. The proof retains that criterion's route.

`def-pc-affine-module-complex-functor` records the auxiliary explicit construction in the
same new module. It has no hole and makes no choice from unproved existence. Its data
are termwise tilde followed by SheafOfModules.pushforward along Y.isoSpec.inv.

No change record is needed: existing public signatures, definitions, and public imports
are unchanged. The new nodes are in the item's chapter and unit. The original node's
proof, proof_deps and proof_origin have been updated to match the Lean proof.

## Second reading by Y2

1. **Interface unchanged.** Compared `PerfectAffineClassesSmall.lean` with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body differ. The added module contains the explicitly recorded new definition and presentation theorem.

2. **Proof validity.** Compiled both delivered modules in import order with `lcompile.py --all`; compilation succeeds with no errors. The target has no `sorry`; the only remaining `sorry` is the named theorem `exists_affine_finite_module_presentation`, with its matching node and proof docstring. No forbidden declarations or hollow definitions occur. The explicit functor is a genuine termwise construction and its zero-map obligation is proved.

3. **Statements and nodes.** Checked the target and new declarations against their DAG node statements, proof dependencies, and source/proof-origin records. The new presentation statement is a strict geometric reduction (finite-term presentation), not a restatement of the target. Its edge cases include zero complexes, zero rings, and empty affine schemes as documented. No existing library or Mathlib declaration duplicates the new results according to the recorded searches.

4. **Pruning and route.** The target proof uses the finite-term encoding, the presentation theorem, and the skeleton injection exactly as recorded. Removed direct proof-only imports of `PerfectAffineBoundedProjective` and `DerivedCategory`; the remaining imports are used. The affine perfectness route is retained through the split presentation theorem, and the unit route is unchanged.

5. **Changes made.** No code or statement repair was needed after review. Added this second-reading report section only; the delivered files already compile and the DAG records agree with the Lean code.
