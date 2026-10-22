## What changed

Proved `SheafOfModules.ExactPullbackSigned.exact_pullback_signed_comparison`
with its original statement. Uniqueness of left derived functors supplies the
normalized identification with the exact derived functor. The existing canonical
shift-unit theorem supplies the unique tensor comparison and its separate-input
shift equations. Private category calculations combine these into the simultaneous
shift equation, transport the comparison through the identification, and prove
symmetry and associativity first on resolving models and then on all inputs.

The proof uses the existing normalized derived-tensor constraints rather than
constructing them again. It imports `DerivedTensorAdditiveConstraints`,
`TensorColimitsIndependentCoefficients`, and Mathlib's pointwise-derived API.
The first import is public because the repaired model predicate uses its public
model and representative definitions. The node records the actual proof route.

A compilation repair names the four proof-field conditions of `TensorConstraints`
and gives its associativity-model condition the equivalent bundled interface of
`DerivedTensorConstraints.Model`, `totalModel`, and `representative`.
The record retains its six fields and its mathematical meaning. A separate Lean
check proves both implications with the original condition. Three proved public
lemmas cache existing propositional cochain tensor instances; they are instances
only locally. The six original tensor, shift, exact-functor, factorization and
identification definitions are unchanged. The change record is
`coord/changes/exact-pullback-tensor-constraint-predicates.md`.

All proofs remain in the original module. Local instance-search and transparency
settings avoid unfolding large totalization constructions. No adopted source file
or target declaration is changed, and there are no forced consumer adaptations:
the downstream scan found no current Lean importers.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.ExactPullbackSigned.exact_pullback_signed_comparison`
(node `lem-pur-exact-pullback-signed-comparison`). The delivery adds zero holes,
splits off zero statements, and leaves zero `sorry`s in its module. All generic
helpers and the three cache lemmas are proved. Existing imported theorems retain
their own proof obligations; they are used as the stage-3 brief prescribes.

The complete canonical-interface proof compiled through `lcompile.py` in 53.1
seconds. Expanding the equivalent bundled model predicate reduced the checked
constructor-and-model prefix from 36.0 to 25.6 seconds; the final old/new
condition equivalence passed in 23.9 seconds. The production module has the same
completed proof and no holes. The mandatory delivery compile verifies this packet;
several earlier production checks reached the single-file limit, which motivated
the recorded definition and private functor-interface repairs.

## No longer needed

Removed direct proof imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback` and
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.

The proof route and obsolete tool-use entries no longer invoke:

- `lem-weil-pbc-ringed-topos-flat-module-pullback`: resolving pullback applied to a
  flat sheaf in degree zero proves the flatness assertion directly. The old flat
  pullback module remains a transitive dependency of K-flat pullback.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: the actual adjunction is already
  a field of `RingedPullback`, namely `moduleAdj`.
- `lem-weil-pbc-ringed-topoi-derived-pullback`: uniqueness of left derived functors
  gives the identification without invoking another construction of pullback.
- `lem-weil-pbc-site-derived-tensor-descent`: resolving representatives and
  naturality give pair and triple extensionality directly. Its tensor definitions
  and transitive statement dependencies remain in use.
- `lem-weil-pbc-total-tensor-integer-shifts`: the separate-input shift equations,
  naturality and the shift addition law imply the simultaneous-shift equation.

The definition nodes `def-pc-kflat-complex`, `def-pc-flat-sheaf-modules`, and
`def-pc-tensor-complex-sheaves` are no longer separate proof steps; they remain
statement dependencies. No module or declaration is withdrawn, and no unit route
is bypassed. The new direct dependency
`lem-pur-derived-tensor-additive-constraints` supplies the existing normalized
associator, symmetry and resolving-model closure. The existing
`siteSheafTensorRightIso`, from
`lem-weil-pbc-independent-sheaf-tensor-colimits`, identifies the two flatness APIs.
No new tool approval is inserted.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is valid. It reconstructs several pieces already
available from localization and the normalized derived-tensor constraints, so the
proof uses those shorter routes. The original expanded record interface caused
repeated unfolding of cochain totalization during type checking. The equivalent
bundled model condition and cached propositional instances repair that issue;
the change record includes the old and new definitions and the checked
implication proofs for independent statement review.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
