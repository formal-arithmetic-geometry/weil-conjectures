## What changed

Replaced the target hole with a proof unpacking the comparison predicate, obtaining
invertibility of its counit component, and composing with the localized single-map
isomorphism. Added the affine-local flatness intermediate and proved the flat-single counit helper
from flatComplexDerivedPullback and Mathlib left-derived uniqueness.

## Proved and sorry left

Closed AlgebraicGeometry.isIso_modulePullbackComparison_of_isFlatOver_identity by
reduction (one hole closed, one added; this is a decomposition).
Also proved AlgebraicGeometry.isIso_flat_single_derived_counit completely from existing
named dependencies.
Holes added: AlgebraicGeometry.isFlat_of_isFlatOver_identity. Net holes closed minus added: 0.
The new counit helper has no local hole, but still depends on open upstream theorems.
Remaining holes:
- AlgebraicGeometry.isFlat_of_isFlatOver_identity
  (lem-pc-intrinsic-flat-module-tensor-flat).
No sorry remains in the target module. All three files compile together.

## No longer needed

Removed the target's direct import of Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback.
The proved helper also avoids imports of DerivedModuleBaseChangeMap and DirectImage.Basic;
its statement needs only DerivedPullback and sheaf flatness.
The old proof dependency lem-pc-flat-complex-derived-pullback is replaced in the target node
by lem-pc-flat-single-derived-counit, which still uses it. The other old dependency,
def-pc-derived-module-base-change-map, remains directly used. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies do not directly state the affine-local to tensor-flatness
bridge. This is now a separate item. The universal-property transport is proved. No existing signature or definition changed.

## New nodes

lem-pc-intrinsic-flat-module-tensor-flat: the affine-local flatness bridge, independent
of the morphism or derived category.

lem-pc-flat-single-derived-counit (proved): invertibility of the counit at a tensor-flat single
module, independent of the module-comparison predicate and affine-local flatness.

## Second reading by R3

1. Compared every delivered module with the repository. Only the target module existed;
   its declaration signature and docstring are byte-for-byte unchanged. Its changes are
   proof-only imports and its proof. Both added modules contain new theorem statements,
   no definitions. No interface change record is required.
2. Compiled all three modules in import order with lcompile.py (17.4, 5.7, 7.3 seconds).
   The only local sorry is the named isFlat_of_isFlatOver_identity. A scratch-copy
   #print axioms probe of all three declarations reports propext, Classical.choice,
   Quot.sound and sorryAx only. There are no forbidden declarations or hollow definitions.
3. Read IsFlatOver and IsFlat definitions and checked Stacks 01U4 and 05NE:
   equal affine opens give coordinate-ring flatness, localization gives stalk flatness,
   and stalkwise exactness gives tensor flatness. No finite-generation or nonemptiness
   hypothesis is needed. Zero modules and empty schemes satisfy the statement.
   This bridge is strictly smaller than the derived comparison target. The counit helper
   separately proves the derived part, including single-term and zero-term flatness and
   Mathlib's universal-property factorization. Independent leanfinder, loogle and grep
   searches found ring-module exactness criteria but no duplicate sheaf bridge; local
   library and upstream searches agree. The existing flat_stalk_of_isFlat proves the
   reverse direction and cannot close this hole. Closing it requires additional affine
   localization and stalkwise exactness work, not a short existing-lemma application.
4. The proof uses flatComplexDerivedPullback via the counit helper and uses Mathlib
   leftDerived_fac_app and isLeftDerivedFunctor_iff_isIso_leftDerivedLift directly.
   Proof-only imports are plain import; public imports supply the theorem signatures.
   The target's removed direct flat-complex dependency remains transitively used, so
   no branch is pruned. Checked the unit's realized record: none of these nodes realizes
   a unit statement or step; its route and record are unchanged.
5. Checked the target node against the reduction and the helper node against every
   proof step. The sole open node matches its Lean statement verbatim, has its named
   docstring proof and required fields. Existing node changes are confined to proof,
   proof_deps and proof_origin. The delivery is a decomposition, not a completed target.

Changes by the second reader: corrected the new flatness theorem's source citation and
node source/proof_origin from derived-pullback tags to 01U4 and 05NE; replaced copied
comment markup in its node proof with a standalone mathematical argument, including
finite limits/colimits; added independent search records; clarified dependency pruning,
upstream sorry dependence and the zero net hole count. No Lean proof or signature changed.
