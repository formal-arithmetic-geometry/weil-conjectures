## What changed

Proved the existing theorem in Sheaf.AlgebraicGeometry.GroupScheme.LieLocalDimension
from a new Lie/cotangent interface, the source-library theorem
AlgebraicGeometry.Smooth.isRegularLocalRing_stalk, and Mathlib dimension lemmas.
The existing signature and docstring are unchanged. Added proof-only imports of
LieCotangentDual, WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth, and
Mathlib.LinearAlgebra.Dual.Lemmas. Updated the item node to match this route.

The argument explicitly transports dimensions across a residue-field semilinear
map using rank_eq_of_equiv_equiv and Cardinal.toNat, then uses dual_finrank_eq and
regular-local cotangent dimension. All delivered modules compile without warnings.

## Proved and sorry left

Closed AlgebraicGeometry.GrpObj.finrank_lie_eq_localKrullDim_of_smooth
(node lem-ag-smooth-lie-local-dimension). No sorry remains in the original module.
Added one hole: AlgebraicGeometry.GrpObj.exists_lie_identity_cotangent_dual_equiv
(node lem-ag-lie-identity-cotangent-dual), in the new module LieCotangentDual.
This is a decomposition, with net holes zero, not an axiom-free completion.
The remaining interface has no smoothness hypothesis and states an equivalence,
not the original dimension equality; regularity and both dimension steps are Lean proofs.
No data definitions, target statements, or other existing signatures changed.

## No longer needed

Removed the original module's direct imports of
Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality and
Sheaf.RingTheory.SmoothOverFieldRegularLocal.
The rational duality module/node lem-sc-rational-tangent-cotangent-duality remains
needed through the new interface; it is not globally pruned.
The module Sheaf.RingTheory.SmoothOverFieldRegularLocal and node
lem-weil-pbc-smooth-over-field-regular-local are no longer needed by this argument:
the proved scheme-stalk regularity theorem replaces the affine-algebra bridge.
The direct proof dependency def-wf-lie-algebra-derivation is moved into the new
interface's proof dependencies, not globally removed. The regular-local cotangent
Mathlib leaf lem-weil-pbc-regular-local-cotangent-dimension is retained.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original dependencies did not directly connect the sheaf Hom definition of
Lie G to the rational dual-number tangent space, and smooth_over_field_regular_local
only speaks about affine-algebra localizations. The latter bridge is already supplied
by Smooth.isRegularLocalRing_stalk in the proved source library. The former bridge
is the single remaining new interface; it requires residue-field scalar transport,
which the combining proof handles explicitly.

Edge cases checked mathematically: the trivial group has zero cotangent space and
zero Lie algebra; nonreduced groups still satisfy the new interface; no finite-type,
smoothness, characteristic-zero, or algebraic-closure restriction is needed for it.
Infinite-dimensional cotangent spaces do not invalidate this equivalence; the
original smoothness hypothesis is used separately for regularity and dimension.
The local copy of literature contains citation tables rather than blueprint text;
the inherited node/source and existing declaration docstrings supply the route.

## New nodes

lem-ag-lie-identity-cotangent-dual: the Lie algebra is semilinearly equivalent to
the residue-field dual of the cotangent space at the identity, without smoothness.
Module lean/Sheaf/AlgebraicGeometry/GroupScheme/LieCotangentDual.lean. Its docstring
and node record the rationality, infinitesimal-point, and cotangent-duality argument.
No change records are required.

## Second reading by K1

1. Compared the delivered module with the repository using diff. The existing declaration's
   signature and docstring are byte for byte unchanged; no definitions or target statements
   change. The extra module contains only a new named theorem, not a data definition.
2. Compiled both files in import order without warnings. Scratch `#print axioms` checks show
   only propext, Classical.choice, Quot.sound and sorryAx for the two delivered theorems.
   lieEquiv, Smooth.isRegularLocalRing_stalk and iff_finrank_cotangentSpace have only the
   three allowed axioms. The only textual hole is
   AlgebraicGeometry.GrpObj.exists_lie_identity_cotangent_dual_equiv. There are no forbidden
   declarations or holes inside definitions. This remains a decomposition with net holes zero.
3. The split theorem is a true Lie/cotangent identification without smoothness, not a renamed
   dimension equality. The trivial group has both spaces zero; the additive group has both
   spaces one-dimensional; alpha_p in characteristic p still has one-dimensional tangent and
   cotangent spaces although its local Krull dimension is zero. Thus smoothness is correctly
   used only in the combining dimension proof. No finite-dimensional restriction is needed for
   the equivalence. Independent LeanFinder, Loogle and grep searches, and rg of the project
   library, found no existing general Lie-to-stalk-cotangent equivalence; the matrix-group
   cotangent results apply to a special case. Its node and sourced docstring are present.
4. Read the supplied dependencies and the upstream regularity proof. The direct scheme-stalk
   regularity theorem is the shortest available regularity route. Every removed old dependency
   is accounted for under No longer needed; rational duality and the Lie definition remain
   through the new interface. Public imports supply signature types; proof imports remain
   private. The sk-i-cartier realized lists are empty, and the identity tangent/cotangent then
   regularity route still implements the dimension paragraph without bypassing a unit step.
5. Read both delivered nodes against the Lean. Their proof-dependency lists are the unions of
   their recorded steps, their Lean signatures match the files, and their proof-origin records
   describe the actual reduction. The split node has source, searches, creation, blueprint,
   chapter, unit and Lean records. The proved upstream regularity theorem is explicitly named
   in the item's proof record. No change record is necessary.

Changed the new interface docstring and node proof to make the inverse construction explicit:
subtract the structural scalar lift of the residue, apply the functional modulo m squared,
and use the unit laws to identify differentiated group multiplication with vector addition.
Fixed spacing before `:=` in the combining proof and added this independent review. No existing
signature, existing docstring, definition or import was changed by the second reading.
