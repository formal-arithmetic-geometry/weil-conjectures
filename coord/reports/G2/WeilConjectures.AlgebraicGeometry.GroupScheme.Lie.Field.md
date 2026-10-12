## What changed

`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Field` keeps all existing signatures,
definitions and public imports. Added proof-only imports of
`Mathlib.AlgebraicGeometry.AlgClosed.Basic`,
`WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier`,
`Sheaf.AlgebraicGeometry.GroupScheme.LieLocalDimension`, and
`Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension`.

The rational-point lifting proof forms the fibre over the given point. The original structure
map being locally finite type implies the morphism is locally finite type, so the fibre is
locally finite type over k. Surjectivity gives a nonempty fibre; its Jacobson topology gives a
closed point without any quasi-compactness assumption. Mathlib's `pointOfClosedPoint` gives a
section. The pullback identity and the Over commutativity equations supply the required point
and equality. This proof is complete and introduces no intermediate assumptions.

The dimension proof uses the existing Cartier smoothness theorem, then composes Lie-to-local
and local-to-global dimension equalities. The two equalities are separate new modules and
nodes, each strictly a part of the argument. The identity-local equality does not assume
smoothness or characteristic zero; the Lie-local equality needs only smoothness and does not
assume global quasi-compactness or characteristic zero. This keeps the third paragraph of
`sk-i-cartier`: smoothness, tangent dimension, translation, global dimension.

Existing node copies retain the routes for their other declarations and append the precise
Lie.Field dimension reduction. All three modules compile locally without warnings.
The two new dependency modules were also checked for import cycles; their DAG dependencies
have no paths back to their new nodes. No target or other existing declaration was changed.

## Proved and sorry left

* `AlgebraicGeometry.exists_points_comp_eq_of_surjective`: proved directly from Mathlib.
* `AlgebraicGeometry.GrpObj.finrank_lie_eq_topologicalKrullDim`: reduced by a complete Lean
  proof to Cartier smoothness and the two new intermediate theorems.
* No direct `sorry` remains in the item's module.
* `AlgebraicGeometry.GrpObj.finrank_lie_eq_localKrullDim_of_smooth` remains `sorry`, in
  `Sheaf.AlgebraicGeometry.GroupScheme.LieLocalDimension`, node
  `lem-ag-smooth-lie-local-dimension`.
* `AlgebraicGeometry.GrpObj.localKrullDim_identity_eq_topologicalKrullDim` remains `sorry`, in
  `Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension`, node
  `lem-ag-group-identity-local-dimension`.

The dimension theorem is not yet axiom-free: the intermediates and imported Lie theory still
carry existing proof obligations. The two original already-proved identity-component
constructions are unchanged.

## No longer needed

No original import was removed: the public Lie.Ring import is needed by the statements.
No existing node or module is claimed globally pruned: the original nodes also carry
other declarations outside this item, whose dependencies must remain.

The rational-point proof needs no new Nullstellensatz module, no imported
`FundamentalGroup.GeometricFiber` existence lemma, and no finite or quasi-compact fibre
assumption. It uses the existing Mathlib closed-point theorem directly.

While checking the new modules, removed the redundant candidate imports
`Mathlib.AlgebraicGeometry.Properties` (both modules) and
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (IdentityLocalDimension).
Their needed statements are already visible through the required public source imports.
No other proof-only imports were added and then left unused.

## Where the brief, the DAG or earlier work was wrong

The two existing matching node files record declarations in several modules; neither provides
a numbered Lean-ready proof for this module's dimension theorem. The existing Cartier node's
own `proof` is empty, although its blueprint proof text is present. The delivery supplies
only the missing dimension reduction and leaves its other routes intact.

The first theorem has no blueprint tag or dedicated node in its existing docstring. Its full
proof now closes that untracked obligation without introducing another node.

The rational-point sketch suggests taking a closed point of a nonempty locally finite type
fibre. Quasi-compactness is unnecessary: use JacobsonSpace.nonempty_inter_closedPoints for the
whole nonempty fibre, rather than the compact-space existence lemma.

The source's existing tangent-cotangent duality declaration uses dual-number morphisms, whereas
`GrpObj.Lie` uses morphisms of sheaves of modules. It cannot be applied directly to replace the
missing comparison. LieLocalDimension records precisely the comparison plus smooth regularity
needed here. SmoothOverFieldRegularLocal is a ring-level statement, not directly a scheme-stalk
instance. IdentityLocalDimension records the remaining translation and field-extension glue.

LeanSearch was attempted for each new statement and returned Internal Server Error; it is
recorded as unavailable, not as no match. LeanFinder and local grep were run and produced no
exact matches. Blueprint searches for identity/dimension and smooth/tangent found the source
multi-clause nodes, not these separately usable statements.

Edge cases: the trivial group has zero Lie and local/global dimension zero; finite etale
and disconnected groups likewise have zero dimensions. Smooth positive-characteristic groups
are included in the Lie-local statement; nonreduced finite group schemes are included only in
the local-global statement, which concerns prime chains and is invariant under nilpotents.
The identity section guarantees nonemptiness, so no false empty-scheme equality is asserted.
The argument over a non-algebraically-closed field passes through its algebraic closure;
it does not assume translations by k-points reach every closed point over k.

## New nodes

`lem-ag-smooth-lie-local-dimension`: module
`lean/Sheaf/AlgebraicGeometry/GroupScheme/LieLocalDimension.lean`. It isolates the smooth
identity's tangent/cotangent comparison and regular-local dimension criterion. The statement
has an unchanged existing Lie definition and uses no global dimension in its conclusion.
Source: the dimension paragraph of `lem-wf-same-lie-closed-subgroup` and the third paragraph of
`sk-i-cartier`. Its node names the existing rational tangent-cotangent, smooth regularity and
regular-local cotangent criterion nodes. It remains a future proof item.

`lem-ag-group-identity-local-dimension`: module
`lean/Sheaf/AlgebraicGeometry/GroupScheme/IdentityLocalDimension.lean`. It isolates the
translation argument showing that the local ring at the identity has the scheme's global
dimension. Its statement makes no mention of Lie or characteristic zero. Source: the same
source dimension paragraph. Its node cites translation, dimension base change, closed-point
local dimension and the scheme dimension supremum theorem. It remains a future proof item.

No definition changes or change records are needed.


## Second reading by G2

1. Compared the complete Field module with the repository using `diff -u`. The only
   existing-module changes are four plain proof imports and the bodies of the two previously
   open theorems. Every existing signature, definition, docstring and public import is byte
   for byte unchanged. The two additional modules are new statements, with matching new nodes;
   there are no statement changes or change records. Verdict: passes.

2. Compiled all three files through lcompile.py without errors or warnings. Scratch copies
   with explicit `#print axioms` show that exists_points_comp_eq_of_surjective uses exactly
   propext, Classical.choice and Quot.sound. The dimension reduction and the unchanged
   identity-component declarations also use sorryAx from open dependencies; neither is claimed
   axiom-free. The two new theorems are the only direct sorries delivered, each named and
   documented. No forbidden declaration or hollow definition occurs. Verdict: passes as a
   partial proof delivery, with one of the two original open theorems axiom-free.

3. Read both new Lean statements and both complete node records. Smoothness is enough for
   finite-dimensional cotangent space at the rational identity even without global
   quasi-compactness. The second equality requires finite type, expressed by locally finite
   type and quasi-compactness, and works for nonreduced groups and arbitrary fields. Checked
   the trivial group, disconnected finite etale groups, positive-characteristic smooth groups,
   and infinitesimal finite groups: the last may have nonzero Lie dimension, but is excluded
   from the smooth lemma and has local/global dimension zero. The two lemmas are distinct
   strict parts of the argument, not renamings of its conclusion. Independently searched
   LeanFinder for stalk dimension at the neutral element and duals of smooth cotangent fibres,
   Loogle for Module.finrank with ringKrullDim, and grep for cotangentSheaf and coheight.
   Found the regular-local cotangent criterion and standard-smooth differential rank, but no
   existing scheme-level comparison closing either lemma in a few minutes. Local rg also
   checked the general-linear subgroup comparison: it is a special-case theorem, not a proof
   of either statement for arbitrary group schemes. Verdict: passes; two genuine obligations
   remain.

4. Read the rational-point proof from its conclusion back to the fibre construction. It uses
   locally finite type of f derived from that of X, base-change surjectivity, Jacobson closed
   points and pointOfClosedPoint; it adds no compactness assumption. Read the dimension proof
   against Cartier.smooth_of_grpObj_of_charZero and the definition of Lie as sheaf-module Hom.
   The route remains Cartier smoothness, tangent/local dimension, translations/global
   dimension, exactly the unit's third paragraph. No old public import can be pruned. The old
   node dependencies also serve other declarations, so their retention is justified and no
   global pruning is claimed. The repository's sk-i-cartier.realized entries are already
   empty: this is an inherited coordination gap, not a route change; this delivery does not
   alter the unit record. Verdict: passes, with that pre-existing gap reported.

5. Checked proof, proof_deps and proof_origin of both amended multi-declaration nodes and the
   two new nodes against the reduction and their docstring arguments. Existing non-Field
   routes are retained. All new-node dependencies have a Lean declaration or a Mathlib match;
   the regular-local cotangent criterion is the existing Mathlib leaf. The added import graph
   has no cycle. The existing Cartier node has no recorded numbered proof for its other
   declarations; this delivery preserves their dependency list rather than inventing one.
   Verdict: passes for the delivered reduction.

Changes by the second reader: added plain imports of RationalTangentCotangentDuality and
SmoothOverFieldRegularLocal to LieLocalDimension, and DimensionBaseChange,
DimensionAtPointFieldExtension and ClosedPointDimensionLocalRing to IdentityLocalDimension.
These expose the already recorded proof-plan dependencies in the modules of the open lemmas,
as brief-stage3 requires; they add no public interface or new assumption. Dimension is already
provided through DimensionBaseChange, translations through Lie.Basic, and regular-local
cotangent dimension through SmoothOverFieldRegularLocal, so duplicate imports are unnecessary.
No mathematical proof body or existing signature required repair.
