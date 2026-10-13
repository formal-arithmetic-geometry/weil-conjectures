## What changed

Proved the original `AlgebraicGeometry.strictPerfectClosedPushforward_stalkModel`
without changing its signature or public imports. Construct the stalk complex using the
explicit `openModuleStalkFunctor`, transfer bounds and finite-free retractions, and compute
homology using the proved `openModuleStalk_closedPushforward_homology`.

This repair removes the whole new `OpenModuleStalkRestriction` module, including its
private duplicate `AlgebraicGeometry.inverse_stalkMap_germ`, the other germ-linearity
helpers, and its new node `lem-sc-open-module-stalk-restriction`.
The homology module now imports and uses the existing public
`AlgebraicGeometry.nonempty_restriction_stalk_extension_iso` from
`Sheaf.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso` instead.
Apply it to the single complex of the pushforward sheaf, evaluate the resulting complex
isomorphism in degree zero, and restrict scalars. The open immersion's stalk map is a
ring isomorphism, so restriction of scalars is an equivalence and the extension/restriction
adjunction unit is invertible. Composing with its inverse and `overFunctorEquiv` gives
exactly the coefficient isomorphism needed by the homology proof. No natural comparison
is needed and no existing private helper is repeated.

The delivery adds three modules with nodes: `OpenModuleStalkFunctor`,
`OpenModuleStalkFreeProjective`, and `OpenModuleStalkClosedPushforwardHomology`.
Their definitions are explicit constructions; no data comes from an unproved witness.
Unit stalks use the existing public `Scheme.ideal_module_product_stalk` applied to the
identity inclusion of the unit sheaf. This retains the earlier repair deleting the
duplicate `ModuleStalkUnitIso` module and node.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.strictPerfectClosedPushforward_stalkModel`
(node `lem-sc-strict-perfect-closed-pushforward-stalk-model`).

Added zero holes. No sorry remains in any delivered module. All four delivered modules
compiled together without warnings. Fresh axiom checks of the repaired parent and
homology theorem report only `propext`, `Classical.choice`, and `Quot.sound`.
Also proved `AlgebraicGeometry.openModuleStalk_free_projective`
(node `lem-sc-open-module-stalk-free-projective`) and
`AlgebraicGeometry.openModuleStalk_closedPushforward_homology`
(node `lem-sc-open-module-stalk-closed-pushforward-homology`).
The explicit `AlgebraicGeometry.openModuleStalkFunctor` and its zero-morphism,
finite-limit, finite-colimit, and additivity instances are fully proved
(node `def-sc-open-module-stalk-functor`).

The proof includes rank zero through the empty coproduct. Empty opens admit no point,
and the homology argument covers every nonzero integer degree. The homology lemma
requires neither bounds nor projectivity. The new scalar-cancellation argument uses
only that the open immersion's stalk map is an isomorphism, with no nonzero-ring assumption.

## No longer needed

Removed new module `Sheaf.AlgebraicGeometry.OpenModuleStalkRestriction` and new node
`lem-sc-open-module-stalk-restriction`, and removed its import from the homology module.
All of its private germ-linearity proofs and natural-isomorphism constructions are pruned.
The existing `lem-pc-open-restriction-stalk-extension-iso` supplies the needed comparison.

The earlier duplicate `Sheaf.AlgebraicGeometry.ModuleStalkUnitIso` and new node
`lem-sc-module-stalk-unit-iso` remain removed. Its callers use the existing
`lem-weil-pbc-ideal-module-product-stalk` theorem directly.

Removed the parent's original proof imports `Sheaf.Algebra.Homology.ModuleStalkExact`
and `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`. Both existing modules remain
transitively needed: `ClosedPushforwardStalks` by the homology module, and
`ModuleStalkExact` by `IdealModuleProductStalk`. No existing library module is claimed
pruned from the target closure. The unused public import
`Sheaf.AlgebraicGeometry.DerivedCategory` remains removed from the new homology module.

The old direct proof dependencies `lem-weil-pbc-closed-pushforward-stalks` and
`lem-weil-pbc-module-stalk-exact` are no longer direct dependencies of the parent.
They remain transitively needed through the new homology proof and the unit-stalk
calculation respectively; `def-pc-perfect-complex` remains directly used.

The unit `sk-thm-picard-duality.realized` has no entry for this node. The stalk-model
argument still constructs the complex, transfers bounds, proves projectivity from
finite-free retractions, and computes degree-zero and other homology. No unit route
is bypassed, and no truncation or augmented resolution is introduced.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the existing private `inverse_stalkMap_germ` theorem
word for word. This repair deletes the duplicate module and node and changes its caller
to use the existing public complex-stalk theorem. The private theorem is inaccessible
through ordinary imports, but its public enclosing theorem suffices after specialization
to a single complex; the earlier assumption that a new natural comparison was needed
was wrong. The homology node's proof and proof_deps now record the existing theorem,
and stale search prose about copying private helpers is corrected.

No existing definition, statement, signature or visibility changed. No forced adaptation
or change record is needed. Removed the obsolete second-reading section so a fresh
independent reader can review this repair.

## New nodes

`def-sc-open-module-stalk-functor`: explicit slice-site/open-subscheme stalk functor,
with proved zero-morphism preservation, finite-limit preservation, finite-colimit
preservation and additivity. Module `Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor`.

`lem-sc-open-module-stalk-free-projective`: projectivity of the stalk image of any finite
free sheaf. Module `Sheaf.AlgebraicGeometry.OpenModuleStalkFreeProjective`.

`lem-sc-open-module-stalk-closed-pushforward-homology`: homology of any complex
derived-isomorphic to a restricted closed pushforward of the unit, without bounds or
projectivity assumptions. Module `Sheaf.AlgebraicGeometry.OpenModuleStalkClosedPushforwardHomology`.
Its coefficient comparison now uses existing `lem-pc-open-restriction-stalk-extension-iso`.

The parent node follows the constructed functor, mapped retractions and homology proof.
No change records added.

## Second reading by T1

1. **Interfaces — pass.** Compared every delivered module with its repository path.
   Only the parent already exists. Its theorem signature is byte for byte unchanged,
   including all hypotheses, universes and the full conclusion; its public imports and
   docstring are unchanged. The three helper modules are new. No definition or existing
   visibility changed, so no change record or forced adaptation is required.
2. **Proof and construction — pass.** Compiled all four modules in import order using
   lcompile.py, with no errors or warnings. Searched their sources for sorry and all
   forbidden declarations/options: none found. Independently printed axioms for the
   parent, both new theorems, the constructed functor and all four public instances;
   every result lists only propext, Classical.choice and Quot.sound, never sorryAx.
   The complex is constructed termwise from K. The unit and coefficient isomorphisms
   are obtained from proved theorems; there is no arbitrary witness from an unproved
   existence statement and no hollow definition.
3. **New statements — pass.** No unproved statement is split off. Reviewed the exact
   stalk composite, finite-free projectivity and the homology calculation independently.
   Rank zero uses the empty coproduct; an empty open supplies no point; arbitrary
   nonzero integer degrees are covered; scalar cancellation uses a ring isomorphism,
   without assuming a nonzero ring. The homology lemma is strictly the homology part
   of the parent and requires neither bounds nor projectivity. Fresh LeanFinder and
   Mathlib grep searches used different wording (exact additive stalk functors,
   projective modules and finite locally free sheaves); also searched lean/Sheaf,
   lean/WeilConjectures and the upstream checkout. No matching public theorem replaces
   these helpers. Existing public ideal_module_product_stalk and
   nonempty_restriction_stalk_extension_iso are reused; no private germ helper is copied.
4. **Route, imports and pruning — pass.** The parent transfers bounds, maps the given
   retractions and applies the separately proved homology calculation. The helpers use
   Mathlib's finite-coproduct projectivity, exact functor localization and single-complex
   homology. All public imports support public signatures or the public functor's
   construction; proof dependencies are plain imports. The old parent dependencies
   removed from its proof_deps are completely accounted for under No longer needed,
   including their continued transitive use. No existing module is claimed removed
   from the targets' closure. Inspected sk-thm-picard-duality.realized: its empty
   statement/step lists are unchanged, and this argument bypasses no unit step.
5. **DAG agreement — pass after metadata repair.** Read all four nodes alongside their
   Lean modules. Each proof_deps equals the union of its proof steps' uses; the steps
   and proof_origin describe the actual composite, retractions and homology argument.
   The three new nodes carry sources, searches, creation and blueprint records, and
   the parent's statement and statement dependencies are unchanged. Replaced the
   flattened lean.statement fields of the three new nodes with their verbatim Lean
   signatures. In particular, the homology node now retains the newline separating
   its let-bound complex from its conclusion.

Second reading changed only the three new node signature records and this report
(including explicit names of the parent's retired direct dependencies). No Lean proof,
statement, definition, import or docstring needed repair. One original hole is closed,
zero holes are added, and zero unproved statements are split off.
