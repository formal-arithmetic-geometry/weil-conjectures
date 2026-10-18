## What changed

Proved `AlgebraicGeometry.Etale.isIso_proper_projection_formula_reordered` in
`Sheaf.AlgebraicGeometry.ProperProjectionFormula` by specializing the existing
`isIso_rightDerivedLowerStarProjectionMap_of_finite A r`, taking its two components,
and using the Mathlib instances for symmetry components, functor images and composites
of isomorphisms. The signature, all public imports and all definitions are unchanged.
Updated its docstring and node `lem-amb-proper-coproducts-projection` to describe this
proof. There are no adapted modules or change records.

The existing finite projection theorem is recorded by
`lem-etale-proper-projection-formula-finite` in the same unit `sk-prop-sf-cbc`. Its
objectwise proof in `ProjectionFormulaFiniteObjectwise` uses proper geometric pullbacks,
the constant-complex formula over a geometric point, and geometric-stalk conservativity.
Thus reuse retains the current blueprint's geometric-stalk and constant-complex route.
The unit record has no realized proof steps to bypass.

Validation: the original-import version compiled in 3.1 seconds; the final version
with both redundant proof imports removed compiled in 3.4 seconds using `lcompile.py`,
without errors or warnings. No bound, nonzero-ring assumption, or restriction on either
unbounded complex was added. The zero ring and empty schemes remain included.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_proper_projection_formula_reordered`
(node `lem-amb-proper-coproducts-projection`).

Added 0 holes. Split off 0 statements. There are 0 sorries left in the item module,
and no other Lean modules are delivered. Existing imported obligations are reused;
this is not a claim that their entire transitive axiom closure is already sorry-free.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`:
the general torsion-ring theorem `lem-kun-0f0g` is unnecessary for this finite-coefficient
specialization because the library already supplies the exact finite projection theorem.

Removed the proof-only import
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: its exported interface
is already present through the unchanged public compatibility import
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`. This proof needs no separate
application of `etaleInverseImageModulesExact`; exact pullback is already encoded in the
canonical projection map and the existing finite theorem.

Removed `prop-weil-pbc-inverse-image-modules-exact`, `lem-kun-0f0g`,
`def-kun-derived-tensor`, and `def-kun-projection-formula-map` from this node's direct
proof dependencies. The latter two remain statement dependencies: the canonical tensor
and canonical projection morphism are unchanged. Likewise inverse-image exactness stays
in the statement dependencies. Removed the obsolete direct tool-use approvals for
`lem-kun-0f0g` and `prop-weil-pbc-inverse-image-modules-exact`, retaining
`lem-kun-tensor-sym`. No global withdrawal of these nodes is claimed: other modules may
still need them. All public imports are retained to preserve the existing public interface.

## Where the brief, the DAG or earlier work was wrong

The planned finite-ring-to-torsion reduction is redundant for this module: the upstream
finite-coefficient theorem already proves invertibility of the exact middle map. The
node's docstring already identified that theorem as an alternative. The current
blueprint proof was read at
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-amb-proper-coproducts-projection.proof.md`;
its geometric-stalk argument is supplied by the reused theorem's existing objectwise
proof. The local Stacks source `etale-cohomology.tex`,
`lemma-projection-formula-proper-mod-n` (Tag 0F0G), gives the same stalk and fibre route.

Searches: repository `rg` found the exact finite theorem and its already proved assembly
`finite_projection_iso`; Mathlib `rg` confirmed `NatIso.isIso_app_of_isIso` and
`Functor.map_isIso`. `msearch.py` LeanFinder returned only more general/unrelated graded
bifunctor constructions; Loogle found the component-isomorphism instances used here.
No new statement, definition, source conjecture, or missing node was needed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
