## What changed

Proved `AlgebraicGeometry.exists_gradedAlgebra_closed_descent` in the assigned module,
with its public signature and public imports unchanged. All added helpers are private and proved.
The proof constructs operations directly on opens. An inducing map supplies ambient representatives;
restriction compatibility makes the operations independent of those representatives. Linearity over
the subscheme structure sheaf is checked on inverse images of affine neighborhoods using
`Scheme.Hom.app_surjective` and sheaf separation. The unit is constructed from its global section
using `SheafOfModules.unitHomEquiv`. The specified isomorphisms reflect all four algebra laws.
The node's proof, proof dependencies and proof origin now record this route.

The argument includes empty opens, the empty closed subscheme and zero modules: extension along
opens still applies; sheaf separation on an empty open has no pointwise obligations; no nonzero
section, nonempty space or degree cancellation is assumed. Arbitrary nilpotent closed immersions
are included because scalar lifting uses the quotient-ring surjectivity on affine opens.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_gradedAlgebra_closed_descent`
(node `lem-pur-closed-immersion-graded-algebra-descent`).
Zero holes remain in the module; zero holes were added; zero statements were split off.
This is a proof, not a decomposition. The required remote single-file compile passed
without warnings in 13.6 seconds. The delivery tool additionally runs compilation and its axiom probe.

## No longer needed

No existing import was removed. The proof avoids these four planned dependencies, removed from
this node's `proof_deps` and proof-step uses:

- `lem-weil-pbc-closed-pushforward-stalks`, module
  `WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks`: ambient representatives replace
  stalk comparison.
- `lem-weil-pbc-module-stalk-tensor`, module
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor`: operations are constructed
  directly, with scalar linearity checked locally; no tensor comparison is required.
- `lem-weil-pbc-closed-immersion-pushforward-fully-faithful`, module
  `WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`: sectionwise
  injectivity of the specified isomorphisms reflects the laws.
- `def-weil-presheaf-modules-sheafification`, module
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: the construction uses existing
  section modules and their restrictions, without extending maps through sheafification.

These are dependency-edge removals for this item. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The planned tensor comparison and fully faithful lifting are a valid
route, but unnecessary for this sectionwise interface. The direct construction proves the item
without importing any still-unproved project theorem. The existing theorem docstring describes
the original alternative argument; the updated DAG records the formal proof actually delivered.
The unit record has no realized proof-step constraints on this auxiliary node, and the normal-cone
route is preserved.

Searches used the prescribed LeanFinder, Loogle and grep services and local searches in Mathlib,
Sheaf and WeilConjectures. The fully faithful theorem and tensor universal property were read;
neither supplies a shorter normalized sectionwise construction than the direct proof above.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
