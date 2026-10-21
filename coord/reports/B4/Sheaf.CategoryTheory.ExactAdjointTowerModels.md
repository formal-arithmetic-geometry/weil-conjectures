## What changed

Proved `CategoryTheory.ExactAdjointTowerModels.exists_models` in
`lean/Sheaf/CategoryTheory/ExactAdjointTowerModels.lean`. All existing structures,
definitions and theorem signatures are unchanged. The added helpers are private and
fully proved.

The proof constructs canonical K-injective resolutions with injective terms, uses the
exact adjunction and its pointwise extension to preserve K-injectivity, and transports
the termwise product and limit computations to the chosen complex limits. The
K-injective localizer criterion constructs all four universal derived models; their
invertible units give the four normalized computation isomorphisms. Canonical product
and limit comparisons supply `c` and `beta`; their projection equations prove
naturality and commutation with the shift and difference. The derived Hom bijection
and explicit product/limit homotopies prove independence of chain representatives.

For exact products, the cone map induced by `(identity, minus identity)` gives the
sign isomorphism, with coordinates checked against both biproduct projections. The
negative comparison's normalization then proves the specified positive inclusion's
unit identity and quasi-isomorphism. The two triangle assertions follow by transporting
the distinguished mapping-cocone triangle along these actual isomorphisms.

Updated only `proof`, `proof_deps` and `proof_origin` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-exact-adjoint-tower-models.json`.
The blueprint unit and all statement dependencies are preserved. No definition repair,
consumer adaptation, new public declaration or new module is needed. Preflight
classifies the proof elaboration commands as an interface change, so
`coord/changes/exact-adjoint-tower-models-proof-commands.md` documents those commands
and the unchanged downstream interface (consumer held by V6).

## Proved and sorry left

Closed the single original hole:
`CategoryTheory.ExactAdjointTowerModels.exists_models`
(node `lem-weil-pbc-exact-adjoint-tower-models`).

Original holes: 1. Closed: 1. Remaining in the item: 0. Added elsewhere: 0.
Split off: 0. Every private helper is complete.

Validation: the final pruned proof compiled through `lcompile.py` (38.4 seconds).
Unused section-instance warnings were removed by explicit `omit` declarations.
The final delivery compile and axiom probe passed without warnings; server preflight
requested the accompanying elaboration-command change record, which is now included. A direct comparison confirms that every
existing definition/structure interface and the theorem signature are unchanged.

## No longer needed

Removed the proof import `WeilConjectures.Algebra.Homology.RoosComplex` and the proof
edge to `lem-weil-derived-limit-roos-complex`. The unit-normalized comparison already
makes the inclusion a quasi-isomorphism on K-injectives, so no separate Roos
quasi-isomorphism theorem is needed.

Removed the proof import `Sheaf.CategoryTheory.KInjectiveTotalDerived` and its proof
edges to `lem-weil-pbc-kinjective-total-derived`: the existing localizer derivability
API constructs the universal units directly at the complex localization, avoiding
transport of a homotopy-category unit. Its existing statement dependency is retained.

Removed the proof import
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`. The assigned statement
has small sites and ring sheaves in the same universe, so the adopted source theorem
`SheafOfModules.isGrothendieckAbelian` applies directly. The dependency on the
Grothendieck property of ring sheaves remains; its more general universe interface
is unnecessary for this proof.

An experimental proof import of
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` was also removed:
its generic helper was unnecessary once the localizer criterion was applied directly.
It is absent from the delivered imports and is not added as a DAG dependency.

These are unused imports/proof edges of this item; no claim is made that their modules
can be withdrawn globally, since other consumers or statement dependencies may retain
them. No module or upstream declaration is deleted. All other planned dependencies
are used through their existing library declarations or Mathlib implementations.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and required no repair. The original plan's independent
step establishing the Roos inclusion as a quasi-isomorphism is redundant: the stronger
normalized comparison plus its invertible unit on K-injectives already proves it.
The final DAG records this shorter argument. The generic total-derivation node's
homotopy-category interface is also unnecessary for the complex-localization unit
required by `DerivedModel`; the existing localizer API supplies that interface directly.

Some compile requests returned the documented busy-server response (exit 124); they
were retried without changing the launcher, limits or compilation method.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
