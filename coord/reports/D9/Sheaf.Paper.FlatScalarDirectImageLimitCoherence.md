## What changed

Proved `CategoryTheory.FlatScalarLimitCoherence.flatScalarDirectImageLimitCoherence`
in the assigned module without changing its statement or any existing definition.
Added three proved private helpers for the ordinary projection square, equality of
natural transformations on K-injective representatives, and preservation of
K-injectivity by inverse limit. The main argument cancels invertible units,
uses the six supplied normalization equations and naturality, and localizes the
ordinary projection square. The second conclusion is naturality of the actual
composite transformation. The third uses the existing flat scalar-extension
adjunction, whiskered with towers, and the exact-left-adjoint criterion.

Updated the assigned DAG node's proof, proof dependencies and proof origin to
match that argument. No new declarations with postponed proofs, new nodes,
statement changes or forced adaptations are included.

Validation: the final pruned module compiled successfully through `lcompile.py`
with no errors or warnings. The entire original theorem signature was compared
verbatim and is unchanged. All Lean lines are at most 100 characters.

Sources read: Stacks `sites-cohomology.tex`, Tag 0A07,
`lemma-Rf-commutes-with-Rlim`, first proof; `derived.tex`, Tag 08BJ,
`lemma-adjoint-preserve-K-injectives`. The scalar-extension input is the already
proved `SheafOfModules.flatRestriction_exact_leftAdjoint` (03CZ and 03ER(3)).
The unit remains `sk-prop-sf-cbc`; its compact-support base-change statement and
route are unchanged. The revised proof is only below that unit.

Searches ran through msearch: LeanFinder for equality of derived natural
transformations on K-injectives, Loogle for `CategoryTheory.Limits.limit.post`,
and grep for `rightDerived_ext|exists_iso_Q_obj_of_isKInjective|limit.post_post`.
The library's existing K-injective representative lemma supplies the shortest
extension argument; no matching scalar-coherence theorem was found.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.FlatScalarLimitCoherence.flatScalarDirectImageLimitCoherence`
(blueprint `lem-cbc-flat-scalar-direct-image-limit-coherence`).
Added 0 holes. No `sorry` remains in the delivery. No decomposition.

## No longer needed

Removed these unused private imports:
`Sheaf.CategoryTheory.DiagramSiteRealization`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
`Mathlib.CategoryTheory.Abelian.FunctorCategory`.
All four original public imports are retained verbatim, including the required
unit-route module `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`.
The existing public API is unchanged. New proof inputs are imported privately.

The revised proof does not use the following planned proof dependencies:

- `lem-weil-pbc-diagram-site-realization`: directly use the existing small-module
  diagram Grothendieck theorem and lift/reindex the naturals.
- `prop-pur-kinjective-resolutions-exist`: directly use the existing general
  Grothendieck K-injective resolution API.
- `lem-weil-pbc-flat-ringed-diagram-restriction`: the needed K-injective
  preservation follows directly from its existing exact-left-adjoint input;
  all the direct-image comparisons are supplied in this theorem's hypotheses.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: its computation
  properties are already explicit hypotheses. The direct-image/limit
  comparison dependency remains on the unit route and its normalizations
  are used explicitly.
- `lem-weil-ringed-tower-pushforward-limit-acyclic`: the normalization equations
  hold on all complexes, so no auxiliary target resolution is needed.
- `lem-cbc-exact-product-functor-strict-limit`: lambda and its normalization
  are explicit hypotheses, so constructing its Roos model again is unnecessary.
- `lem-weil-pbc-kinjective-hom-derived`: naturality is already supplied by the
  composite of natural transformations, so individual derived morphisms need
  not be represented by chain maps.

Removed the obsolete tool-use approvals for the unused planned dependencies
listed above, retaining the existing approvals for
`lem-weil-pbc-right-adjoint-preserves-kinjective` and
`lem-weil-tower-category-levelwise-abelian` and
`lem-weil-ringed-tower-pushforward-limit-comparison`. The three already proved inputs
`lem-weil-pbc-flat-restriction-exact-left-adjoint`,
`lem-weil-pbc-small-module-diagrams-grothendieck`, and
`lem-weil-pbc-kinjective-functorial-existence` are used as generic tools; no unit
step is replaced. New tool-use approvals, if needed, belong to the maintainer.

These are removals from the proof route only. Statement dependencies retain
their original records, and no upstream declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The first preflight required restoring all original public imports and the
unit-route comparison module; this packet now retains them verbatim.

The original plan is valid but proves more auxiliary model comparisons than
needed for the stated theorem. Its all-complex normalization hypotheses permit
the direct unit-cancellation proof above. The ordinary square works for any
natural d0 with these endpoints, so its additional underlying-sheaf identity
hypothesis need not be used. No mathematical statement error was found.

Compile-server no-answer responses were retried; they were not treated as
Lean compilation failures or as a reason to stop work.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
