# AlgebraicGeometry.ProjectiveSpace.finite_H_twist_affine

## Reason

The stage-3 textual interface checker conservatively flags added `variable`, `open`,
namespace and `attribute` commands. This record documents those commands for the new
private proof helpers. No existing declaration, definition, visibility, public import,
universe or statement has changed. The original theorem is proved in the same namespace.

The new `AffineTwistCech` namespace contains only private definitions and proved private
lemmas. Its `variable` commands bind the finite coordinate type, affine scheme and twist.
The `open` commands resolve names only while elaborating this file. The attribute is
`attribute [local instance] MvPolynomial.gradedAlgebra`, used only in the private
integral-model basis comparison. It has local scope and exports no new global instance.
The main `ProjectiveSpace` namespace is nested under `AlgebraicGeometry`, giving the
identical fully qualified theorem name as the old single namespace command.
All five added imports are ordinary proof-only imports.

Repair X-853f9 generalizes the returned delivery's private projective-bound helper to
`finite_affine_cover_cohomology_bound`, with explicit parameters for an arbitrary
scheme X, a separated morphism X to affine T, and a finite affine cover of X.
The standard projective cover is now one application of this general result.
The existing projective-only helper is private in a module that already depends on
this item, so importing it would form a cycle. No existing library signature or
visibility changes; only newly delivered private proof scaffolding is generalized.

## Old

```lean
theorem finite_H_twist_affine {T : Scheme.{u}} [IsAffine T]
    [IsNoetherianRing Γ(T, ⊤)] (N : Type u) [Finite N] (m : ℤ) (q : ℕ) :
    letI : Module Γ(T, ⊤) ((twist N T m).H q) :=
      Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
    Module.Finite Γ(T, ⊤) ((twist N T m).H q)
```

Proof: `by sorry`. The file opened `namespace AlgebraicGeometry.ProjectiveSpace`
without any local helper section.

## New

```lean
theorem finite_H_twist_affine {T : Scheme.{u}} [IsAffine T]
    [IsNoetherianRing Γ(T, ⊤)] (N : Type u) [Finite N] (m : ℤ) (q : ℕ) :
    letI : Module Γ(T, ⊤) ((twist N T m).H q) :=
      Module.compHom _ (ℙ(N; T) ↘ T).appTop.hom
    Module.Finite Γ(T, ⊤) ((twist N T m).H q)
```

Proof: complete affine-base monomial comparison and finite homology calculation.
Private helpers precede it under `namespace AlgebraicGeometry` and use local
elaboration commands; the public statement and its elaborated scalar structure stay
identical. There are no new public declarations or new hypotheses.

## Users

`tools/downstream.py ... --uses finite_H_twist_affine` reports the following two textual
users. The broader import closure has no interface to adapt: neither local commands nor
private declarations are public data. No other module is modified in this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjectiveTwistFiniteCohomology | J4 | Own unchanged public theorem now proved; private proof scaffolding added. |
| Sheaf.AlgebraicGeometry.ProjectiveFiniteCohomologyPresentation | unclaimed | Its application of the unchanged theorem needs no adaptation. |

No target statement or definition used by a target changes. No forced adaptation is
necessary or included.

## Status

landed 20261013T123546-L-3711602 2026-10-13 (merge of deliver/J4/Sheaf.AlgebraicGeometry.ProjectiveTwistFiniteCohomology)
