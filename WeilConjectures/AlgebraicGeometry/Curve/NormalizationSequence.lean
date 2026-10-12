/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Curve.Reductions

/-!
# The normalisation exact sequence for the eight curve assertions

Let `X` be a reduced curve over an algebraically closed field `k`, `ν : X' ⟶ X` its
normalisation (more generally a finite surjective morphism which is an isomorphism over a dense
open), `j : U ⟶ X` an open immersion and `j' : U' ⟶ X'` its pullback. The extension by zero of
the unit gives a short exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0` whose cokernel is
supported on finitely many closed points, so that the eight curve assertions for `j_! 𝐅_ℓ` on
`X` follow from those for `j'_! 𝐅_ℓ` on `X'`.

## Main statements

- `AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`: the normalisation
  exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0`.
- `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`: the
  assertions for `j_! 𝐅_ℓ` on a reduced curve follow from those on its normalisation.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The normalisation exact sequence.** Let `X` be a reduced curve over an algebraically
closed field `k`, `ν : X' ⟶ X` a finite surjective morphism which is an isomorphism over a
dense open `V ⊆ X` (e.g. the normalisation of `X`), `j : U ⟶ X` an open immersion and
`j' : U' ⟶ X'` its pullback along `ν`. For a prime `ℓ` with `Λ/ℓΛ` finite there is a
monomorphism

`α : j_! (Λ/ℓ)_U ⟶ ν_* j'_! (Λ/ℓ)_{U'}`

(the extension by zero of the unit of `ν|_{U'}^* ⊣ ν|_{U'*}`, stalkwise the diagonal into the
fibre) whose cokernel `Q` is constructible and supported on the finite set `X ∖ V`, giving the
short exact sequence `0 → j_! 𝐅_ℓ → ν_* j'_! 𝐅_ℓ → Q → 0`.

Mathlib's `Scheme.Hom.normalization` is the relative normalisation of a morphism, and does not
directly provide the normalisation of a reduced curve together with its finiteness; we therefore
state the lemma for an arbitrary finite surjective `ν` which is an isomorphism over a dense open,
the properties of the normalisation that are used. The compatibility of the sequence with field
extension and restriction to opens, also part of the blueprint statement, is not recorded in
this existential form. (blueprint: `lemma-weil-pbc-normalization-exact-sequence`) -/
theorem exists_mono_lowerShriek_constantModSheaf_lowerStar {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] (V : X.Opens) (hV : Dense (V : Set X))
    [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'} [IsOpenImmersion j']
    {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] :
    ∃ α : (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)),
      Mono α ∧ Scheme.IsConstructibleSheaf (cokernel α) ∧
        IsZero ((V.ι)^*[ModuleCat.{u + 1} Λ].obj (cokernel α)) :=
  sorry

/-- **Normalisation and the smooth constant case.** Let `X` be a reduced curve over an
algebraically closed field `k`, `ν : X' ⟶ X` a finite surjective morphism from a smooth
`k`-scheme which is an isomorphism over a dense open (e.g. the normalisation of `X`),
`j : U ⟶ X` an open immersion and `j' : U' ⟶ X'` its pullback along `ν`. Then the eight
assertions for `j_! 𝐅_ℓ` on `X` follow from those for `j'_! 𝐅_ℓ` on the smooth curve `X'`
(which are the Kummer and Artin–Schreier calculations): finite direct image is exact and
preserves cohomology, and the normalisation exact sequence
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar` has a third term whose
cohomology is concentrated in degree zero and invariant under field extension.
(blueprint: `lemma-weil-pbc-curve-normalization-constant`) -/
theorem IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite {k : Type u} [Field k]
    [IsAlgClosed k] {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] [Smooth (ν ≫ f)] (V : X.Opens)
    (hV : Dense (V : Set X)) [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j]
    {j' : U' ⟶ X'} [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime]
    (H : IsCurve.Assertions Λ (ν ≫ f)
      ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))) :
    IsCurve.Assertions Λ f ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)) :=
  sorry

end AlgebraicGeometry
