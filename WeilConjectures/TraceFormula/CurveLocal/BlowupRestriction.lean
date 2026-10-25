/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction

/-!

# The blow-up restriction vanishing

This file states the geometric vanishing used by the curve route of the trace formula
(blueprint `sk-lem-tf-blowup-restriction`, proved in its own subsection by blowing up the closed
point, see `sk-rem-tf-curve-local-proof`):

Let `T` be the strict localization of a smooth surface over an algebraically closed field `k` at a
closed point `t`, `H` a regular curve through `t` and `D`, `B` reduced closed curves through `t`
whose tangent cones satisfy `C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`. Let
`i : T ∖ (D ∪ H) ⟶ T ∖ D` and let `E` be a bounded complex on `T ∖ (D ∪ H)` with finite locally
constant cohomology and finite `ℓ`-group monodromy. Then the restriction
`RΓ(T ∖ D, i_! E) ⟶ RΓ(B ∖ t, (i_! E)|_{B ∖ t})` is zero in `D(Λ)`.

The tangent cone condition is expressed in the local ring `R` of `T` through the ideals `I`, `J`
of the two curves (`IsLocalRing.TangentConesMeetAtOrigin`): the supports of the tangent cones
`Spec (gr_𝔪 R / in I)` and `Spec (gr_𝔪 R / in J)` meet only at the origin if and only if the
ideal `in I + in J` of the graded ring `gr_𝔪 R` contains all homogeneous elements of large degree,
that is, if `𝔪^N ⊆ (I ∩ 𝔪^N) + (J ∩ 𝔪^N) + 𝔪^(N+1)` for all large `N`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The *tangent cones of `R ⧸ I` and `R ⧸ J` meet only at the origin*: the initial ideals
`in I` and `in J` in the associated graded ring `gr_𝔪 R = ⊕ 𝔪^N / 𝔪^(N+1)` together contain every
homogeneous element of large degree, i.e. `𝔪^N ⊆ (I ∩ 𝔪^N) + (J ∩ 𝔪^N) + 𝔪^(N+1)` for all large
`N`. For curves `D`, `B` through the closed point of a surface `Spec R` with ideals `I`, `J`,
this is the condition `C_t D ∩ C_t B = {0}` of blueprint `sk-lem-tf-blowup-restriction`. -/
def TangentConesMeetAtOrigin (I J : Ideal R) : Prop :=
  ∃ n : ℕ, ∀ N ≥ n, maximalIdeal R ^ N ≤
    I ⊓ maximalIdeal R ^ N ⊔ J ⊓ maximalIdeal R ^ N ⊔ maximalIdeal R ^ (N + 1)

end IsLocalRing

namespace AlgebraicGeometry.Etale

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The ideal of global sections of a closed subscheme `d : D ⟶ Spec R` of an affine scheme. -/
noncomputable def specIdeal {R : CommRingCat.{u}} {D : Scheme.{u}} (d : D ⟶ Spec R) : Ideal R :=
  RingHom.ker ((Scheme.ΓSpecIso R).inv ≫ d.appTop).hom

/-- **Blow-up restriction vanishing** (blueprint `sk-lem-tf-blowup-restriction`; SGA 5, III B,
§§2–4). Let `T = Spec R` be the strict localization of a smooth surface `S` over the algebraically
closed field `k` at a `k`-point `s`, `ℓ` a prime invertible in `k` and `Λ` a finite commutative
`ℓ`-primary ring. Let `H` be a regular curve through the closed point `t` (its ring is a discrete
valuation ring) and `D`, `B` reduced closed curves through `t` whose tangent cones satisfy
`C_t D ∩ C_t B = {0}` and `C_t D ∩ T_t H = {0}`. Let `i : T ∖ (D ∪ H) ⟶ T ∖ D` and let `E` be a
bounded complex on `T ∖ (D ∪ H)` whose cohomology sheaves are trivialized by a finite étale Galois
cover with group a finite `ℓ`-group, with finite constant values (finite locally constant
cohomology with finite `ℓ`-group monodromy). Then the restriction
`RΓ(T ∖ D, i_! E) ⟶ RΓ(B ∖ t, (i_! E)|_{B ∖ t})` is zero in `D(Λ)`; here `B ∖ t = B ∩ (T ∖ D)`,
since the tangent cone condition forces `B ∩ D = {t}`.

This is the statement of the blueprint node of the subsection `sk-lem-tf-blowup-restriction`,
whose own task proves it. -/
theorem sectionsRestriction_app_eq_zero_of_tangentConesMeetAtOrigin
    {S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 aS]
    (s : Spec (.of k) ⟶ S) (hs : s ≫ aS = 𝟙 _) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    {D H B : Scheme.{u}} (dD : D ⟶ strictLocalization s) (dH : H ⟶ strictLocalization s)
    (dB : B ⟶ strictLocalization s) [IsClosedImmersion dD] [IsClosedImmersion dH]
    [IsClosedImmersion dB] [Nonempty D] [Nonempty H] [Nonempty B]
    (hH : ∃ _ : IsDomain Γ(H, ⊤), IsDiscreteValuationRing Γ(H, ⊤))
    (hD : IsReduced D ∧ ringKrullDim Γ(D, ⊤) = 1)
    (hB : IsReduced B ∧ ringKrullDim Γ(B, ⊤) = 1)
    (hDB : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s) (specIdeal dD)
      (specIdeal dB))
    (hDH : IsLocalRing.TangentConesMeetAtOrigin (strictHenselization s) (specIdeal dD)
      (specIdeal dH))
    (E : DerivedCategory (Sheaf (dD.openComplement ⊓ dH.openComplement).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hE : (∃ a b : ℤ, E.IsGE a ∧ E.IsLE b) ∧ ∀ n : ℤ,
      ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (_ : IsPGroup ℓ G)
        (c : Scheme.GaloisCover G (dD.openComplement ⊓ dH.openComplement).toScheme)
        (M : ModuleCat.{u + 1} Λ) (_ : Finite M),
        Nonempty ((c.π)^*[ModuleCat.{u + 1} Λ].obj
            ((DerivedCategory.homologyFunctor _ n).obj E) ≅
          (constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    (sectionsRestriction (ModuleCat.{u + 1} Λ)
      (dB.resLE dD.openComplement (dB ⁻¹ᵁ dD.openComplement) le_rfl)
      (V := Scheme.Etale.mk (𝟙 _)) (W := Scheme.Etale.mk (𝟙 _))
      (dB.resLE dD.openComplement (dB ⁻¹ᵁ dD.openComplement) le_rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)).app
        (((strictLocalization s).homOfLE (inf_le_left :
          dD.openComplement ⊓ dH.openComplement ≤ dD.openComplement))_!open[ModuleCat.{u + 1} Λ]
          |>.mapDerivedCategory.obj E) = 0 :=
  sorry

end AlgebraicGeometry.Etale
