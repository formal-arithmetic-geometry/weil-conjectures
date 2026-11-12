/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstruction
public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.IntegralTowers
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint

/-!
# The integral right adjoint built from towers

Let `E/ℚ_ℓ` be finite, `k` an algebraic closure of a finite field of characteristic `p ≠ ℓ`, and
`f : X ⟶ Y` a separated morphism of finite type between schemes of finite type over `k`, with a
compactification `c`. Let `Rf_{!,𝒪_E} : Dᵇc(X, 𝒪_E) ⥤ Dᵇc(Y, 𝒪_E)` be the integral direct image
with compact support (`sfCompactSupportFiniteIntegralFunctor`).

On towers, `Rf_{!,•}` has a right adjoint `f^!_•` on normalized constructible towers
(`ExceptionalIntegralReconstruction.Systems.exceptional`, with the adjunction
`ExceptionalIntegralReconstruction.SystemAdjunction`). Blueprint
`proposition-sp-integral-adjunction` transports this adjunction to integral complexes along the
equivalence `red ⊣ R lim` between `Dᵇc(-, 𝒪_E)` and normalized constructible towers (blueprint
`lemma-sp-tower-adjunction-foundation`): the functor
`H_{f,𝒪_E}(K) = R lim_n f^!_• (red_Y K)` is right adjoint to `Rf_{!,𝒪_E}`, and it is therefore
identified with any other right adjoint, such as `f^!_{𝒪_E}`, by a unique counit-preserving
isomorphism.

## Main statements

* `AlgebraicGeometry.ProEtale.exists_towerLimit_rightAdjoint_sfCompactSupport`: blueprint
  `proposition-sp-integral-adjunction--1`.
* `AlgebraicGeometry.ProEtale.exists_towerLimit_rightAdjoint_sfCompactSupport_uniq`: blueprint
  `proposition-sp-integral-adjunction--2`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

open WeilConjectures WeilConjectures.IntegralSystemRealization
  WeilConjectures.ExceptionalIntegralReconstruction

/-- The full subcategories of two equal object properties are equivalent, compatibly with the
inclusions. -/
private def fullSubcategoryEquivOfEq {C : Type*} [Category* C] {P Q : ObjectProperty C}
    (h : P = Q) : P.FullSubcategory ≌ Q.FullSubcategory where
  functor := ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.ge
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] (c : Compactification f)

/-- Blueprint `proposition-sp-integral-adjunction--2`: **the integral right adjoint built from
towers, and its uniqueness**. There are a right adjoint `f^!_•` of `Rf_{!,•}` on normalized
constructible towers and a right adjoint `H` of `Rf_{!,𝒪_E}` on `Dᵇc(-, 𝒪_E)` with
`H(K) ≅ R lim_n f^!_• (red_Y K)` (blueprint `proposition-sp-integral-adjunction--1`), and for every
right adjoint `G` of `Rf_{!,𝒪_E}`, for instance the exceptional inverse image `f^!_{𝒪_E}`, there
is a unique isomorphism `H ≅ G` compatible with the counits. -/
theorem exists_towerLimit_rightAdjoint_sfCompactSupport_uniq :
    ∃ (s : Systems l E c) (_ : SystemAdjunction l E c s)
      (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
      (adj : sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ H),
      Nonempty (H ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E Y).ι ⋙ (calculus l E Y).reduction ⋙
          s.exceptional l E c ⋙ coefficientSequenceLimit l E X) ∧
      ∀ (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
        (adj' : sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G),
        ∃! e : H ≅ G, ∀ N, (sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E).map (e.hom.app N) ≫
            adj'.counit.app N = adj.counit.app N := by
  obtain ⟨-, rX, rY, s, a, ⟨R⟩⟩ := exceptionalIntegralReconstruction l E D hl f c
  let eX := fullSubcategoryEquivOfEq
    (finiteTorConstructibleIntegral_eq_sfIntegralConstructible l E D hl X)
  let eY := fullSubcategoryEquivOfEq
    (finiteTorConstructibleIntegral_eq_sfIntegralConstructible l E D hl Y)
  let ψ : ((eX.inverse ⋙ integralLeft l E c rX rY s a) ⋙ eY.functor) ⋙
      (sfIntegralConstructible l E Y).ι ≅
      sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⋙
          (sfIntegralConstructible l E Y).ι :=
    Functor.isoWhiskerLeft eX.inverse
      (Functor.isoWhiskerRight R.identification (finiteTorConstructibleIntegral l E Y).ι ≪≫
        (finiteTorConstructibleIntegral l E Y).liftCompιIso _ _)
  let φ := ((sfIntegralConstructible l E Y).fullyFaithfulι.whiskeringRight _).preimageIso ψ
  let adj := ((eX.symm.toAdjunction.comp (integralAdjunction l E c rX rY s a)).comp
    eY.toAdjunction).ofNatIsoLeft φ
  exact ⟨s, a, _, adj,
    ⟨Functor.isoWhiskerLeft eY.inverse (rightComposite l E c rX rY s a)⟩,
    fun G adj' ↦ adj.existsUnique_iso_comp_counit adj'⟩

/-- Blueprint `proposition-sp-integral-adjunction--1`: **the integral right adjoint built from
towers**. There are a right adjoint `f^!_•` of `Rf_{!,•}` on normalized constructible towers and
a right adjoint `H` of `Rf_{!,𝒪_E}` on `Dᵇc(-, 𝒪_E)`, obtained by transporting the tower
adjunction along `red ⊣ R lim`, with `H(K) ≅ R lim_n f^!_• (red_Y K)`. -/
theorem exists_towerLimit_rightAdjoint_sfCompactSupport :
    ∃ (s : Systems l E c) (_ : SystemAdjunction l E c s)
      (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X),
      Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ H) ∧
      Nonempty (H ⋙ (sfIntegralConstructible l E X).ι ≅
        (sfIntegralConstructible l E Y).ι ⋙ (calculus l E Y).reduction ⋙
          s.exceptional l E c ⋙ coefficientSequenceLimit l E X) := by
  obtain ⟨s, a, H, adj, h, -⟩ :=
    exists_towerLimit_rightAdjoint_sfCompactSupport_uniq l E D hl f c
  exact ⟨s, a, H, ⟨adj⟩, h⟩

end AlgebraicGeometry.ProEtale
