/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek

/-!
# The étale reading lands in objects of étale origin

Let `T` be a finite discrete commutative ring and `Φ` the comparison of the two models of
pro-étale sheaves with coefficients in `T` (`ProEtale.finiteCoefficientModEquivalence`), and its
derived version (`ProEtale.finiteCoefficientDerivedEquivalence`).

* **The constructibility dictionary**
  (`ProEtale.isConstructible_finiteCoefficientModEquivalence_obj`): `Φ` sends a constructible
  module object over `T_X = p_X^* T̲` (on the strata of a stratification, pro-étale locally
  finitely presented) to an intrinsically constructible sheaf of `T`-modules (on the strata,
  locally constant with finite stalks). Pro-étale locally, a finitely presented module object
  becomes the constant sheaf of a finite `T`-module
  (`ProEtale.isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj`), and being locally
  constant with finite stalks is local for the pro-étale topology
  (`ProEtale.IsFiniteLocallyConstant.of_cover`).
* Hence `Φ` sends bounded constructible condensed complexes to intrinsically bounded
  constructible pro-étale complexes
  (`ProEtale.boundedConstructibleIntrinsic_finiteCoefficientDerivedEquivalence`).
* **Clause (ii) of blueprint `lem-sf-proetale-constructible-origin`**
  (`ProEtale.DerivedCategory.boundedConstructibleIntrinsic_le_boundedConstructible`): at a finite
  coefficient ring, intrinsically bounded constructible pro-étale complexes are of étale origin.
  By clause (i) their cohomology sheaves are of étale origin, so they are `ν^* K'` for a bounded
  below étale complex `K'` (`ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology`);
  `K'` is bounded with constructible cohomology sheaves, `ν^*` being exact and fully faithful.
* Together: `ProEtale.CondensedRing.etaleOriginReading`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Being locally constant with finite stalks is local for the pro-étale topology**: if the
pullbacks of `F` to the members of a pro-étale covering family are locally constant with finite
stalks, so is `F`. -/
theorem IsFiniteLocallyConstant.of_cover {X : Scheme.{u}} {ι : Type (u + 1)}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (h : ∀ i, IsFiniteLocallyConstant Λ (((g i)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    IsFiniteLocallyConstant Λ F := by
  choose κ V v hv hM using h
  refine ⟨Σ i, κ i, fun p ↦ V p.1 p.2, fun p ↦ v p.1 p.2 ≫ g p.1,
    Precoverage.IsStableUnderComposition.comp_mem_coverings g hg v hv, fun p ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hM p.1 p.2
  exact ⟨M, hM, ⟨(ProEtale.upperStarComp _ (v p.1 p.2) (g p.1)).app F ≪≫ e⟩⟩

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The constructibility dictionary**: the comparison `Φ_X` sends a constructible module object
over `T_X = p_X^* T̲` to an intrinsically constructible sheaf of `T`-modules on `X_proét`. On each
stratum `Xₐ` of a stratification for `M`, the restriction of `M` is finitely presented on the
members `U` of a pro-étale cover of `Xₐ`, so `Φ_U(M|_U) ≅ (Φ_X M)|_U` is locally constant with
finite stalks (`ProEtale.isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj`), hence so
is `(Φ_X M)|_{Xₐ}` (`ProEtale.IsFiniteLocallyConstant.of_cover`). -/
theorem isConstructible_finiteCoefficientModEquivalence_obj {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)}
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj T) X) M) :
    IsConstructible (ULift.{u + 1} T) ((finiteCoefficientModEquivalence X T).functor.obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hS a
  have h : Presieve.ofArrows (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.X i.down) (fun i ↦ 𝒰.f i.down) =
      𝒰.presieve₀ := by
    refine le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩) fun _ _ ⟨i⟩ ↦ ?_
    exact Presieve.ofArrows.mk (ι := ULift.{u + 1} 𝒰.I₀) (Y := fun i ↦ 𝒰.X i.down) ⟨i⟩
  refine IsFiniteLocallyConstant.of_cover (fun i : ULift.{u + 1} 𝒰.I₀ ↦ 𝒰.f i.down)
    (h ▸ 𝒰.mem₀) fun i ↦ ?_
  have hP := CondensedRing.isFinitelyPresented_upperStar_of_comap_iso
    (Profinite.continuousMapRingObj T) (𝒰.f i.down)
    (condensedPullbackHom (Profinite.continuousMapRingObj T) (S.immersion a))
    (CondensedRing.comapUpperStarObjIso _ (S.immersion a) M) (h𝒰 i.down)
  exact isFiniteLocallyConstant_of_iso
    (((𝒰.f i.down)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].mapIso
      ((finiteCoefficientModUpperStarIso T (S.immersion a)).app M) ≪≫
      (finiteCoefficientModUpperStarIso T (𝒰.f i.down)).app _).symm)
    (isFiniteLocallyConstant_finiteCoefficientModEquivalence_obj hP)

/-- The derived comparison `Φ_X` sends bounded constructible condensed complexes over `T_X` to
intrinsically bounded constructible pro-étale complexes of `T`-modules: `Φ_X` is induced by an
exact equivalence, which preserves boundedness and commutes with the cohomology sheaves, and it
sends constructible cohomology sheaves to constructible ones
(`ProEtale.isConstructible_finiteCoefficientModEquivalence_obj`). -/
theorem boundedConstructibleIntrinsic_finiteCoefficientDerivedEquivalence {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) K) :
    DerivedCategory.boundedConstructibleIntrinsic (ULift.{u + 1} T) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj K) :=
  ⟨(finiteCoefficientModEquivalence X T).functor.bounded_mapDerivedCategory_obj hK.1,
    fun q ↦ isConstructible_of_iso
      (((finiteCoefficientModEquivalence X T).functor.mapDerivedCategoryHomologyFunctorIso
        q).app K)
      (isConstructible_finiteCoefficientModEquivalence_obj T (hK.2 q))⟩

/-- Blueprint `lem-sf-proetale-constructible-origin`: Constructible pro-étale coefficients are
of étale origin, clause (ii).

At a finite coefficient ring `Λ`, a bounded complex `K` of sheaves of `Λ`-modules on the small
pro-étale site of `X` whose cohomology sheaves are constructible (in the intrinsic sense of
`def-weil-finite-torsion-constructibility`,
`ProEtale.DerivedCategory.boundedConstructibleIntrinsic`) is of étale origin
(`ProEtale.DerivedCategory.boundedConstructible`): it is `ν^* K'` for a bounded constructible
étale complex `K'`. By clause (i)
(`ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`) the cohomology sheaves of
`K` are `ν^*` of constructible étale sheaves, so the dévissage along the truncation triangles
(`ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology`) gives `K ≅ ν^* K'` for a
bounded below `K'`. As `ν^*` is exact and fully faithful, `K'` is bounded and its cohomology
sheaves are the constructible étale sheaves of clause (i). -/
theorem DerivedCategory.boundedConstructibleIntrinsic_le_boundedConstructible [Finite Λ]
    (X : Scheme.{u}) :
    DerivedCategory.boundedConstructibleIntrinsic Λ X ≤
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X := by
  rintro K ⟨hb, hc⟩
  have hK (q : ℤ) := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj Λ (hc q)
  obtain ⟨K', ⟨a, ha⟩, ⟨e⟩⟩ := DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology
    (hK := fun q ↦ (hK q).elim fun G hG ↦ ⟨G, hG.2⟩) (hb := hb)
  obtain ⟨b, hb'⟩ := hb.2
  have : (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K').IsLE b :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  refine ⟨K', ⟨⟨⟨a, ha⟩, ⟨b, isLE_of_isLE_mapDerivedCategory_comparisonUpperStar this⟩⟩,
    fun q ↦ ?_⟩, ⟨e⟩⟩
  obtain ⟨G, hG, ⟨eG⟩⟩ := hK q
  exact IsConstructibleSheaf.of_iso ((ν^*(X)[ModuleCat.{u + 1} Λ]).preimageIso
    (eG ≪≫ ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e).symm ≪≫
      (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app K').symm))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- **The étale reading lands in objects of étale origin**: for every bounded constructible
condensed `𝒪_E ⧸ ℓⁿ`-complex `M` on `X`, the pro-étale complex `Φ(M)` is of étale origin. It is
intrinsically bounded constructible
(`ProEtale.boundedConstructibleIntrinsic_finiteCoefficientDerivedEquivalence`), hence of étale
origin by `lem-sf-proetale-constructible-origin` (ii)
(`ProEtale.DerivedCategory.boundedConstructibleIntrinsic_le_boundedConstructible`). -/
theorem etaleOriginReading (X : Over (Spec (.of k))) : EtaleOriginReading ℓ E n X := fun M ↦
  DerivedCategory.boundedConstructibleIntrinsic_le_boundedConstructible X.left _
    (boundedConstructibleIntrinsic_finiteCoefficientDerivedEquivalence _ M.property)

end AlgebraicGeometry.ProEtale.CondensedRing
