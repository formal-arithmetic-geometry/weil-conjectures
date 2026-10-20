/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SfClassFullCohomologicalDimension
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction

/-!
# The relative interpretation of the exceptional adjoint

Source: Weil blueprint, sk-prop-sf-existence, cor-sf-ambient-adjoint-discharge
(blueprint: cor-sf-ambient-adjoint-discharge).
The statement below spells out exactly the class-restricted vanishing and natural
relative Hom bijections. It imposes no ambient exceptional datum.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

section FixedCounit

open scoped CategoryTheory.Functor

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [CompactSpace Y] [QuasiCompact f]

variable [HasCompactification f]

private noncomputable def fixedAdjunction :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⊣
      Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f :=
  (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso Λ c).symm

private noncomputable def fixedDischargeCounit
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.TStructure.t.plus L) :
    (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj
      ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ⟶ L :=
  ((fixedCompactSupportComparisonIso Λ c).app
      ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩).hom ≫
    D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map ((fixedAdjunction Λ c).counit.app _) ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).counit.app L

/-- The counit of the exceptional adjunction is natural in the bounded below `L`. -/
@[reassoc]
private lemma fixedDischargeCounit_naturality
    {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) (hL' : DerivedCategory.TStructure.t.plus L')
    (φ : L ⟶ L') :
    (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map
      ((R(f)^![ModuleCat.{u + 1} Λ]).map φ) ≫
        fixedDischargeCounit Λ c L' hL' =
      fixedDischargeCounit Λ c L hL ≫ φ := by
  have h := (fixedCompactSupportComparisonIso Λ c).hom.naturality
    (X := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩)
    (Y := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL'⟩)
    (ObjectProperty.homMk ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).map
      (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).map φ)))
  dsimp at h
  simp only [fixedDischargeCounit, rightDerivedUpperShriek, Functor.comp_map,
    Iso.app_hom]
  have h2 := (fixedAdjunction Λ c).counit_naturality
    (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).map φ)
  have h3 := (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).counit_naturality φ
  rw [reassoc_of% h, ← Functor.map_comp_assoc]
  erw [h2]
  rw [Functor.map_comp_assoc]
  erw [h3]
  simp

/-- The key computation behind `rightDerivedUpperShriekHomEquiv`: for `K'` bounded below,
`g ↦ Rf_! g ≫ ε_L` sends `ν^* h`, for `h : K' ⟶ f^× Rν_* L`, to the image of `h` under the chain
of adjunction bijections, read through the compact-support comparison at `K'`. -/
private lemma fixedDischarge_map_comp_counit
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L)
    (h : K' ⟶ (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f).obj
      (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L)) :
    (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map h) ≫
        fixedDischargeCounit Λ c L hL =
      ((fixedCompactSupportComparisonIso Λ c).app ⟨K', hK'⟩).hom ≫
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _).symm
          (((fixedAdjunction Λ c).homEquiv _ _).symm h) := by
  have hn := (fixedCompactSupportComparisonIso Λ c).hom.naturality
    (X := ⟨K', hK'⟩) (Y := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩)
    (ObjectProperty.homMk h)
  dsimp at hn
  simp only [fixedDischargeCounit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, Iso.app_hom]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ z ≫
      D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map ((fixedAdjunction Λ c).counit.app _) ≫
        (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).counit.app L) hn

/-- For `K'` bounded below and `L` bounded below, `g ↦ Rf_! g ≫ ε_L` is a bijection
`Hom(ν^* K', Rf^! L) ≃ Hom(Rf_! ν^* K', L)`. -/
private lemma fixedDischarge_bijective_of_plus
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K'
      ⟶ (R(f)^![ModuleCat.{u + 1} Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g
      ≫ fixedDischargeCounit Λ c L hL) := by
  let E := (((fixedAdjunction Λ c).homEquiv K' _).symm.trans
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm).trans
      (((fixedCompactSupportComparisonIso Λ c).app ⟨K', hK'⟩).symm.homFromEquiv (Z := L))
  have hcomp : (fun g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K'
      ⟶ (R(f)^![ModuleCat.{u + 1} Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g
      ≫ fixedDischargeCounit Λ c L hL) ∘
        (fun h ↦ D(ν^*(X)[ModuleCat.{u + 1} Λ]).map h) = ⇑E := by
    ext h
    exact fixedDischarge_map_comp_counit Λ c hK' hL h
  have hν := bijective_comparisonUpperStar_mapDerivedCategory_map K' _
    (plus_etaleRightDerivedUpperShriek_obj f hL)
  refine (Function.Bijective.of_comp_iff _ hν).1 ?_
  rw [hcomp]
  exact E.bijective

/-- For `K` bounded below of étale origin and `L` bounded below, `g ↦ Rf_! g ≫ ε_L` is a
bijection `Hom(K, Rf^! L) ≃ Hom(Rf_! K, L)`. -/
private lemma fixedDischarge_bijective
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : K ⟶ (R(f)^![ModuleCat.{u + 1} Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g
      ≫ fixedDischargeCounit Λ c L hL) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  have h : (fun g : K ⟶ (R(f)^![ModuleCat.{u + 1} Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g
      ≫ fixedDischargeCounit Λ c L hL) =
      ⇑((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c
      ).mapIso e).homFromEquiv ∘
        (fun g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K' ⟶ (R(f)^![ModuleCat.{u + 1} Λ]).obj L ↦
          (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).map g
      ≫ fixedDischargeCounit Λ c L hL) ∘
        ⇑e.symm.homFromEquiv := by
    ext g
    simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.symm_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [h]
  exact ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c
      ).mapIso e).homFromEquiv.bijective.comp
    ((fixedDischarge_bijective_of_plus Λ c hK' hL).comp
      e.symm.homFromEquiv.bijective)

end FixedCounit

/-- The bounded-class interpretation combines the sharp class vanishing bound and the
relative adjunction for the explicitly defined transported etale functor. The inverse
Hom map sends a to Rf_!(a) followed by the relative counit eps; functoriality gives
naturality in its source, and the last equation gives naturality in its target.
Source: blueprint, cor-sf-ambient-adjoint-discharge
(blueprint: cor-sf-ambient-adjoint-discharge).
Proof: thm-sf-fullcd-class gives FullCD_cls with bound 2d on the proper part, uniformly
on the weakly-etale base changes. This uses etale-origin sheaves only, not all sheaves.
Theorem thm-sf-ambient-adjoint-class supplies the relative Hom bijections and coherent
compactification comparisons for bounded-below etale-origin K and every bounded-below
L. Substituting the defining formula ν_X^* f× Rν_Y* identifies the right-hand functor
with sfFiniteExceptionalFixed. Its relative counit supplies eps, and the Hom
bijections give the asserted bijectivity. Their naturality gives the last equation.
No unrestricted ambient adjunction or all-sheaf dimension bound follows. -/
theorem sfConstructibleExceptionalAdjointDischarge
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (d : ℕ)
    (_hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    sfClassFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E (n + 1))
        (2 * d) ∧
    ∃ eps : ∀ (L : DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
        (_hL : DerivedCategory.TStructure.t.plus L),
      (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L) ⟶ L,
      (∀ (L) (hL : DerivedCategory.TStructure.t.plus L) (K)
          (_hK : (DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1}
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
                X).mapDerivedCategory).essImage K),
        Function.Bijective (fun a : K ⟶
            (sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).obj L ↦
          (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map a ≫
            eps L hL)) ∧
      ∀ (L L') (hL : DerivedCategory.TStructure.t.plus L)
          (hL' : DerivedCategory.TStructure.t.plus L') (a : L ⟶ L'),
        (sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).map
            ((sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c).map a) ≫
              eps L' hL' = eps L hL ≫ a := by
  let Λ := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  let : HasCompactification f := c.hasCompactification
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (CommRingCat.of Dk.k))
  refine ⟨?_, fixedDischargeCounit Λ c, ?_, ?_⟩
  · let : IsAlgClosed Dk.k := IsAlgClosure.isAlgClosed Dk.k₀
    let aY := Y ↘ Spec (CommRingCat.of Dk.k)
    have van {X' Y' : Scheme.{u}} (q : X' ⟶ c.Z) (p : X' ⟶ Y') (g : Y' ⟶ Y)
        (sq : IsPullback q p c.g g)
        (M : Sheaf (ProEt.topology X') (ModuleCat.{u + 1} Λ))
        (hM : etaleOrigin (ModuleCat.{u + 1} Λ) X' M) (r : ℤ)
        (hr : (2 * d : ℤ) < r) :
        IsZero ((DerivedCategory.homologyFunctor _ r).obj
          ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
      have : IsProper p := MorphismProperty.of_isPullback sq inferInstance
      obtain ⟨M₀, ⟨e⟩⟩ := hM
      have hv := Etale.isZero_higherDirectImage_of_isPullback_of_isProper Λ c.g
        (c.g ≫ aY) aY rfl d _hd sq M₀ r hr
      let K := (DerivedCategory.Plus.singleFunctor _ 0).obj M₀
      refine IsZero.of_iso
        (Functor.map_isZero (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y') hv) ?_
      exact (DerivedCategory.homologyFunctor _ r).mapIso
          ((lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.mapIso
            (((DerivedCategory.singleFunctor _ 0).mapIso e).symm ≪≫
              (((comparisonUpperStar (ModuleCat.{u + 1} Λ) X').mapDerivedCategorySingleFunctor
                0).app M₀).symm) ≪≫
            ((rightDerivedLowerStarComparisonIso' p (ModuleCat.{u + 1} Λ)).app K).symm) ≪≫
        (((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategoryHomologyFunctorIso
          r).app _).symm
    constructor
    · intro M hM r hr
      exact van (𝟙 _) c.g (𝟙 _) (IsPullback.of_id_fst (f := c.g)) M hM r
        (by exact_mod_cast hr)
    · intro V M hM r hr
      exact van (pullback.fst c.g V.hom) (pullback.snd c.g V.hom) V.hom
        (IsPullback.of_hasPullback c.g V.hom) _
        (etaleOrigin_upperStar_obj (pullback.fst c.g V.hom) hM) r
        (by exact_mod_cast hr)
  · intro L hL K hK
    apply fixedDischarge_bijective Λ c _ hL
    obtain ⟨K₀, ⟨e⟩⟩ := hK
    exact ⟨K₀.obj, K₀.property, ⟨e⟩⟩
  · intro L L' hL hL' a
    exact fixedDischargeCounit_naturality Λ c hL hL' a

end AlgebraicGeometry.ProEtale
