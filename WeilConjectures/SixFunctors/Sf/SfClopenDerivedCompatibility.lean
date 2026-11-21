/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfClopenRestrictionData
import WeilConjectures.SixFunctors.Sf.SfClopenScalarQuotientComparison
import WeilConjectures.SixFunctors.Sf.SfClopenPreservesCompleteness
import WeilConjectures.SixFunctors.Sf.SfClopenPreservesResidueTor
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Normalized derived reduction and completeness on a clopen component

## References

* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem sf_clopen_localization_naturality
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{t}} {U : T.Opens}
    (d : SfClopenCoefficientRestriction l E T U)
    {P Q : CochainComplex (scalarReductionSource l E T) ℤ} (f : P ⟶ Q) :
    (sfClopenDerivedRestriction d).map (DerivedCategory.Q.map f) ≫
        (sfClopenLocalizationIso d Q).hom =
      (sfClopenLocalizationIso d P).hom ≫
        DerivedCategory.Q.map ((sfClopenComplexRestriction d).map f) := by
  let := d.additive
  let := d.limits
  let := d.colimits
  exact (sfClopenModuleRestriction U _ _ d.completion).mapDerivedCategoryFactors_hom_naturality f

private theorem sf_clopen_transition_tensor
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t})
    (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) (q : ℤ)
    (V : T.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E T (n + 1)).obj.obj V)
    (x : (P.X q).val.obj V) :
    ((unrestrictedTowerTransition l E T P n).f q).val.app V
        (unrestrictedTowerTensorSection l E T (n + 1) (P.X q) V s x) =
      unrestrictedTowerTensorSection l E T n (P.X q) V
        ((integralCoefficientSheafTransition l E T n).hom.app V s) x := by
  exact (unrestrictedIntegralTransition_existsUnique l E T n).exists.choose_spec P q V s x

/-- Exact ordinary restriction to a clopen preserves the actual normalized quotient
complexes, their augmented towers, derived completeness and objectwise residue Tor bounds. -/
theorem sf_clopen_derived_compatibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    Nonempty (SfClopenCompleteRestriction d) := by
  obtain ⟨reduction, finite_quotient, quotient, hfinite, hcounit, hquotient⟩ :=
    sf_clopen_scalar_quotient_comparison l E T U hU d
  have htransition (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenComplexRestriction d).map (unrestrictedTowerTransition l E T P n) ≫
          (quotient P n).hom =
        (quotient P (n + 1)).hom ≫
          unrestrictedTowerTransition l E U.toScheme ((sfClopenComplexRestriction d).obj P) n := by
    apply (cancel_epi (quotient P (n + 1)).inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply HomologicalComplex.hom_ext
    intro q
    apply unrestrictedReduction_hom_ext l E U.toScheme (n + 1)
    intro V s x
    change ((quotient P n).hom.f q).val.app V
        (((unrestrictedTowerTransition l E T P n).f q).val.app
          (op ((sfClopenSiteInclusion U).obj V.unop))
          (((quotient P (n + 1)).inv.f q).val.app V
            (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
              (((sfClopenComplexRestriction d).obj P).X q) V s x))) =
      ((unrestrictedTowerTransition l E U.toScheme
        ((sfClopenComplexRestriction d).obj P) n).f q).val.app V
          (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
            (((sfClopenComplexRestriction d).obj P).X q) V s x)
    have hinv :
        ((quotient P (n + 1)).inv.f q).val.app V
            (unrestrictedTowerTensorSection l E U.toScheme (n + 1)
              (((sfClopenComplexRestriction d).obj P).X q) V s x) =
          unrestrictedTowerTensorSection l E T (n + 1) (P.X q)
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) x := by
      have h := congrArg (((quotient P (n + 1)).inv.f q).val.app V)
        (hquotient P (n + 1) q V.unop s x)
      have hid := congrArg
        (fun f ↦ ((f.f q).val.app V)
          (unrestrictedTowerTensorSection l E T (n + 1) (P.X q)
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) x))
        (quotient P (n + 1)).hom_inv_id
      exact h.symm.trans hid
    rw [hinv, sf_clopen_transition_tensor, sf_clopen_transition_tensor]
    have hcoeff :
        (integralCoefficientSheafTransition l E T n).hom.app
            (op ((sfClopenSiteInclusion U).obj V.unop))
            ((d.finite (n + 1)).hom.hom.app V s) =
          (d.finite n).hom.hom.app V
            ((integralCoefficientSheafTransition l E U.toScheme n).hom.app V s) := by
      exact congrArg (fun f ↦ (f.hom.app V).hom s) (d.transition n)
    rw [hcoeff]
    exact hquotient P n q V.unop
      ((integralCoefficientSheafTransition l E U.toScheme n).hom.app V s) x
  have hunit (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenComplexRestriction d).map (unrestrictedTowerUnit l E T P n) ≫
          (quotient P n).hom =
        unrestrictedTowerUnit l E U.toScheme ((sfClopenComplexRestriction d).obj P) n := by
    ext q V x
    change ((quotient P n).hom.f q).val.app V
        (((unrestrictedTowerUnit l E T P n).f q).val.app
          (op ((sfClopenSiteInclusion U).obj V.unop)) x) =
      ((unrestrictedTowerUnit l E U.toScheme
        ((sfClopenComplexRestriction d).obj P) n).f q).val.app V x
    have hglobal := congrArg (((quotient P n).hom.f q).val.app V)
      (unrestrictedTowerUnit_condition l E T P n q
        (op ((sfClopenSiteInclusion U).obj V.unop)) x)
    have hlocal := unrestrictedTowerUnit_condition l E U.toScheme
      ((sfClopenComplexRestriction d).obj P) n q V x
    apply hglobal.trans
    apply Eq.trans _ hlocal.symm
    simpa only [map_one] using hquotient P n q V.unop 1 x
  let component (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :=
    sfClopenLocalizationIso d (unrestrictedTowerComplex l E T n P) ≪≫
      DerivedCategory.Q.mapIso (quotient P n)
  have naturality (P : CochainComplex (scalarReductionSource l E T) ℤ) (n : ℕ) :
      (sfClopenDerivedRestriction d).map
          (DerivedCategory.Q.map (unrestrictedTowerTransition l E T P n)) ≫
          (component P n).hom =
        (component P (n + 1)).hom ≫
          DerivedCategory.Q.map
            (unrestrictedTowerTransition l E U.toScheme
              ((sfClopenComplexRestriction d).obj P) n) := by
    dsimp only [component, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, sf_clopen_localization_naturality, Category.assoc,
      ← DerivedCategory.Q.map_comp, htransition, DerivedCategory.Q.map_comp, Category.assoc]
  let comparison (P : CochainComplex (scalarReductionSource l E T) ℤ) :
      canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ⟶
        canonicalIntegralReductionTower l E U.toScheme
          ((sfClopenComplexRestriction d).obj P) :=
    NatTrans.ofOpSequence (fun n ↦ (component P n).hom) (by
      intro n
      simpa only [Functor.comp_map, canonicalIntegralReductionTower,
        Functor.ofOpSequence_map_homOfLE_succ] using naturality P n)
  let tower (P : CochainComplex (scalarReductionSource l E T) ℤ) :
      canonicalIntegralReductionTower l E T P ⋙ sfClopenDerivedRestriction d ≅
        canonicalIntegralReductionTower l E U.toScheme
          ((sfClopenComplexRestriction d).obj P) :=
    NatIso.ofComponents (fun n ↦ component P n.unop) (by
      intro i j f
      exact (comparison P).naturality f)
  refine ⟨{
    reduction := reduction
    finite_quotient := finite_quotient
    finite_quotient_tensor := hfinite
    reduction_counit := hcounit
    quotient := quotient
    quotient_tensor := hquotient
    tower := tower
    tower_quotient := fun _ _ ↦ rfl
    tower_unit := ?_
    complete := sf_clopen_preserves_completeness l E T U hU d
    tor := sf_clopen_preserves_residue_tor l E T U hU d }⟩
  intro P n
  change (sfClopenDerivedRestriction d).map
      (DerivedCategory.Q.map (unrestrictedTowerUnit l E T P n)) ≫
        ((sfClopenLocalizationIso d (unrestrictedTowerComplex l E T n P)).hom ≫
          DerivedCategory.Q.map (quotient P n).hom) = _
  rw [← Category.assoc, sf_clopen_localization_naturality, Category.assoc,
    ← DerivedCategory.Q.map_comp, hunit]

end WeilConjectures
