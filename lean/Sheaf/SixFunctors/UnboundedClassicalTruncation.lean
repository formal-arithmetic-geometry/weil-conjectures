/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClassicalDefinition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.KInjectiveBridge

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Fixed-degree truncation for pro-etale sections

Source: the Weil conjectures blueprint, `sk-prop-pe-unbounded-classical`, node
`det-pe-unbounded-classical-truncation` (blueprint: det-pe-unbounded-classical-truncation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite

namespace AlgebraicGeometry.ProEtale

/-- The constant (possibly noncommutative) coefficient ring sheaf on the small pro-etale site.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable def coefficientRingSheaf (X : Scheme.{u}) (A : Type u) [Ring A] :
    Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
    (RingCat.of (ULift.{u + 1, u} A))

/-- The category of sheaves of left modules over the coefficient ring sheaf.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
abbrev coefficientModules (X : Scheme.{u}) (A : Type u) [Ring A] :=
  SheafOfModules.{u + 1} (coefficientRingSheaf X A)

/-- Evaluation of coefficient-module sheaves at a pro-etale object, with scalars forgotten.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable abbrev evaluationAb (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt) : coefficientModules X A ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.forget (coefficientRingSheaf X A) ⋙
    PresheafOfModules.evaluation (coefficientRingSheaf X A).obj (op W) ⋙
    forget₂ (ModuleCat.{u + 1}
      ((coefficientRingSheaf X A).obj.obj (op W))) AddCommGrpCat.{u + 1}

/-- The total right derived evaluation functor on the unbounded derived category.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable def derivedSections (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt) [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    DerivedCategory (coefficientModules X A) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (evaluationAb X A W).rightDerivedFunctor

/-- Cohomology of derived sections at `W`, computed in the derived category of abelian groups.
Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation). -/
noncomputable def sectionCohomology (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt) [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (q : ℤ) (H : coefficientModules X A) : AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
    ((derivedSections X A W).obj
      ((DerivedCategory.singleFunctor (coefficientModules X A) (0 : ℤ)).obj H))

private theorem classicalModule_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    {H H' : SheafOfModules.{u + 1} R} (e : H ≅ H')
    (hH : IsClassicalModuleSheaf H) : IsClassicalModuleSheaf H' := by
  exact (isClassical_iso_iff
    ((SheafOfModules.toSheaf R ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).mapIso e)).mp hH

private theorem finite_range_upper_bound
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (P : C → Prop)
    (hPiso : ∀ {H H' : C}, (H ≅ H') → P H → P H')
    (e : ℤ) (hF : ∀ (H : C), P H → ∀ p : ℤ, e < p →
      IsZero ((DerivedCategory.homologyFunctor D p).obj
        (F.obj ((DerivedCategory.singleFunctor C 0).obj H))))
    (K : DerivedCategory C) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q : ℤ, a ≤ q → q ≤ b →
      P ((DerivedCategory.homologyFunctor C q).obj K))
    (r : ℤ) (hr : b + e < r) :
    IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj K)) := by
  suffices H : ∀ (n : ℕ) (K : DerivedCategory C) (a b : ℤ), b - a ≤ n →
      K.IsGE a → K.IsLE b →
      (∀ q : ℤ, a ≤ q → q ≤ b → P ((DerivedCategory.homologyFunctor C q).obj K)) →
      ∀ r : ℤ, b + e < r →
        IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj K)) from
    H (b - a).toNat K a b (by omega) inferInstance inferInstance hK r hr
  intro n
  induction n with
  | zero =>
    intro K a b hab _ _ hK r hr
    by_cases hlt : b < a
    · exact (DerivedCategory.homologyFunctor D r).map_isZero
        (F.map_isZero (DerivedCategory.TStructure.t.isZero K b a hlt))
    · have : K.IsGE b := DerivedCategory.TStructure.t.isGE_of_ge K b a (by omega)
      obtain ⟨Y, ⟨eY⟩⟩ :=
        DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
      have hY : P Y := hPiso
        ((DerivedCategory.homologyFunctor C b).mapIso eY ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app Y)
        (hK b (by omega) le_rfl)
      apply (hF Y hY (r - b) (by omega)).of_iso
      exact (DerivedCategory.homologyFunctor D r).mapIso
        (F.mapIso eY ≪≫ F.mapIso
          (((DerivedCategory.singleFunctors C).shiftIso (-b) b 0 (by omega)).app Y).symm ≪≫
          (F.commShiftIso (-b)).app _) ≪≫
        ((DerivedCategory.homologyFunctor D 0).shiftIso (-b) r (r - b) (by omega)).app _
  | succ n ih =>
    intro K a b hab _ _ hK r hr
    by_cases hlt : b < a
    · exact (DerivedCategory.homologyFunctor D r).map_isZero
        (F.map_isZero (DerivedCategory.TStructure.t.isZero K b a hlt))
    have hab' : a ≤ b := by omega
    let t := DerivedCategory.TStructure.t (C := C)
    let T := (t.triangleLTGE b).obj K
    have hT := F.map_distinguished _ (t.triangleLTGE_distinguished b K)
    have h₁ : IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj T.obj₁)) := by
      refine ih T.obj₁ a (b - 1) (by omega) (inferInstanceAs
        (t.IsGE ((t.truncLT b).obj K) a))
        (t.isLE_truncLT_obj K b (b - 1) (by omega)) ?_ r (by omega)
      intro q hqa hqb
      have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K b q (by omega)
      exact hPiso
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncLTι b).app K))).symm
        (hK q hqa (by omega))
    have h₃ : IsZero ((DerivedCategory.homologyFunctor D r).obj (F.obj T.obj₃)) := by
      refine ih T.obj₃ b b (by omega) (inferInstanceAs
        (t.IsGE ((t.truncGE b).obj K) b)) (inferInstanceAs
        (t.IsLE ((t.truncGE b).obj K) b)) ?_ r hr
      intro q hqb hbq
      have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K b q hqb
      exact hPiso
        (asIso ((DerivedCategory.homologyFunctor C q).map ((t.truncGEπ b).app K)))
        (hK q (by omega) hbq)
    exact (DerivedCategory.HomologySequence.exact₂ _ hT r).isZero_of_both_zeros
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem rightDerived_preserves_countable_products
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasCountableProducts C] [HasCountableProducts D] [CountableAB4Star D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.rightDerivedFunctor := by
  classical
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let a : G ⋙ DerivedCategory.Q ≅
      q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso D).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors _).symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let β : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    a.hom ≫ Functor.whiskerLeft q F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C)
        F.rightDerivedFunctor).hom
  have hβ (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (β.app I) := by
    dsimp [β, a]
    infer_instance
  obtain ⟨hP, hQ, _⟩ := derivedCategory_countableProducts_core D
  have : ∀ (I : ℕ → CochainComplex D ℤ),
      PreservesLimit (Discrete.functor I) DerivedCategory.Q := fun I ↦
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQ ℕ I).some
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := D)) :=
    preservesLimitsOfShape_of_discrete _
  have hfamily (K : ℕ → DerivedCategory C) :
      PreservesLimit (Discrete.functor K) F.rightDerivedFunctor := by
    have hex (n : ℕ) := DerivedCategory.exists_iso_Q_obj_of_isKInjective (K n)
    choose I hI he using hex
    let e (n : ℕ) := (Classical.choice (he n)).symm
    have : ∀ n, (I n).IsKInjective := hI
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    obtain ⟨hPI, ⟨hPL⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit I
    have : CochainComplex.IsKInjective P.pt := hPI
    have hFPL := isLimitOfPreserves DerivedCategory.Q
      (isLimitOfPreserves G (HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor I)))
    let α : Discrete.functor I ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ e n.as)
    let c := (Cone.postcompose α.hom).obj (DerivedCategory.Q.mapCone P)
    have hc : IsLimit c := (IsLimit.postcomposeHomEquiv α _).symm hPL
    apply preservesLimit_of_preserves_limit_cone hc
    let αβ : (Discrete.functor I ⋙ G) ⋙ DerivedCategory.Q ≅
        (Discrete.functor I ⋙ DerivedCategory.Q) ⋙ F.rightDerivedFunctor :=
      Discrete.natIso (fun (n : Discrete ℕ) ↦ asIso (β.app (I n.as)))
    have hmap : IsLimit (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P)) :=
      (IsLimit.equivOfNatIsoOfIso αβ
        (DerivedCategory.Q.mapCone (G.mapCone P))
        (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
        (Cone.ext (asIso (β.app P.pt)) (fun n ↦ by
          simpa [αβ] using β.naturality (P.π.app n)))).1 hFPL
    exact (IsLimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight α F.rightDerivedFunctor)
      (F.rightDerivedFunctor.mapCone (DerivedCategory.Q.mapCone P))
      (F.rightDerivedFunctor.mapCone c) (Cone.ext (Iso.refl _) (fun n ↦ by simp [c]))).1 hmap
  exact preservesLimitsOfShape_of_discrete _

private theorem classical_upper_bound
    (X : Scheme.{u}) (A : Type u) [Ring A]
    (W : X.ProEt)
    [HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}]
    [(Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (e : ℕ)
    (hbound : ∀ (q : ℤ) (H : coefficientModules X A),
      IsClassicalModuleSheaf H → q > e → IsZero (sectionCohomology X A W q H))
    (L : DerivedCategory (coefficientModules X A)) (b : ℤ)
    (hclass : ∀ q : ℤ, q ≤ b → IsClassicalModuleSheaf
      ((DerivedCategory.homologyFunctor (coefficientModules X A) q).obj L))
    (hL : ∀ q : ℤ, b < q → IsZero
      ((DerivedCategory.homologyFunctor (coefficientModules X A) q).obj L))
    (m : ℤ) (hm : b + e + 1 < m) : IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} m).obj
        ((derivedSections X A W).obj L)) := by
  let C := coefficientModules X A
  let F := evaluationAb X A W
  let RF := F.rightDerivedFunctor
  let K := DerivedCategory.Q.objPreimage L
  let T := Scheme.ProEt.postnikovTower K
  let P := ∏ᶜ (fun n : ℕ ↦ T.obj (op n))
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1}
  have hK : (DerivedCategory.Q.obj K).IsLE b :=
    (DerivedCategory.isLE_iff _ _).2 fun q hq ↦
      (hL q hq).of_iso ((DerivedCategory.homologyFunctor C q).mapIso
        (DerivedCategory.Q.objObjPreimageIso L))
  have htrunc (n : ℕ) (r : ℤ) (hr : b + e < r) :
      IsZero ((H r).obj (RF.obj (DerivedCategory.Q.obj (T.obj (op n))))) := by
    have : (DerivedCategory.Q.obj (T.obj (op n))).IsGE (-(n : ℤ)) := by
      change (DerivedCategory.Q.obj (K.truncGE (-(n : ℤ)))).IsGE (-(n : ℤ))
      infer_instance
    have : (DerivedCategory.Q.obj (T.obj (op n))).IsLE b := by
      rw [DerivedCategory.isLE_iff]
      intro q hq
      by_cases hnq : -(n : ℤ) ≤ q
      · have := K.quasiIsoAt_πTruncGE (-(n : ℤ)) q hnq
        exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj K) b q hq).of_iso
          ((DerivedCategory.homologyFunctorFactors C q).app K ≪≫
            asIso (HomologicalComplex.homologyMap (K.πTruncGE (-(n : ℤ))) q) ≪≫
            (DerivedCategory.homologyFunctorFactors C q).symm.app _).symm
      · exact DerivedCategory.isZero_of_isGE _ (-(n : ℤ)) q (by omega)
    refine finite_range_upper_bound RF (fun Y : C ↦ IsClassicalModuleSheaf Y)
      (fun e h ↦ @classicalModule_of_iso X (coefficientRingSheaf X A) _ _ e h) e
      (fun Y hY q hq ↦ hbound q Y hY hq)
      _ (-(n : ℤ)) b ?_ r hr
    intro q hnq hqb
    have := K.quasiIsoAt_πTruncGE (-(n : ℤ)) q hnq
    refine @classicalModule_of_iso X (coefficientRingSheaf X A) _ _
      ((DerivedCategory.homologyFunctor C q).mapIso
          (DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
        (DerivedCategory.homologyFunctorFactors C q).app K ≪≫
        asIso (HomologicalComplex.homologyMap (K.πTruncGE (-(n : ℤ))) q) ≪≫
        (DerivedCategory.homologyFunctorFactors C q).symm.app _)
      (hclass q hqb)
  have hFprod : PreservesLimitsOfShape (Discrete ℕ) F := by
    change PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.evaluation (coefficientRingSheaf X A) (op W) ⋙
        forget₂ (ModuleCat.{u + 1} ((coefficientRingSheaf X A).obj.obj (op W)))
          AddCommGrpCat.{u + 1})
    infer_instance
  have hCP : HasCountableProducts C := inferInstance
  have hDP : HasCountableProducts AddCommGrpCat.{u + 1} := inferInstance
  have hAB : CountableAB4Star AddCommGrpCat.{u + 1} := by
    refine ⟨fun J ↦ ?_⟩
    exact HasExactLimitsOfShape.of_domain_equivalence AddCommGrpCat.{u + 1}
      (Discrete.equivalence Equiv.ulift : Discrete (ULift.{u + 1} J) ≌ Discrete J)
  have hRF : PreservesLimitsOfShape (Discrete ℕ) RF :=
    rightDerived_preserves_countable_products.{u + 1, u + 2, u + 1, u + 2}
      (C := C) (D := AddCommGrpCat.{u + 1}) F
  obtain ⟨hprod, _, _⟩ := Scheme.ProEt.products_derived.{u, 0} X (coefficientRingSheaf X A)
    ℕ (fun n : ℕ ↦ T.obj (op n))
  obtain ⟨hAbProd, _, hH⟩ := derivedCategory_countableProducts_core AddCommGrpCat.{u + 1}
  have hP (r : ℤ) (hr : b + e < r) :
      IsZero ((H r).obj (RF.obj (DerivedCategory.Q.obj P))) := by
    have : PreservesLimitsOfShape (Discrete ℕ) (H r) := hH ℕ r
    have hh := isLimitOfPreserves (H r) (isLimitOfPreserves RF hprod.some)
    exact hh.isZero_pt (Functor.isZero _ fun j ↦ htrunc j.as r hr)
  let φ := towerTransitionEndomorphism
    (K := fun n : ℕ ↦ T.obj (op n)) (WeilConjectures.integralOperationsTowerStep T)
  have hT := RF.map_distinguished _ (DerivedCategory.mappingCocone_triangle_distinguished φ)
  have hRoos : IsZero ((H m).obj
      (RF.obj (DerivedCategory.Q.obj (WeilConjectures.integralOperationsRoos T)))) := by
    exact (DerivedCategory.HomologySequence.exact₁ _ hT (m - 1) m (by omega)).isZero_of_both_zeros
      ((hP (m - 1) (by omega)).eq_of_src _ _) ((hP m (by omega)).eq_of_tgt _ _)
  have := Scheme.ProEt.left_complete_quasiIso.{u, 0} X (coefficientRingSheaf X A) K
  have : IsIso (DerivedCategory.Q.map (Scheme.ProEt.postnikovComparison K)) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C _) _
      ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)
  exact hRoos.of_iso ((H m).mapIso (RF.mapIso
    ((DerivedCategory.Q.objObjPreimageIso L).symm ≪≫
      asIso (DerivedCategory.Q.map (Scheme.ProEt.postnikovComparison K)))))

/-- A finite coefficient ring has cohomological dimension `e` on classical module sheaves at
`W`, and then unbounded classical complexes satisfy the stated vanishing and truncation
comparison. Source: blueprint `det-pe-unbounded-classical-truncation`
(blueprint: det-pe-unbounded-classical-truncation).

Proof (blueprint detail, Parts (1) and (2)):

1. Evaluation is additive, left exact, and preserves countable products, by sectionwise
kernels and limits (`lem-weil-pbc-module-sheaves-limits-sectionwise`). The ringed-site module
category and abelian groups are Grothendieck (`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-weil-pbc-ring-modules-grothendieck-abelian`), so functorial K-injective resolutions exist
(`lem-weil-pbc-kinjective-functorial-existence`). The total derived functor is computed on
K-injectives (`lem-weil-pbc-kinjective-total-derived`), commutes with shifts and preserves
triangles (`lem-pc-right-derived-functor-triangulated`). Bounded-below injective resolutions
identify its value on `H[0]` with ordinary evaluation cohomology
(`lem-sc-bounded-below-injective-resolution`, `def-sp-left-exact-additive`).

2. Set `C_n = τ_{≥-n} L`. Its cohomology lies in `[-n,b]` and is classical, since zero
sheaves are classical (`def-kun-truncations`, `sk-def-pe-classical-definition`). If `b < -n`,
it is acyclic and hence zero in the derived category (`def-weil-abstract-derived-category`).

3. Otherwise put `a = -n`. For fixed `m > b+e`, induct on `r` from `a-1` to `b` using
`τ_{≤r-1} C_n → τ_{≤r} C_n → H^r(C_n)[-r]`
(`lem-weil-pbc-truncation-triangle`). The base truncation is zero; the last term after derived
evaluation has degree-`m` cohomology `H^{m-r}(W,H^r(C_n))`, zero because `m-r > e`.
The long exact sequence (`lem-sf-derived-homology-long-exact`) propagates vanishing. Since
`τ_{≤b} C_n → C_n` is a quasi-isomorphism, every `C_n` has this bound.

4. Choose K-injective resolutions `E_n → J_n`. Their termwise product is K-injective and
represents the derived product (`lem-pc-ringed-space-product-kinjective`). Evaluation commutes
with this product and its projections. Exact products of abelian groups
(`lem-pc-abelian-groups-exact-products`) and `lem-weil-derived-limit-products-core` identify the
evaluated product with the product in `D(Ab)`. Thus derived evaluation preserves these products
with their specified projections, not merely up to an unspecified object isomorphism.

5. Left completeness (`det-pe-left-complete-iso`) and `det-pe-products-derived` identify `L`
with the fibre of `1-T` on the product of the `C_n` (`def-weil-derived-limit`). Apply the
triangulated derived evaluation and Step 4. Projection by projection, the image of `T` is the
shift map induced by the transitions on the evaluated tower. Hence the image triangle is the
specified Roos triangle for `B_n = RΓ(W,C_n)`.

6. The abelian-group Milnor sequence (`lem-pc-derived-limit-milnor-sequence`) has outside
terms `R¹lim H^{m-1}(B_n)` and `lim H^m(B_n)`. For `m > b+e+1`, both towers are zero by
Step 3, so the middle term is zero. This proves clause (1) with its stated bound.

7. For clause (2) take `L = τ_{<N} K` and `b = N-1`. Clause (1) gives vanishing above
`N+e`. The standard truncation triangle (`def-sbc-standard-tstructure-derived-category`) has
canonical middle map `K → τ_{≥N} K`; the quotient-to-truncation map is a quasi-isomorphism
by the truncation cohomology formulas (`def-kun-truncations`). Apply derived evaluation and
its long exact sequence. Since `N < m-e-1` implies `m > N+e+1`, the outside terms in degrees
`m` and `m+1` vanish, and the middle map is an isomorphism. All maps retain the coefficient
action; the inverse of a bijective linear map is linear, so underlying groups suffice. -/
theorem unbounded_classical_truncation
    (X : Scheme.{u}) (A : Type u) [Ring A] [Finite A]
    (W : X.ProEt) [HasDerivedCategory (coefficientModules X A)]
    [Abelian.HasKInjectiveResolutions (coefficientModules X A)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (e : ℕ)
    (hbound : ∀ (q : ℤ) (H : coefficientModules X A),
      IsClassicalModuleSheaf H → q > e → IsZero (sectionCohomology X A W q H))
    : (∀ (L : DerivedCategory (coefficientModules X A))
      (_hL : IsClassicalModuleComplex L) (b : ℤ),
      (∀ (q : ℤ), b < q → IsZero
        ((DerivedCategory.homologyFunctor (coefficientModules X A) q).obj L)) →
      ∀ (m : ℤ), b + e + 1 < m → IsZero
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} m).obj
          ((derivedSections X A W).obj L))) ∧
    (∀ (K : DerivedCategory (coefficientModules X A))
      (_hK : IsClassicalModuleComplex K) (m N : ℤ),
      N < m - e - 1 → IsIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} m).map
          ((derivedSections X A W).map
            ((CategoryTheory.Triangulated.TStructure.truncGEπ
              DerivedCategory.TStructure.t N).app K)))) := by
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    surjectiveTower_hasSheafify.{u, 0} X
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    surjectiveTower_wEqualsLocallyBijective.{u, 0} X
  have hvanish := classical_upper_bound X A W e hbound
  constructor
  · intro L hL b hb m hm
    exact hvanish L b (fun q _ ↦ hL q) hb m hm
  · intro K hK m N hN
    let t := DerivedCategory.TStructure.t (C := coefficientModules X A)
    let L := (t.truncLT N).obj K
    have hc : ∀ q : ℤ, q ≤ N - 1 → IsClassicalModuleSheaf
        ((DerivedCategory.homologyFunctor (coefficientModules X A) q).obj L) := by
      intro q hq
      have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K N q (by omega)
      refine @classicalModule_of_iso X (coefficientRingSheaf X A) _ _
        (asIso ((DerivedCategory.homologyFunctor (coefficientModules X A) q).map
          ((t.truncLTι N).app K))).symm (hK q)
    have hb : ∀ q : ℤ, N - 1 < q → IsZero
        ((DerivedCategory.homologyFunctor (coefficientModules X A) q).obj L) := by
      have : L.IsLE (N - 1) := t.isLE_truncLT_obj K N (N - 1) (by omega)
      exact (DerivedCategory.isLE_iff L (N - 1)).mp inferInstance
    have hT := (evaluationAb X A W).rightDerivedFunctor.map_distinguished _
      (t.triangleLTGE_distinguished N K)
    exact DerivedCategory.isIso_homologyMap_mor₂ _ hT m (m + 1) rfl
      (hvanish L (N - 1) hc hb m (by omega))
      (hvanish L (N - 1) hc hb (m + 1) (by omega))

end AlgebraicGeometry.ProEtale
