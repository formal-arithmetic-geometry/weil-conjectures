/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor
import WeilConjectures.SixFunctors.Completed.CompletedScalarCanonicalAssociatorFormula
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages

/-! # Field-tower coherence of the explicit integral comparison

For a tower of coefficient fields, the explicit integral comparisons compose, through the
integral scalar associator, to the direct comparison.

## Implementation details

The associator is passed as an argument `assoc` together with its defining equation `hassoc`
(the defining equation `integralTensorAssociator_eq` of `integralTensorAssociator`, which lives
in a module importing this one). By `completedScalarCanonicalAssociatorFormula`, the integral
associator `sfIntegralScalarComp` is the ordinary derived associator `tensorComposition`
conjugated by the three completion comparisons. Naturality of the balancing isomorphism cancels
the comparisons, and what remains is associativity of balanced derived extension,
`pbcReductionNormalization_assoc`.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Propositions 3.5.1 and 6.8.14(2),
  Remark 6.8.15
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

private theorem leftAdjointUniq_ofNatIsoRight {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (adj : F ⊣ G) (e : G ≅ G') (adj' : F' ⊣ G') :
    Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj' =
      (conjugateIsoEquiv adj' adj).symm e.symm := by
  ext X
  apply ((adj.ofNatIsoRight e).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight, conjugateIsoEquiv, Equiv.symm_mk, Equiv.coe_fn_mk,
    Iso.symm_hom, Iso.symm_inv, conjugateEquiv_symm_apply_app, Adjunction.homEquiv_unit,
    Functor.comp_obj, NatTrans.comp_app, Functor.id_obj, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp]
  rw [← e.hom.naturality, ← Category.assoc, ← Adjunction.homEquiv_unit, ← Category.assoc,
    ← Functor.map_comp, ← Adjunction.homEquiv_counit]
  simp

private theorem tensorComposition_eq {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d) :
    PurCompactSupport.tensorComposition a b d h =
      Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction d)
        (pbcDerivedRestrictComp a b d h) :=
  leftAdjointUniq_ofNatIsoRight _ _ _

private theorem balancing_assoc {R₀ R₁ R₂ R₃ : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃) (d : R₀ ⟶ R₂) (e : R₁ ⟶ R₃) (f : R₀ ⟶ R₃)
    (hab : a ≫ b = d) (hbc : b ≫ c = e) (hdc : d ≫ c = f) (hae : a ≫ e = f)
    (K : DerivedCategory (pbcModules X R₀)) :
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction e) (pbcDerivedScalarAdjunction f)
        (pbcDerivedRestrictComp a e f hae)).inv.app K ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction b)
        (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction e)
        (pbcDerivedRestrictComp b c e hbc)).inv.app ((pbcDerivedExtend a).obj K) ≫
      (pbcDerivedExtend c).map ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction d)
        (pbcDerivedRestrictComp a b d hab)).hom.app K) =
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction d)
        (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction f)
        (pbcDerivedRestrictComp d c f hdc)).inv.app K := by
  have H := pbcReductionNormalization_assoc a b c d e f hab hbc hdc hae K
  simp only [pbcReductionNormalization_hom_eq] at H
  rw [← cancel_mono ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction d)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction f)
    (pbcDerivedRestrictComp d c f hdc)).hom.app K), Category.assoc, Category.assoc, H]
  simp

private theorem cancel_aux {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
    {FL : 𝒜 ⥤ 𝒞} {Fb : 𝒜 ⥤ ℬ} {FM : ℬ ⥤ 𝒞} (β : FL ⟶ Fb ⋙ FM)
    {P : 𝒞} {A T : 𝒜} {S W : ℬ} (p : P ⟶ FL.obj A) (x : A ⟶ T) (y : Fb.obj T ⟶ S)
    (w : S ⟶ W) (z : Fb.obj A ⟶ W) (hz : Fb.map x ≫ y ≫ w = z) :
    p ≫ FL.map x ≫ β.app T ≫ FM.map y ≫ FM.map w = p ≫ β.app A ≫ FM.map z := by
  have h := β.naturality x
  simp only [Functor.comp_map] at h
  rw [reassoc_of% h, ← hz]
  simp only [Functor.map_comp]

private theorem comp_map_comp {𝒜 𝒞 : Type*} [Category 𝒜] [Category 𝒞] (F : 𝒜 ⥤ 𝒞)
    {P Q : 𝒞} {A B D : 𝒜} (p : P ⟶ Q) (q : Q ⟶ F.obj A) (r : A ⟶ B) (s : B ⟶ D)
    (t : P ⟶ F.obj B) (hz : p ≫ q ≫ F.map r = t) :
    p ≫ q ≫ F.map (r ≫ s) = t ≫ F.map s := by
  rw [← hz, F.map_comp]
  simp only [Category.assoc]

private theorem chi_cancel (E L : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (i : E →ₐ[Padic l] L)
    (K : DerivedCategory (integralTowerModules l E X))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    (completedTensorComparison l X E L i).app K ≫ (CompletedLineTensor.chi l E X L i K hK).inv =
      𝟙 _ :=
  (CompletedLineTensor.chi l E X L i K hK).hom_inv_id

private theorem map_chi_cancel {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {Z : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) M) X)}
    (g : (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) L)
        (Coefficient.{u} l (PadicAlgCl l) M) (coefficientInclusion l (PadicAlgCl l) L M k) X)).obj
      ((pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
          X)).obj K.obj) ⟶ Z) :
    (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) L)
        (Coefficient.{u} l (PadicAlgCl l) M) (coefficientInclusion l (PadicAlgCl l) L M k) X)).map
        ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)).app
            K.obj) ≫
      (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) L)
        (Coefficient.{u} l (PadicAlgCl l) M) (coefficientInclusion l (PadicAlgCl l) L M k) X)).map
        (CompletedLineTensor.chi l (Coefficient.{u} l (PadicAlgCl l) E) X
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) K.obj
          (CompletedLineTensor.intrinsic_complete l _ X K)).inv ≫ g = g := by
  rw [← Functor.map_comp_assoc, chi_cancel, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem associator_formula {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (pbcDerivedExtend (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) L)
        (Coefficient.{u} l (PadicAlgCl l) M) (coefficientInclusion l (PadicAlgCl l) L M k) X)).map
        ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)).app
            K.obj) ≫
      (completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) L)
          (Coefficient.{u} l (PadicAlgCl l) M) (coefficientInclusion l (PadicAlgCl l) L M k)).app
        ((integralScalarExtensionOfUniverses l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)
            X).obj K.obj) ≫
      ((sfIntegralScalarComp l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X 0
        (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) L M k)).hom.app K).hom =
    (PurCompactSupport.tensorComposition _ _ _
        (PurCompactSupport.completedMap_composition l _ _ _ _ _ X)).hom.app K.obj ≫
      (completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) M) ((coefficientInclusion l (PadicAlgCl l) L M k).comp
            (coefficientInclusion l (PadicAlgCl l) E L h))).app K.obj := by
  simp only [completedScalarCanonicalAssociatorFormula]
  rw [reassoc_of% (chi_cancel l X _ _ (coefficientInclusion l (PadicAlgCl l) L M k)
    ((integralScalarExtensionOfUniverses l (Coefficient.{u} l (PadicAlgCl l) E)
      (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X).obj
        K.obj)
    (CompletedLineTensor.extension_complete l _ X _ _ K.obj
      (CompletedLineTensor.intrinsic_complete l _ X K))), map_chi_cancel]
  rfl

variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

private theorem tower_aux (C : CoefficientSystem l X) {E L M : Index l (PadicAlgCl l)}
    (h : E ≤ L) (k : L ≤ M)
    (m : Coefficient.{u} l (PadicAlgCl l) E →ₐ[Padic l] Coefficient.{u} l (PadicAlgCl l) M)
    (hm : (coefficientInclusion l (PadicAlgCl l) L M k).comp
      (coefficientInclusion l (PadicAlgCl l) E L h) = m)
    (hs : completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) M) m X ≫ (C.coefficient M).integralMap l X =
      (C.coefficient E).integralMap l X)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (integralTensorComparison l X C h).app K ≫
      (integralTensorComparison l X C k).app
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition
          l (PadicAlgCl l) X E L h).obj K) ≫
        (integralTensor l X C M).map
          ((sfIntegralScalarComp l (Coefficient.{u} l (PadicAlgCl l) E)
              (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X 0
              (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) M)
              (coefficientInclusion l (PadicAlgCl l) L M k) ≪≫
            eqToIso (congrArg (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l (PadicAlgCl l) E)
              (Coefficient.{u} l (PadicAlgCl l) M) i X) hm)).hom.app K) =
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction
        (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) M) m X))
      (pbcDerivedScalarAdjunction ((C.coefficient M).integralMap l X))
      (pbcDerivedScalarAdjunction ((C.coefficient E).integralMap l X))
      (pbcDerivedRestrictComp (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) M) m X)
        ((C.coefficient M).integralMap l X) ((C.coefficient E).integralMap l X) hs)).inv.app
        K.obj ≫
      (pbcDerivedExtend ((C.coefficient M).integralMap l X)).map
        ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) M) m).app K.obj) := by
  subst hm
  simp only [integralTensorComparison_app, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id]
  simp only [integralTensor, Functor.comp_map, ObjectProperty.ι_map]
  simp only [Category.assoc]
  refine (cancel_aux (integralTensorBalancing l X C k).inv _ _ _ _ _
    (associator_formula l X h k K)).trans ?_
  refine comp_map_comp (pbcDerivedExtend ((C.coefficient M).integralMap l X)) _ _ _ _ _ ?_
  rw [tensorComposition_eq]
  exact balancing_assoc X _ _ _ _ _ _ _ _ _ _ K.obj

/-- For a tower `E ≤ L ≤ M`, the explicit integral comparisons compose, through the
integral scalar associator `assoc`, to the direct comparison. Here `hassoc` identifies
`assoc` with `sfIntegralScalarComp` followed by equality transport along the
field-inclusion composition law. -/
theorem integralTensorComparison_tower (C : CoefficientSystem l X)
    (assoc : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M),
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ⋙
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) L) (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) L M k) X ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) E M (h.trans k)) X)
    (hassoc : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M),
      assoc h k =
        sfIntegralScalarComp l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) X
          0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) M)
          (coefficientInclusion l (PadicAlgCl l) L M k) ≪≫
        eqToIso (congrArg
          (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) M) i X)
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l
            (PadicAlgCl l)).2 E L M h k))) :
    ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      (integralTensorComparison l X C h).app K ≫
        (integralTensorComparison l X C k).app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition
            l (PadicAlgCl l) X E L h).obj K) ≫
        (integralTensor l X C M).map ((assoc h k).hom.app K) =
      (integralTensorComparison l X C (h.trans k)).app K := by
  intro E L M h k K
  rw [hassoc, integralTensorComparison_app l X C (h.trans k) K, integralTensorBalancing]
  exact tower_aux l X C h k (coefficientInclusion l (PadicAlgCl l) E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l (PadicAlgCl l)).2 E L M h k)
    (C.coefficient_scalar E M (h.trans k)) K

end WeilConjectures.LocallyFiniteAdicRealization
