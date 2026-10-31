/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.SystemSingletonEvaluationMate
import WeilConjectures.CategoryTheory.SystemRestrictionMateCoherence
import WeilConjectures.CategoryTheory.InverseImageScalarRestrictionComparison

/-! # Scalar normalization of singleton evaluation and direct image

Source: Stacks Project, Tags 0D6D, 07A6 and 0D6E; Zheng, Construction 4.1.
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
  SheafOfModules.systemNormalizationSingleton
  SheafOfModules.systemNormalizationRestriction

namespace CategoryTheory

private theorem normalizedConjugateHom
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₁ ≅ L₂)
    (V : A) (Z : B) (f : V ⟶ R₁.obj Z) :
    b.homEquiv V Z (c.inv.app V ≫ (a.homEquiv V Z).symm f) =
      f ≫ (conjugateIsoEquiv a b c.symm).hom.app Z := by
  apply (b.homEquiv V Z).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_counit]
  rw [← Category.assoc, ← c.inv.naturality, Category.assoc]
  rfl

end CategoryTheory

namespace CategoryTheory.SystemEvaluationNormalization

universe a b c d va vb vc vd qA qB qA' qB'
variable {A : Type a} {B : Type b} {A' : Type c} {B' : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} A'] [Category.{vd} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{qA} A] [HasDerivedCategory.{qB} B]
  [HasDerivedCategory.{qA'} A'] [HasDerivedCategory.{qB'} B']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  {U : A ⥤ A'} {V : B ⥤ B'} [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitNormalized (adj : L ⊣ R) (adj' : L' ⊣ R')
    (s : L ⋙ V ≅ U ⋙ L') : UnitNormalized adj adj' s := by
  intro M
  have h := Adjunction.derivedExact_mateEquiv_app_fac adj adj'
    (TwoSquare.mk _ _ _ _ s.inv)
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).inv)
    (by
      intro N
      have hs := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj s.symm N
      have hi := (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (L ⋙ V)) (.up ℤ)).inv_hom_id_app N
      rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
      simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, hi,
        Category.id_comp, Category.comp_id] at hs
      rw [← cancel_epi (L'.mapDerivedCategoryFactorsh.inv.app
        ((U.mapHomotopyCategory (.up ℤ)).obj N) ≫
          L'.mapDerivedCategory.map (U.mapDerivedCategoryFactorsh.inv.app N))]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom,
        Iso.symm_inv, NatTrans.comp_app, Functor.mapDerivedCategorySquareIso,
        Functor.mapDerivedCategoryNatIso_symm] using hs) M
  dsimp only [UnitNormalized, derivedMate, ordinaryMate]
  erw [h]
  simp only [Iso.inv_hom_id_app_assoc]

end CategoryTheory.SystemEvaluationNormalization

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))


variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
  (hFB : SystemSingletonGeometricComparisons SY TY SX TX FB)
  (hFA : SystemSingletonGeometricComparisons SY TY SX TX FA)
  (HB : StrictRingSystem BX ⥤ StrictRingSystem BY) [HB.Additive]
  (HA : StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj AY)) [HA.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  (adjB : FB.functor ⊣ HB) (adjA : FA.functor ⊣ HA)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, FB.levelFunctor n ⊣ Hn n)
  (H0 : systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0 ⥤
    systemLevel ((Functor.const ℕᵒᵖ).obj AY) 0) [H0.Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)]
  (adj0 : FA.levelFunctor 0 ⊣ H0)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The singleton Hom comparison agrees with the resolution-normalized restriction
comparison, and preserves the actual counit and strict restriction-form transitions.
All four direct images are total right derived functors of the ordinary right adjoints
of the specified geometric inverse images; their adjunctions are induced before deriving.
The ordinary squares are constructed in the conclusion, with their underlying maps fixed,
and the resolution-unit equations pin their mates to the named composition comparisons.
Constant-ring strict systems are the ringed-sequence-site presentation of ordinary towers.

Source: Stacks Tags 0D6D, 07A6 and 0D6E; Zheng, Construction 4.1, printed p. 21, and
comparison before Lemma 4.10, printed p. 23. The scalar square is agent-formulated
(blueprint: lem-pur-system-evaluation-scalar-restriction-normalization).

Proof:
1. Compose the normalized singleton and geometric adjunctions on both sides. Conjugate
c_n inverse to obtain beta_B; its Hom action is exactly the displayed chain. This uses
lem-pur-system-level-left-extension, lem-pur-system-single-derived-extension,
lem-pur-system-singleton-geometric-pullback and def-weil-pbc-adjunction-conjugate.
2. Transpose beta_B applied to a test arrow. At level n singleton multiplication is the
identity, and the singleton triangle cancels its unit against its counit. Setting the
arrow to the identity gives the evaluated geometric counit equation.
3. Scalar restriction commutes with inverse image on underlying sheaves by the identity;
the pulled-back algebra square makes this identity linear. It also commutes with actual
strict transitions. The resulting ordinary squares have the stated underlying equations.
Use lem-sfb-ringed-comparison-tensor-adjunction and the two factorizations in
lem-pur-diagram-ring-restriction-pushforward: their derived mates are delta and kappa,
with the resolution-unit normalization of 0D6E, including for nonflat coefficients.
4. Repeat the singleton construction for constant coefficients. Its counit equation
identifies it with the unique constant-tower comparison of
lem-weil-pbc-tower-derived-evaluation-normalization. The ordinary tower evaluation mate
and its derived resolution-unit equation give the constant comparison normalization.
5. Resolve a test A-module by a flat-term K-flat complex (lem-pc-kflat-resolution).
Singleton extension and pullback preserve that resolving class by
lem-pur-system-singleton-scalar-extension and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The composition comparisons compute
termwise via lem-weil-pbc-ringed-topoi-derived-pullback on this same representative.
6. In the left-adjoint scalar/singleton square both paths send b tensor u-inverse(q)
to itself after multiplying coefficient factors, below n; above n both are the zero map.
The normalized singleton/scalar isomorphisms identify the right-adjoint evaluation and
restriction squares with the actual identity on sections, not with chosen level isos.
7. Apply Hom into Z and the two mate-pasting clauses (lem-weil-pbc-mate-pasting) to this
whole-system square. The two Hom transposes agree, giving the displayed scalar square.
8. For n at most m the actual derived strict transition is conjugate to the canonical
lower-singleton map by lem-pur-system-single-derived-evaluation. The final square of
lem-pur-system-singleton-geometric-pullback commutes with these lower-singleton maps.
Conjugating the canonical level restriction square identifies its inverse mate with chi,
by lem-pur-sheaf-ring-derived-coefficient-adjunction and the two-path comparison theorem.
9. Mate pasting now gives the restriction-form transition equation, including n=m.
Every comparison is a natural transformation, so these identities are natural for all Z.
No K-injective-preservation assertion for varying-ring evaluation is used. -/
theorem systemEvaluationScalarRestrictionNormalization
    (htransition : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (IB n).ringUnderlying.hom =
        (IB m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (halgebra : ∀ n : ℕ,
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (aY.app (op n))) ≫ (IB n).ringUnderlying.hom =
        IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (aX.app (op n))) :
    ∃ d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA,
    ∃ (delta : HB.rightDerivedFunctor ⋙ (systemNormalizationRestriction aY).mapDerivedCategory ≅
        (systemNormalizationRestriction aX).mapDerivedCategory ⋙ HA.rightDerivedFunctor)
      (kappa : ∀ n : ℕ,
        (Hn n).rightDerivedFunctor ⋙ (singletonLevelRestriction aY n).mapDerivedCategory ≅
          (singletonLevelRestriction aX n).mapDerivedCategory ⋙ H0.rightDerivedFunctor)
      (chi : ∀ {n m : ℕ} (h : n ≤ m),
        (systemRestriction BX h).mapDerivedCategory ⋙ (Hn m).rightDerivedFunctor ≅
          (Hn n).rightDerivedFunctor ⋙ (systemRestriction BY h).mapDerivedCategory),
      delta.hom = CategoryTheory.SystemEvaluationNormalization.derivedMate adjB adjA d.scalar ∧
      (∀ n : ℕ, (kappa n).hom =
        CategoryTheory.SystemEvaluationNormalization.derivedMate (adjn n) adj0 (d.level n)) ∧
      (∀ {n m : ℕ} (h : n ≤ m), (chi h).inv =
        CategoryTheory.SystemEvaluationNormalization.derivedMate
          (adjn n) (adjn m) (d.restriction h)) ∧
      CategoryTheory.SystemEvaluationNormalization.UnitNormalized adjB adjA d.scalar ∧
      (∀ n : ℕ, CategoryTheory.SystemEvaluationNormalization.UnitNormalized
        (adjn n) adj0 (d.level n)) ∧
      (∀ {n m : ℕ} (h : n ≤ m),
        CategoryTheory.SystemEvaluationNormalization.UnitNormalized
          (adjn n) (adjn m) (d.restriction h)) ∧
      (∀ n : ℕ,
        (systemNormalizationEvaluation SY TY SX TX FA HA adjA
          (fun _ ↦ H0) (fun _ ↦ adj0) hFA n).hom =
        CategoryTheory.SystemEvaluationNormalization.derivedMate adjA adj0 (FA.evaluation n)) ∧
      (∀ n : ℕ, CategoryTheory.SystemEvaluationNormalization.UnitNormalized
        adjA adj0 (FA.evaluation n)) ∧
      (∀ (n : ℕ) (V : DerivedCategory (systemLevel BY n))
        (Z : DerivedCategory (StrictRingSystem BX))
        (f : V ⟶ (derivedSystemEvaluation BY n).obj (HB.rightDerivedFunctor.obj Z)),
        ((adjn n).mapDerivedCategoryRightDerivedAdjunction.comp
          (systemSingleDerivedExtension BX n SX TX).adjunction).homEquiv V Z
          ((systemNormalizationSingleton SY TY SX TX FB hFB n).inv.app V ≫
            (((systemSingleDerivedExtension BY n SY TY).adjunction.comp
              adjB.mapDerivedCategoryRightDerivedAdjunction).homEquiv V Z).symm f) =
          f ≫ (systemNormalizationEvaluation SY TY SX TX FB HB adjB Hn adjn hFB n).hom.app Z) ∧
      (∀ (n : ℕ) (Z : DerivedCategory (StrictRingSystem BX)),
        (singletonLevelRestriction aY n).mapDerivedCategory.map
            ((systemNormalizationEvaluation SY TY SX TX FB HB adjB Hn adjn hFB n).hom.app Z) ≫
          (kappa n).hom.app ((derivedSystemEvaluation BX n).obj Z) =
        (systemNormalizationDerivedRestrictionEvaluation aY n).inv.app
            (HB.rightDerivedFunctor.obj Z) ≫
          (derivedSystemEvaluation ((Functor.const ℕᵒᵖ).obj AY) n).map (delta.hom.app Z) ≫
          (systemNormalizationEvaluation SY TY SX TX FA HA adjA
            (fun _ ↦ H0) (fun _ ↦ adj0) hFA n).hom.app
              ((systemNormalizationRestriction aX).mapDerivedCategory.obj Z) ≫
          H0.rightDerivedFunctor.map
            ((systemNormalizationDerivedRestrictionEvaluation aX n).hom.app Z)) ∧
      (∀ (n : ℕ) (Z : DerivedCategory (StrictRingSystem BX)),
        (derivedSystemEvaluation BX n).map
            (adjB.mapDerivedCategoryRightDerivedAdjunction.counit.app Z) =
          (FB.derivedEvaluation n).hom.app (HB.rightDerivedFunctor.obj Z) ≫
            (FB.levelFunctor n).mapDerivedCategory.map
              ((systemNormalizationEvaluation SY TY SX TX FB HB adjB Hn adjn hFB n).hom.app Z) ≫
            (adjn n).mapDerivedCategoryRightDerivedAdjunction.counit.app
              ((derivedSystemEvaluation BX n).obj Z)) ∧
      (∀ {n m : ℕ} (h : n ≤ m) (Z : DerivedCategory (StrictRingSystem BX)),
        (systemDerivedTransition BY h).app (HB.rightDerivedFunctor.obj Z) ≫
            (systemRestriction BY h).mapDerivedCategory.map
              ((systemNormalizationEvaluation SY TY SX TX FB HB adjB Hn adjn hFB n).hom.app Z) =
          (systemNormalizationEvaluation SY TY SX TX FB HB adjB Hn adjn hFB m).hom.app Z ≫
            (Hn m).rightDerivedFunctor.map ((systemDerivedTransition BX h).app Z) ≫
            (chi h).hom.app ((derivedSystemEvaluation BX n).obj Z)) := by
  classical
  have homComparison (n : ℕ) (V : DerivedCategory (systemLevel BY n))
      (Z : DerivedCategory (StrictRingSystem BX))
      (f : V ⟶ (derivedSystemEvaluation BY n).obj (HB.rightDerivedFunctor.obj Z)) :
      ((adjn n).mapDerivedCategoryRightDerivedAdjunction.comp
        (systemSingleDerivedExtension BX n SX TX).adjunction).homEquiv V Z
        ((systemNormalizationSingleton SY TY SX TX FB hFB n).inv.app V ≫
          (((systemSingleDerivedExtension BY n SY TY).adjunction.comp
            adjB.mapDerivedCategoryRightDerivedAdjunction).homEquiv V Z).symm f) =
        f ≫ (systemNormalizationEvaluation SY TY SX TX FB HB adjB Hn adjn hFB n).hom.app Z := by
    let a := (systemSingleDerivedExtension BY n SY TY).adjunction.comp
      adjB.mapDerivedCategoryRightDerivedAdjunction
    let b := (adjn n).mapDerivedCategoryRightDerivedAdjunction.comp
      (systemSingleDerivedExtension BX n SX TX).adjunction
    let c := systemNormalizationSingleton SY TY SX TX FB hFB n
    change b.homEquiv V Z (c.inv.app V ≫ (a.homEquiv V Z).symm f) =
      f ≫ (conjugateIsoEquiv a b c.symm).hom.app Z
    exact normalizedConjugateHom a b c V Z f
  let : PreservesFiniteLimits uTop.inverse := uTop.leftExact
  have level (n : ℕ) := InverseImageScalarRestriction.exists_comparison
    IA (IB n) (aY.app (op n)) (aX.app (op n)) (halgebra n)
  have restriction {n m : ℕ} (h : n ≤ m) :=
    InverseImageScalarRestriction.exists_comparison (IB m) (IB n)
      (BY.map (homOfLE h).op) (BX.map (homOfLE h).op) (htransition h)
  obtain ⟨d, _, _, hd, hk, hc, hs, ht⟩ := systemRestrictionMateCoherence
    AY AX BY BX aY aX uTop IA IB FB FA HB HA adjB adjA Hn adjn H0 adj0
    htransition halgebra (fun n ↦ (level n).choose) (fun n ↦ (level n).choose_spec)
    (fun h ↦ (restriction h).choose) (fun h ↦ (restriction h).choose_spec)
  have := hd
  have := hk
  have {n m : ℕ} (h : n ≤ m) := hc h
  let delta := asIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
    adjB adjA d.scalar)
  let kappa (n : ℕ) := asIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
    (adjn n) adj0 (d.level n))
  let chi {n m : ℕ} (h : n ≤ m) :=
    (asIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
      (adjn n) (adjn m) (d.restriction h))).symm
  refine ⟨d, delta, kappa, @chi, rfl, (fun _ ↦ rfl), (fun _ ↦ rfl),
    CategoryTheory.SystemEvaluationNormalization.unitNormalized adjB adjA d.scalar,
    (fun n ↦ CategoryTheory.SystemEvaluationNormalization.unitNormalized
      (adjn n) adj0 (d.level n)),
    (fun h ↦ CategoryTheory.SystemEvaluationNormalization.unitNormalized
      _ _ (d.restriction h)), ?_,
    (fun n ↦ CategoryTheory.SystemEvaluationNormalization.unitNormalized
      adjA adj0 (FA.evaluation n)), homComparison, ?_, ?_, ?_⟩
  · intro n
    exact systemSingletonEvaluationMate SY TY SX TX FA HA adjA
      (fun _ ↦ H0) (fun _ ↦ adj0) hFA n
  · intro n Z
    dsimp only [derivedSystemEvaluation] at hs ⊢
    simpa only [delta, kappa, asIso_hom,
      systemSingletonEvaluationMate SY TY SX TX FB HB adjB Hn adjn hFB,
      systemSingletonEvaluationMate SY TY SX TX FA HA adjA
        (fun _ ↦ H0) (fun _ ↦ adj0) hFA] using hs n Z
  · intro n Z
    rw [systemSingletonEvaluationMate SY TY SX TX FB HB adjB Hn adjn hFB]
    let : (IB n).modules.Additive := FB.levelAdditive n
    let : PreservesFiniteLimits (IB n).modules := FB.levelLimits n
    let : PreservesFiniteColimits (IB n).modules := FB.levelColimits n
    have h := mateEquiv_counit adjB.mapDerivedCategoryRightDerivedAdjunction
      (adjn n).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso (FB.evaluation n)).inv) Z
    apply (cancel_epi ((FB.derivedEvaluation n).inv.app
      (HB.rightDerivedFunctor.obj Z))).1
    change (Functor.mapDerivedCategorySquareIso (FB.evaluation n)).inv.app
        (HB.rightDerivedFunctor.obj Z) ≫
        (derivedSystemEvaluation BX n).map
          (adjB.mapDerivedCategoryRightDerivedAdjunction.counit.app Z) = _
    change (Functor.mapDerivedCategorySquareIso (FB.evaluation n)).inv.app
        (HB.rightDerivedFunctor.obj Z) ≫
        (systemEvaluation BX n).mapDerivedCategory.map
          (adjB.mapDerivedCategoryRightDerivedAdjunction.counit.app Z) = _
    simp only [Iso.inv_hom_id_app_assoc]
    convert h.symm using 1
    rfl
  · intro n m h Z
    rw [systemSingletonEvaluationMate SY TY SX TX FB HB adjB Hn adjn hFB,
      systemSingletonEvaluationMate SY TY SX TX FB HB adjB Hn adjn hFB]
    apply (cancel_mono ((chi h).inv.app ((derivedSystemEvaluation BX n).obj Z))).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    convert ht h Z using 1
    rfl

end SheafOfModules
