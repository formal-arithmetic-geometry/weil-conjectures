/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange

import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Sheaf.Algebra.Homology.PrincipalQuotientCompletionExists
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Identity scalar extension on the quotient Roos model

Source: Stacks Tags 03EK, 0941 and 0H9K; the identity specialization of the
quotient and two-coordinate comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory.PrincipalQuotientCompletion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

open MonoidalCategory

section TensorCalculations

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory roosF roosχ

private theorem tensorTotals
    (K L : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor _) (.up ℤ) := by
  infer_instance

-- Freeze the total-existence proof before elaborating the concrete tensor maps.
attribute [local instance 2000] tensorTotals

-- Every summand except the degree-zero single-complex term is zero.
private theorem single_ι_epi
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A] [MonoidalCategory A]
    [(curriedTensor A).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor A).obj M).PreservesZeroMorphisms]
    (N : A) (P : CochainComplex A ℤ)
    [HomologicalComplex.HasMapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj N) P (curriedTensor A) (.up ℤ)]
    (i : ℤ) :
    Epi (HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj N) P (curriedTensor A) (.up ℤ)
      0 i i (zero_add i)) := by
  constructor
  intro Z a b hab
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = i := by simpa using hpq
    subst q
    exact hab
  · apply IsZero.eq_of_src
    apply Functor.map_isZero ((curriedTensor A).flip.obj (P.X q))
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N p hp

private theorem single_quotient_epi
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A] [MonoidalCategory A]
    [(curriedTensor A).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor A).obj M).PreservesZeroMorphisms]
    {M N : A} (q : M ⟶ N) [Epi q] (P : CochainComplex A ℤ)
    [HomologicalComplex.HasMapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj M) P (curriedTensor A) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj N) P (curriedTensor A) (.up ℤ)]
    (i : ℤ) [(tensorRight (P.X i)).PreservesEpimorphisms] :
    Epi ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ▷ P.X i ≫
      HomologicalComplex.ιMapBifunctor
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) P (curriedTensor A) (.up ℤ)
        0 i i (zero_add i) ≫
      (HomologicalComplex.mapBifunctorMap ((HomologicalComplex.single A (.up ℤ) 0).map q)
        (𝟙 P) (curriedTensor A) (.up ℤ)).f i) := by
  have := single_ι_epi N P i
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, curriedTensor_obj_map, whiskerLeft_id]
  have hs : ((HomologicalComplex.single A (.up ℤ) 0).map q).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ q ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv :=
    HomologicalComplex.single_map_f_self (.up ℤ) 0 q
  rw [hs]
  simp only [curriedTensor_map_app, comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  have hq : Epi (q ▷ P.X i) :=
    inferInstanceAs (Epi ((tensorRight (P.X i)).map q))
  have hi : Epi ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ▷ P.X i) :=
    inferInstanceAs (Epi ((tensorRight (P.X i)).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv))
  have he := epi_comp
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ▷ P.X i)
    (HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single A (.up ℤ) 0).obj N) P (curriedTensor A) (.up ℤ)
      0 i i (zero_add i))
  simpa only [Category.id_comp] using (epi_comp (q ▷ P.X i)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ▷ P.X i ≫ _))

private theorem quotient_epi
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) (n : ℕ) :
    Epi (quotientMap R t P n) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  let := SheafOfModules.symmetricCategory R
  have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R (P.X i)
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft (P.X i)) :=
    preservesColimitsOfSize_shrink (tensorLeft (P.X i))
  have : PreservesColimitsOfSize.{0, 0} (tensorRight (P.X i)) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (P.X i))
  have h := single_quotient_epi
    (cokernel.π (endoPow (globalSectionMultiplication R t) (n + 1))) P i
  let q := (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))).inv ▷ P.X i ≫
    HomologicalComplex.ιMapBifunctor _ P (curriedTensor _) (.up ℤ) 0 i i (zero_add i) ≫
    (HomologicalComplex.mapBifunctorMap
      ((CochainComplex.singleFunctor _ 0).map
        (cokernel.π (endoPow (globalSectionMultiplication R t) (n + 1))))
      (𝟙 P) (curriedTensor _) (.up ℤ)).f i
  have : Epi q := h
  have hcomp : (quotientMap R t P n).f i =
      ((λ_ (P.X i)).inv ≫ eqToHom (congrArg (fun M ↦ M ⊗ P.X i)
        (tensorUnit_eq R))) ≫ q := by
    dsimp only [q]
    simp only [tensorUnit_eq]
    rfl
  rw [hcomp]
  have hi : Epi ((λ_ (P.X i)).inv) := inferInstance
  have he : Epi (eqToHom (congrArg (fun M ↦ M ⊗ P.X i) (tensorUnit_eq R))) :=
    inferInstance
  have hc := epi_comp ((λ_ (P.X i)).inv)
    (eqToHom (congrArg (fun M ↦ M ⊗ P.X i) (tensorUnit_eq R)))
  exact epi_comp _ q

end TensorCalculations

attribute [local irreducible] quotientTower quotientMap roosF roosχ
  SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem block_one_selection
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) : block 1 X = selection 1 X := by
  apply Pi.hom_ext
  intro n
  simp [block, selection]

private theorem roos_normalization_of_product
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (E : A ⥤ A) [E.Additive] (c : E ≅ 𝟭 A)
    (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (d : RepresentativeRoosComparison E X Y 1) (f : X ⟶ Y)
    (hprod : d.c =
      (NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ _).hom.app (roosP X) ≫
      roosPmap f ≫ selection 1 Y.asFunctor) :
    d.δ.hom =
      (NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ _).hom.app (roosF.obj X) ≫
      roosF.map f ≫ d.a := by
  let cc := NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ _
  let g := roosPmap f
  ext k : 1
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change p + 1 = k at hp
  subst k
  apply (cancel_mono (roosχ ((complexRestriction _ 1).obj Y) p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [d.cone_formula, d.arithmetic_formula]
  change scalarRoosCoordinates E X ((complexRestriction _ 1).obj Y) d.c p = _
  rw [reassoc_of% roosF_map_χ f p]
  rw [block_one_selection]
  apply biprod.hom_ext
  · simp only [scalarRoosCoordinates, Category.assoc, biprod.lift_fst]
    have hc := congrArg (fun h ↦ h.f p) hprod
    simp only [HomologicalComplex.comp_f] at hc
    rw [hc]
    erw [biprod.map_fst, biprod.map_fst_assoc]
    simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
    have hn := c.hom.naturality ((roosχ X p).hom ≫ biprod.fst)
    dsimp only [Functor.mapHomologicalComplex, Functor.id_obj]
    simp only [Category.comp_id]
    change E.map ((roosχ X p).hom ≫ biprod.fst) ≫
        c.hom.app ((roosP X).X p) ≫ g.f p ≫ (selection 1 Y.asFunctor).f p =
      c.hom.app ((roosF.obj X).X (p + 1)) ≫
        (roosχ X p).hom ≫ biprod.fst ≫ g.f p ≫ (selection 1 Y.asFunctor).f p
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun h ↦ h ≫ g.f p ≫ (selection 1 Y.asFunctor).f p) hn
  · simp only [scalarRoosCoordinates, Category.assoc, biprod.lift_snd]
    have hc := congrArg (fun h ↦ h.f (p + 1)) hprod
    simp only [HomologicalComplex.comp_f] at hc
    rw [hc]
    erw [biprod.map_snd, biprod.map_snd_assoc]
    simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
    have hn := c.hom.naturality ((roosχ X p).hom ≫ biprod.snd)
    dsimp only [Functor.mapHomologicalComplex, Functor.id_obj]
    simp only [Category.comp_id]
    change E.map ((roosχ X p).hom ≫ biprod.snd) ≫
        c.hom.app ((roosP X).X (p + 1)) ≫
          g.f (p + 1) ≫ (selection 1 Y.asFunctor).f (p + 1) =
      c.hom.app ((roosF.obj X).X (p + 1)) ≫ (roosχ X p).hom ≫ biprod.snd ≫
        g.f (p + 1) ≫ (selection 1 Y.asFunctor).f (p + 1)
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun h ↦ h ≫ g.f (p + 1) ≫ (selection 1 Y.asFunctor).f (p + 1)) hn


-- The quotient equation uniquely determines the finite-stage comparison.
private theorem quotient_identification
    {A : Type*} [Category A] (E : A ⥤ A) (c : E ≅ 𝟭 A)
    {P Q Q' : A} (q : P ⟶ Q) [Epi q] (q' : E.obj P ⟶ Q')
    (f : Q ⟶ Q') (b : E.obj Q ⟶ Q')
    (hb : E.map q ≫ b = q') (hn : c.inv.app P ≫ q' = q ≫ f) :
    b = c.hom.app Q ≫ f := by
  have : E.PreservesEpimorphisms := Functor.PreservesEpimorphisms.of_iso c.symm
  apply (cancel_epi (E.map q)).1
  rw [hb, ← Category.assoc, c.hom.naturality]
  simp only [Functor.id_map, Category.assoc]
  rw [← hn, ← Category.assoc, c.hom_inv_id_app, Category.id_comp]

private theorem family_transport
    {A : Type*} [Category A] {P : A} (Q : ℕ → A) (q : ∀ n, P ⟶ Q n)
    (n m : ℕ) (h : m = n) : q m ≫ eqToHom (congrArg Q h) = q n := by
  subst m
  simp

private theorem projection_map_transport
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (n m : ℕ) (h : m = n) :
    Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) m ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op m) ≫
      eqToHom (congrArg (fun k : ℕ ↦ Y.asFunctor.obj (op k)) h) =
    Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) := by
  subst m
  simp

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

/-- Finite-stage identity normalization for the prescribed quotient comparison.

Source: Stacks Tags 03EK and 0941; the quotient tensor calculation and cancellation
of the canonical quotient maps. This is the first independent part of the identity
Roos normalization argument.
(blueprint: lem-pur-identity-quotient-roos-normalization).
-/
private theorem identityQuotientFiniteStageNormalization
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w} (𝟙 R))
    (c : F.E ≅ 𝟭 _)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (d : RepresentativeRoosComparison F.E (sourceTower t P) (targetTower F t P) 1)
    (hq : ∀ n : ℕ, (extendedComplex F).map (quotientMap R t P n) ≫
      d.β.hom.app (op n) = quotientMap R t ((extendedComplex F).obj P) (1 * (n + 1) - 1)) :
    let cc : extendedComplex F ≅ 𝟭 _ := NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ _
    d.c = cc.hom.app (roosP (sourceTower t P)) ≫
      roosPmap ((quotientTower R t).map (cc.inv.app P)) ≫
      selection 1 (targetTower F t P).asFunctor := by
  classical
  let EC := extendedComplex F
  let cc : EC ≅ 𝟭 _ := NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ _
  let X := sourceTower t P
  let Y := targetTower F t P
  let f : X ⟶ Y := (quotientTower R t).map (cc.inv.app P)
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, selection]
  erw [Pi.lift_π]
  rw [d.product_formula]
  erw [roosPmap, Pi.map_π]
  have hn : 1 * (n + 1) - 1 = n := by omega
  have := quotient_epi t P n
  have hb : d.β.hom.app (op n) ≫
      eqToHom (congrArg (fun k : ℕ ↦ Y.asFunctor.obj (op k)) hn) =
      cc.hom.app (X.asFunctor.obj (op n)) ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) := by
    apply quotient_identification EC cc (quotientMap R t P n)
      (quotientMap R t (EC.obj P) n)
    · rw [← Category.assoc, hq n]
      exact family_transport (fun k ↦ Y.asFunctor.obj (op k))
        (quotientMap R t (EC.obj P)) n _ hn
    · exact quotient_natural R t (cc.inv.app P) n
  let e : Y.asFunctor.obj (op (1 * (n + 1) - 1)) ≅ Y.asFunctor.obj (op n) :=
    eqToIso (congrArg (fun k : ℕ ↦ Y.asFunctor.obj (op k)) hn)
  apply (cancel_mono e.hom).1
  simp only [Category.assoc]
  erw [hb, projection_map_transport f n (1 * (n + 1) - 1) hn]
  have H := cc.hom.naturality
    (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n)
  simpa only [Functor.id_map, Category.assoc] using
    congrArg (fun q ↦ q ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) H

set_option backward.defeqAttrib.useBackward true

/-- The specified identity-coefficient cochain comparison is scalar multiplication,
conjugated by the same multiplication on the quotient tower, followed by the
specified arithmetic map. No derived completion or resolution occurs in this assertion.

Source: Stacks Tags 03EK, 0941 and 0H9K; identity case of the quotient calculation
and the product/cone comparison
(blueprint: lem-pur-identity-quotient-roos-normalization).

Proof: the quotient map in every degree is the inverse unit constraint followed
by the quotient projection tensor the identity, and is an epimorphism because
sheaf tensor preserves cokernels. Cancel its image under scalar extension.
The quotient formula and naturality of the ordinary scalar identification then
identify each finite-stage map with the ordinary identification followed by the
inverse identification on the quotient tower. Project the product comparison to
each factor to obtain the same formula for products. For exponent one selection
is the identity and the weighted block sum consists of one identity transition.
Postcompose the proposed equality with each of the two signed Roos projections.
The cone formula reduces both equalities to the product formula and naturality
of the ordinary identification. Biproduct and product extensionality prove equality
of cochain maps. This includes zero rings and arbitrary unbounded complexes. -/
theorem identityQuotientRoosNormalization
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, w, w} (𝟙 R))
    (c : F.E ≅ 𝟭 _)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (d : RepresentativeRoosComparison F.E (sourceTower t P) (targetTower F t P) 1)
    (hq : ∀ n : ℕ, (extendedComplex F).map (quotientMap R t P n) ≫
      d.β.hom.app (op n) = quotientMap R t ((extendedComplex F).obj P) (1 * (n + 1) - 1)) :
    let cc : extendedComplex F ≅ 𝟭 _ := NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ _
    d.δ.hom = cc.hom.app ((quotientRoos R t).obj P) ≫
      (quotientRoos R t).map (cc.inv.app P) ≫ d.a := by
  change d.δ.hom =
    (NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ _).hom.app (roosF.obj (sourceTower t P)) ≫
    roosF.map ((quotientTower R t).map
      ((NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ _).inv.app P)) ≫ d.a
  have hprod := identityQuotientFiniteStageNormalization F c t P d hq
  exact roos_normalization_of_product F.E c (sourceTower t P) (targetTower F t P)
    d ((quotientTower R t).map
      ((NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ _).inv.app P)) hprod

end CategoryTheory.PrincipalQuotientCompletion
