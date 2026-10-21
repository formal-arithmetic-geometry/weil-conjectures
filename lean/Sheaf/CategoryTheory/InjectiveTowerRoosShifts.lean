/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11, SHEAF group G9
-/
module

public import Sheaf.CategoryTheory.TowerProductFunctor
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Sheaf.CategoryTheory.ProductCommShift
import Sheaf.Algebra.Homology.SignedMappingCoconeShift

/-!
# Injective tower Roos comparisons and signed integer shifts

Source: Stacks Project, sites-cohomology.tex, Tag 0941; derived.tex, Tags 014E,
070I, 08BJ and 0BK6; homology.tex, Tag 011G. Blueprint main-20261015,
sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md, coefficient comparisons.
(blueprint: lem-pur-injective-tower-roos-shifts)

The cone, its coordinates and its kernel inclusion are the existing `roosF`, `roosχ`
and `roosι`. Natural-number level n denotes positive level n+1. Products below are
products of complexes, with their actual projections; their localized fans are proved
limiting, so no exactness of products of arbitrary module sheaves is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe a b w uC vC r u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex


namespace CategoryTheory.InjectiveTowerRoos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

variable [HasLimitsOfShape ℕᵒᵖ A]

/-- The actual product of the ordinary limit-cone components.
Source: Stacks Tag 0941 (blueprint: lem-pur-injective-tower-roos-shifts). -/
noncomputable abbrev inclusion (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    limit I.asFunctor ⟶ roosP I :=
  Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))

/-- The insertion boundary in the inverse rotation of the fixed cone triangle.
Source: Stacks Tags 014E and 0941
(blueprint: lem-pur-injective-tower-roos-shifts).
In the coordinates `roosχ` this is b ↦ (b,0), with the canonical [-1][1] reindexing. -/
noncomputable abbrev boundary (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosP I ⟶ (roosF.obj I)⟦(1 : ℤ)⟧ :=
  (CochainComplex.mappingCone.triangle (roosU I)).invRotate.mor₃

variable [HasDerivedCategory.{w} A]

/-- Localize a specified termwise shift comparison and apply the localization's shift.
Source: Stacks Tags 011G and 0941
(blueprint: lem-pur-injective-tower-roos-shifts). -/
noncomputable def localizedShift
    (F : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
    (cs : F.CommShift ℤ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    DerivedCategory.Q.obj (F.obj (I⟦m⟧)) ⟶ (DerivedCategory.Q.obj (F.obj I))⟦m⟧ :=
  DerivedCategory.Q.map ((Functor.commShiftIso F (self := cs) m).hom.app I) ≫
    (DerivedCategory.Q.commShiftIso m).hom.app (F.obj I)

/-- The actual localized product of limit projections, in the termwise derived-product model.
Source: Stacks Tag 0941 (blueprint: lem-pur-injective-tower-roos-shifts). -/
noncomputable abbrev projection (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.obj (limit I.asFunctor) ⟶ DerivedCategory.Q.obj (roosP I) :=
  DerivedCategory.Q.map (inclusion I)

end CategoryTheory.InjectiveTowerRoos

namespace CategoryTheory

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

section LimitModel
variable [HasLimitsOfShape ℕᵒᵖ A]

omit [HasCountableProducts A] in
private lemma baseLimit_additive : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [lim_map]

attribute [local instance] baseLimit_additive

private noncomputable def limitModelCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private noncomputable def limitModelLimit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limitModelCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

private noncomputable def limitModelPointIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (limitModelLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)

omit [HasCountableProducts A] in
private lemma limitModelPointIso_hom_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) :
    (limitModelPointIso I).hom ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit I) (limit.isLimit I.asFunctor) n

private noncomputable def limitModelIso :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor :=
  NatIso.ofComponents limitModelPointIso (by
    intro X Y f
    dsimp only [roosLimitFunctor, Functor.comp_map,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    apply limit.hom_ext
    intro n
    dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    simp only [Category.assoc, limitModelPointIso_hom_π, lim_map, limMap_π]
    rw [← Category.assoc, limitModelPointIso_hom_π]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

@[instance_reducible]
private noncomputable def limitShift : (roosLimitFunctor (A := A)).CommShift ℤ :=
  Functor.CommShift.ofIso limitModelIso ℤ

omit [HasCountableProducts A] in
private lemma limitModel_hom_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) :
    limitModelIso.hom.app I ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I :=
  limitModelPointIso_hom_π I n

omit [HasCountableProducts A] in
private lemma limitShift_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m q : ℤ) (n : ℕ) :
    ((Functor.commShiftIso roosLimitFunctor (self := limitShift) m).hom.app I).f q ≫
      (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) m q (q + m) rfl).hom ≫
        (limit.π I.asFunctor (op n)).f (q + m) =
      (limit.π (I⟦m⟧).asFunctor (op n)).f q ≫
        ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n) := by
  simp only [roosLimitFunctor, Functor.comp_obj,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
  change (((Functor.CommShift.ofIso limitModelIso ℤ).commShiftIso m).hom.app I).f q ≫ _ = _
  rw [Functor.CommShift.ofIso_commShiftIso_hom_app]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    shiftFunctor_map_f', shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, NatTrans.id_app]
  have h := congrArg (fun f ↦ f.f (q + m)) (limitModel_hom_π I (op n))
  simp only [HomologicalComplex.comp_f] at h
  erw [Category.assoc, Category.id_comp, Category.comp_id, Category.id_comp, h]
  have h' := congrArg (fun f ↦ f.f q)
    ((limitModelIso.app (I⟦m⟧)).inv_hom_id_assoc
      (limit.π (I⟦m⟧).asFunctor (op n)))
  simp only [Iso.app_hom, Iso.app_inv, HomologicalComplex.comp_f] at h'
  rw [← h']
  congr 1
  exact (congrArg (fun f ↦ f.f q)
    (limitModel_hom_π (I⟦m⟧) (op n))).symm

end LimitModel

private lemma roosU_f_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :
    (roosU I).f q ≫ (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f q =
      (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f q -
        (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) (n + 1)).f q ≫
          (I.asFunctor.map (homOfLE (Nat.le_succ n)).op).f q := by
  have h := (towerTransitionEndomorphism_eq_iff
    (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) (roosU I)).mp rfl n
  exact congrArg (fun f ↦ f.f q) h


private noncomputable abbrev π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :=
  (Pi.π (fun n : ℕ ↦ N.asFunctor.obj (op n)) n).f q

private noncomputable abbrev v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :=
  (roosProj N).f q

private noncomputable abbrev ucoord (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) : (roosF.obj N).X q ⟶ (roosP N).X p :=
  (mappingCocone.snd (roosU N)).v q p (by omega)

-- The generic signed-shift construction follows the proved private helpers in
-- Sheaf.Algebra.Homology.RoosConeCalculus.
private noncomputable abbrev levelFunctor (n : ℕ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj N := N.asFunctor.obj (op n)
  map f := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)
  map_id N := by ext q; rfl
  map_comp f g := by ext q; rfl

@[instance_reducible]
private noncomputable def levelCommShift (n : ℕ) :
    (levelFunctor (A := A) n).CommShift ℤ := by
  change (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex
    (ComplexShape.up ℤ)).CommShift ℤ
  infer_instance

attribute [local instance] levelCommShift

omit [HasCountableProducts A] in
private theorem levelShift_f (n : ℕ) (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q : ℤ) :
    ((Functor.commShiftIso (levelFunctor (A := A) n)
      (self := levelCommShift n) r).hom.app N).f q =
      𝟙 ((N.X (q + r)).obj (op n)) := by
  rfl

private noncomputable abbrev productFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  ProductShift.productFunctor (levelFunctor (A := A))

@[instance_reducible]
private noncomputable def productShift : (productFunctor (A := A)).CommShift ℤ :=
  ProductShift.productCommShift (levelFunctor (A := A))

attribute [local instance] productShift

private noncomputable def productShiftComponent
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosP (N⟦r⟧)).X q ⟶ (roosP N).X (q + r) :=
  (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom.f q

private theorem productShiftComponent_eq
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    productShiftComponent N r q =
      (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom.f q := rfl

private theorem productShift_hom_f (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m q : ℤ) :
    ((Functor.commShiftIso productFunctor (self := productShift) m).hom.app I).f q =
      (ProductShift.productShiftIso (levelFunctor (A := A)) I m).hom.f q := rfl

private theorem productShift_π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q : ℤ) (n : ℕ) :
    productShiftComponent N r q ≫
        π N (q + r) n =
      π (N⟦r⟧) q n ≫
        ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n) := by
  have h := congrArg (fun k ↦ k.f q)
    (ProductShift.productShiftIso_π (levelFunctor (A := A)) N r n)
  simp only [HomologicalComplex.comp_f, levelShift_f] at h
  erw [Category.comp_id] at h
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  simpa only [productShiftComponent, π, shiftFunctor_map_f'] using h

attribute [local irreducible] productShiftComponent

private noncomputable def productShiftComponentAt
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q p : ℤ) (h : q + r = p) :
    (roosP (N⟦r⟧)).X q ⟶ (roosP N).X p :=
  productShiftComponent N r q ≫ ((roosP N).XIsoOfEq h).hom

attribute [local irreducible] productShiftComponentAt

private theorem productShiftComponentAt_eq
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m q p : ℤ) (h : q + m = p) :
    productShiftComponentAt I m q p h =
      ((Functor.commShiftIso productFunctor (self := productShift) m).hom.app I).f q ≫
        ((roosP I).shiftFunctorObjXIso m q p h.symm).hom := by
  unfold productShiftComponentAt
  rw [productShiftComponent_eq]
  rfl

private noncomputable def transitionEndomorphism : productFunctor (A := A) ⟶ productFunctor where
  app := roosU
  naturality _ _ f := (roosU_natural f).symm

private theorem transitionEndomorphism_shift :
    NatTrans.CommShift (transitionEndomorphism (A := A)) ℤ := by
  constructor
  intro r
  apply NatTrans.ext
  funext N
  change (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom ≫
      (roosU N)⟦r⟧' =
    roosU (N⟦r⟧) ≫ (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom
  apply ProductShift.productShift_hom_ext (levelFunctor (A := A)) N r
  intro n
  rw [Category.assoc, ← Functor.map_comp]
  have hu (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
      roosU M ≫ Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) n =
        Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) n -
          Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) (n + 1) ≫
            M.asFunctor.map (homOfLE (Nat.le_succ n)).op :=
    (towerTransitionEndomorphism_eq_iff
      (K := fun n : ℕ ↦ M.asFunctor.obj (op n))
      (fun n : ℕ ↦ M.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n
  erw [hu]
  rw [Category.assoc, ProductShift.productShiftIso_π]
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.comp_sub]
  erw [ProductShift.productShiftIso_π, ProductShift.productShiftIso_π_assoc]
  conv_rhs => erw [← Category.assoc, hu]
  simp only [Preadditive.sub_comp, Category.assoc]
  congr 1
  ext q
  simp [HomologicalComplex.comp_f, shiftFunctor_map_f', levelShift_f, levelFunctor]

attribute [local instance] transitionEndomorphism_shift

private noncomputable abbrev signedFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  SignedCoconeShift.coconeFunctor productFunctor productFunctor transitionEndomorphism

@[instance_reducible]
private noncomputable def signedCommShift : (signedFunctor (A := A)).CommShift ℤ :=
  SignedCoconeShift.coconeCommShift _ _ _

omit [HasCountableProducts A] in
private theorem cofiberMap_eq_coneMap
    {K L K' L' : CochainComplex A ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      mappingCone.map s s' a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X s (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    mappingCone.map, mappingCone.desc, mappingCone.descCochain,
    HomComplex.Cochain.comp_v, mappingCone.inl, mappingCone.fst, mappingCone.snd,
    mappingCone.inr]

private noncomputable def signedRoosIso : signedFunctor (A := A) ≅ roosF :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro N N' f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
      (cofiberMap_eq_coneMap (roosU N) (roosU N')
        (roosPmap f) (roosPmap f) (roosU_natural f)))

@[instance_reducible]
private noncomputable def roosCommShift : (roosF (A := A)).CommShift ℤ := by
  let := signedCommShift (A := A)
  exact Functor.CommShift.ofIso signedRoosIso ℤ

private noncomputable def roosShiftMap (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosF.obj (N⟦r⟧) ⟶ (roosF.obj N)⟦r⟧ :=
  (Functor.commShiftIso roosF (self := roosCommShift (A := A)) r).hom.app N

private theorem roosShiftMap_eq (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosShiftMap N r =
      (Functor.commShiftIso roosF (self := roosCommShift (A := A)) r).hom.app N := rfl

attribute [local irreducible] roosShiftMap

private theorem roosShift_hom (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosShiftMap N r =
      (SignedCoconeShift.coconeFunctorShiftIso productFunctor productFunctor
        transitionEndomorphism N r).hom := by
  rw [roosShiftMap_eq]
  let := signedCommShift (A := A)
  change ((Functor.CommShift.ofIso signedRoosIso ℤ).commShiftIso r).hom.app N = _
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app, signedRoosIso,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.refl_hom,
    Iso.refl_inv, Functor.map_id, Category.comp_id]
  erw [Category.id_comp]
  rfl

attribute [local irreducible] roosCommShift

@[reassoc]
private theorem roosShift_inl (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (mappingCocone.inl (roosU (N⟦r⟧))).v q q (add_zero q) ≫
        (roosShiftMap N r).f q =
      productShiftComponent N r q ≫
        (mappingCocone.inl (roosU N)).v (q + r) (q + r) (add_zero _) ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).inv := by
  rw [roosShift_hom, productShiftComponent_eq]
  exact SignedCoconeShift.coconeFunctorShiftIso_inl
    productFunctor productFunctor transitionEndomorphism N r q

@[reassoc]
private theorem roosShift_inr (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r p q : ℤ) (h : p + 1 = q) :
    (mappingCocone.inr (roosU (N⟦r⟧))).1.v p q h ≫
        (roosShiftMap N r).f q =
      r.negOnePow •
        (productShiftComponent N r p ≫
          (mappingCocone.inr (roosU N)).1.v (p + r) (q + r) (by omega) ≫
          (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).inv) := by
  rw [roosShift_hom, productShiftComponent_eq]
  exact SignedCoconeShift.coconeFunctorShiftIso_inr
    productFunctor productFunctor transitionEndomorphism N r p q h

private theorem v_eq_fst (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    v N q = (mappingCocone.fst (roosU N)).f q := rfl

@[reassoc]
private theorem roosShift_v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫ v N (q + r) =
      v (N⟦r⟧) q ≫
        productShiftComponent N r q := by
  simp only [v_eq_fst]
  apply SignedCoconeShift.cocone_ext_from (roosU (N⟦r⟧)) q
  · rw [roosShift_inl_assoc]
    simp only [
      Iso.inv_hom_id_assoc,
      mappingCocone.inl_v_fst_f, mappingCocone.inl_v_fst_f_assoc,
      Category.comp_id]
  · rw [roosShift_inr_assoc]
    simp only [Category.assoc, Linear.units_smul_comp,
      Iso.inv_hom_id_assoc,
      mappingCocone.inr_v_fst_f, mappingCocone.inr_v_fst_f_assoc,
      comp_zero, zero_comp, smul_zero]

@[reassoc]
private theorem roosShift_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) ((q - 1) + r) (by omega) =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫
        productShiftComponent N r (q - 1)) := by
  apply SignedCoconeShift.cocone_ext_from (roosU (N⟦r⟧)) q
  · rw [roosShift_inl_assoc]
    simp only [ucoord, Linear.comp_units_smul,
      Iso.inv_hom_id_assoc,
      mappingCocone.inl_v_snd_v, mappingCocone.inl_v_snd_v_assoc,
      comp_zero, zero_comp, smul_zero]
  · rw [roosShift_inr_assoc]
    simp only [ucoord, Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
      Iso.inv_hom_id_assoc,
      mappingCocone.inr_v_snd_v, mappingCocone.inr_v_snd_v_assoc,
      Category.comp_id]

private theorem roosShift_u_at (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q p : ℤ) (h : (q - 1) + r = p) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) p (by omega) =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫
        productShiftComponentAt N r (q - 1) p h) := by
  subst p
  simpa only [productShiftComponentAt, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id] using roosShift_u N r q

private theorem roosShift_v_at (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (m q t : ℤ) (h : q + m = t) :
    (roosShiftMap I m).f q ≫
        ((roosF.obj I).shiftFunctorObjXIso m q t h.symm).hom ≫ v I t =
      v (I⟦m⟧) q ≫ productShiftComponentAt I m q t h := by
  subst t
  simpa only [productShiftComponentAt, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id] using roosShift_v I m q

private theorem roosShift_u_at' (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (m q t p : ℤ) (ht : q + m = t) (hp : (q - 1) + m = p) :
    (roosShiftMap I m).f q ≫
        ((roosF.obj I).shiftFunctorObjXIso m q t ht.symm).hom ≫
          ucoord I t p (by omega) =
      m.negOnePow • (ucoord (I⟦m⟧) q (q - 1) rfl ≫
        productShiftComponentAt I m (q - 1) p hp) := by
  subst t
  exact roosShift_u_at I m q p hp

private theorem roosShift_u_at'' (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (m q t p₀ p : ℤ) (h₀ : q - 1 = p₀) (ht : q + m = t) (hp : p₀ + m = p) :
    (roosShiftMap I m).f q ≫
        ((roosF.obj I).shiftFunctorObjXIso m q t ht.symm).hom ≫
          ucoord I t p (by omega) =
      m.negOnePow • (ucoord (I⟦m⟧) q p₀ h₀ ≫
        productShiftComponentAt I m p₀ p hp) := by
  subst p₀
  exact roosShift_u_at' I m q t p ht hp

private noncomputable def productLimit (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    IsLimit (Fan.mk ((roosP N).X q) (π N q)) :=
  isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
    (fun n : ℕ ↦ N.asFunctor.obj (op n))

private theorem product_ext (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ)
    {T : A} {f g : T ⟶ (roosP N).X q}
    (h : ∀ n : ℕ, f ≫ π N q n = g ≫ π N q n) : f = g := by
  apply (productLimit N q).hom_ext
  rintro ⟨n⟩
  exact h n

private theorem roos_ext_at {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {T : A} (q p : ℤ) (hp : q - 1 = p) {f g : T ⟶ (roosF.obj N).X q}
    (hv : f ≫ v N q = g ≫ v N q)
    (hu : f ≫ ucoord N q p hp = g ≫ ucoord N q p hp) : f = g := by
  have hid := mappingCocone.id_X (roosU N) q p (by omega)
  change v N q ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
    ucoord N q p hp ≫
      (mappingCocone.inr (roosU N)).1.v p q (by omega) = 𝟙 _ at hid
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ ((v N q) ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
        ucoord N q p hp ≫
          (mappingCocone.inr (roosU N)).1.v p q (by omega)) := by rw [hid]
    _ = g ≫ ((v N q) ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
        ucoord N q p hp ≫
          (mappingCocone.inr (roosU N)).1.v p q (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hv, hu]
    _ = g := by rw [hid, Category.comp_id]

private lemma roos_boundary_f (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    (InjectiveTowerRoos.boundary I).f q =
      (mappingCocone.inr (roosU I)).1.v q (q + 1) rfl := by
  simp [InjectiveTowerRoos.boundary, Triangle.invRotate, mappingCone.triangle,
    mappingCocone.inr, HomComplex.Cocycle.rightShift_coe,
    HomComplex.Cocycle.ofHom_coe,
    HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero q),
    shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.hom, eqToIso.inv]

private lemma boundary_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    InjectiveTowerRoos.boundary (I⟦m⟧) ≫ (roosShiftMap I m)⟦(1 : ℤ)⟧' =
      m.negOnePow •
        (((Functor.commShiftIso productFunctor (self := productShift) m).hom.app I) ≫
          (InjectiveTowerRoos.boundary I)⟦m⟧' ≫
            (shiftFunctorComm (CochainComplex A ℤ) (1 : ℤ) m).hom.app (roosF.obj I)) := by
  ext q
  simp only [HomologicalComplex.comp_f, HomologicalComplex.units_smul_f_apply,
    shiftFunctor_map_f', roos_boundary_f, shiftFunctorComm_hom_app_f]
  have h := roosShift_inr I m q (q + 1) rfl
  simp only [productShiftComponent_eq, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv] at h
  rw [h]
  erw [Category.comp_id]
  rw [productShift_hom_f]
  congr 1
  congr 1
  simpa only [roosF, Functor.comp_obj, roosConeFunctor, mappingCocone,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp] using
    SignedCoconeShift.cast_cochain (mappingCocone.inr (roosU I)).1
      (rfl : q + m = q + m) (by omega : q + m + 1 = q + 1 + m) rfl (by omega)

-- These prefix, kernel, and recursive-section arguments also occur in
-- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients.
private theorem injective_tower_transition_split
    {A : Type*} [Category A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T]
    (n : ℕ) : IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  classical
  let k := (homOfLE (Nat.le_succ n)).op
  let M := T.obj (op n)
  let L := (evaluationLeftAdjoint A (op n)).obj M
  let L' := (evaluationLeftAdjoint A (op (n + 1))).obj M
  let i : L ⟶ L' :=
    { app := fun m ↦ Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ M) (k ≫ g)
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, L', evaluationLeftAdjoint, Category.assoc] }
  have (m : ℕᵒᵖ) : Mono (i.app m) := by
    let r : L'.obj m ⟶ L.obj m := Sigma.desc fun _ ↦
      if h : Nonempty (op n ⟶ m) then Sigma.ι (fun _ ↦ M) h.some else 0
    have hr : i.app m ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro g
      simp only [i, r, colimit.ι_desc_assoc, Cofan.mk_ι_app,
        dif_pos (show Nonempty (op n ⟶ m) from ⟨g⟩), colimit.ι_desc]
      exact (congrArg (Sigma.ι (fun _ : op n ⟶ m ↦ M))
        (Subsingleton.elim _ g)).trans (Category.comp_id _).symm
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono i := NatTrans.mono_of_mono_app i
  let a : L ⟶ T :=
    { app := fun m ↦ Sigma.desc fun g ↦ T.map g
      naturality := by
        intro x y f
        apply Sigma.hom_ext
        intro g
        simp [L, evaluationLeftAdjoint, Functor.map_comp] }
  let b := Injective.factorThru a i
  have hb : i ≫ b = a := Injective.comp_factorThru a i
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ M) (𝟙 (op (n + 1))) ≫
    b.app (op (n + 1)), ?_⟩
  rw [Category.assoc, ← b.naturality k, ← Category.assoc]
  have hn := congrArg (fun f : L ⟶ T ↦
    Sigma.ι (fun _ ↦ M) (𝟙 (op n)) ≫ f.app (op n)) hb
  simpa [L', evaluationLeftAdjoint, i, a] using hn


private theorem tower_compatibility
    {B : Type*} [Category* B] (F : ℕᵒᵖ ⥤ B) {Z : B}
    (a : ∀ n : ℕ, Z ⟶ F.obj (Opposite.op n))
    (ha : ∀ n, a (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = a n)
    {n m : ℕ} (h : n ≤ m) : a m ≫ F.map (homOfLE h).op = a n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have he : (homOfLE (Nat.le_trans h (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, F.map_comp, ← Category.assoc, ha, ih]

private theorem tower_kernel
    {B : Type*} [Category* B] [Preadditive B]
    (F : ℕᵒᵖ ⥤ B) (c : Cone F) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))) (hP : IsLimit P)
    (i : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hi : ∀ n : ℕ, i ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :
    ∃ h : i ≫ t = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := by
  have hz : i ≫ t = 0 := by
    apply hP.hom_ext
    intro ⟨n⟩
    change (i ≫ t) ≫ P.proj n = 0 ≫ P.proj n
    rw [Category.assoc, ht, Preadditive.comp_sub, hi, ← Category.assoc, hi]
    simp only [zero_comp, sub_eq_zero]
    exact (c.w (homOfLE (Nat.le_succ n)).op).symm
  refine ⟨hz, ⟨Fork.IsLimit.mk' _ ?_⟩⟩
  intro s
  let Z := s.pt
  let k := s.ι
  have hk : k ≫ t = 0 := by
    have h := s.condition
    simp only [comp_zero] at h
    exact h
  have ha (n : ℕ) : (k ≫ P.proj (n + 1)) ≫
      F.map (homOfLE (Nat.le_succ n)).op = k ≫ P.proj n := by
    have hn := congrArg (fun f ↦ f ≫ P.proj n) hk
    rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, zero_comp] at hn
    exact (sub_eq_zero.mp hn).symm
  let d : Cone F :=
    { pt := Z
      π := { app := fun n ↦ k ≫ P.proj n.unop
             naturality := by
               intro n m f
               change 𝟙 Z ≫ (k ≫ P.proj m.unop) =
                 (k ≫ P.proj n.unop) ≫ F.map f
               rw [Category.id_comp]
               symm
               exact tower_compatibility F (fun n ↦ k ≫ P.proj n) ha
                 (leOfHom f.unop) } }
  refine ⟨hc.lift d, ?_, ?_⟩
  · apply hP.hom_ext
    intro ⟨n⟩
    change (hc.lift d ≫ i) ≫ P.proj n = k ≫ P.proj n
    rw [Category.assoc, hi]
    exact hc.fac d (Opposite.op n)
  · intro l hl
    apply hc.hom_ext
    intro n
    change l ≫ i = k at hl
    calc
      l ≫ c.π.app n = k ≫ P.proj n.unop := by
        rw [← hi n.unop, ← Category.assoc, hl]
      _ = hc.lift d ≫ c.π.app n := (hc.fac d n).symm


private theorem fan_shift_splitEpi
    {A : Type u} [Category.{v} A] [Preadditive A]
    (K : ℕ → A) (P : Fan K) (hP : IsLimit P) (q : ∀ n, K (n + 1) ⟶ K n)
    [∀ n, IsSplitEpi (q n)] (t : P.pt ⟶ P.pt)
    (ht : ∀ n, t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫ q n) : IsSplitEpi t := by
  let a : ∀ n : ℕ, P.pt ⟶ K n := fun n ↦ Nat.rec 0
    (fun n a ↦ (a - P.proj n) ≫ section_ (q n)) n
  have ha (n : ℕ) : a (n + 1) ≫ q n = a n - P.proj n := by
    change ((a n - P.proj n) ≫ section_ (q n)) ≫ q n = _
    rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
  let r := hP.lift (Fan.mk P.pt a)
  have hr (n) : r ≫ P.proj n = a n := hP.fac _ ⟨n⟩
  refine IsSplitEpi.mk' ⟨r, ?_⟩
  apply Fan.IsLimit.hom_ext hP
  intro n
  rw [Category.assoc, ht, Preadditive.comp_sub, ← Category.assoc, hr, hr, ha]
  simp

variable [HasLimitsOfShape ℕᵒᵖ A]

private lemma roosι_fst (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    roosι I ≫ CochainComplex.mappingCocone.fst (roosU I) =
      InjectiveTowerRoos.inclusion I := by
  unfold roosι roosLift
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma injective_product [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    (roosP I).IsKInjective ∧
      Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone
        (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) := by
  let K : ℕ → CochainComplex A ℤ := fun n ↦ I.asFunctor.obj (op n)
  have (n : ℕ) : CochainComplex.IsKInjective (K n) := tower_evaluation_isKInjective A I (op n)
  obtain ⟨hk, ⟨hd⟩⟩ := CochainComplex.termwise_product_isKInjective_and_isLimit K
  let c := HomologicalComplex.coneOfHasLimitEval (Discrete.functor K)
  let hc := HomologicalComplex.isLimitConeOfHasLimitEval (Discrete.functor K)
  let e := hc.conePointUniqueUpToIso (limit.isLimit (Discrete.functor K))
  have : CochainComplex.IsKInjective c.pt := hk
  refine ⟨CochainComplex.isKInjective_of_iso e, ⟨?_⟩⟩
  exact hd.ofIsoLimit
    ((Cone.functoriality (Discrete.functor K) DerivedCategory.Q).mapIso
      (hc.uniqueUpToIso (limit.isLimit _)))

private lemma roos_kernel (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ h : InjectiveTowerRoos.inclusion I ≫ roosU I = 0,
      Nonempty (IsLimit (KernelFork.ofι (InjectiveTowerRoos.inclusion I) h)) := by
  exact tower_kernel I.asFunctor (limit.cone _) (limit.isLimit _)
    (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n))))
    (limit.isLimit _) (InjectiveTowerRoos.inclusion I) (roosU I)
    (fun n ↦ Pi.lift_π _ n)
    (fun n ↦ (towerTransitionEndomorphism_eq_iff _ _).mp rfl n)

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma roosU_degreewise_epi (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hI : ∀ q : ℤ, Injective (I.X q)) (q : ℤ) : Epi ((roosU I).f q) := by
  have (n : ℕ) : IsSplitEpi ((I.X q).map (homOfLE (Nat.le_succ n)).op) := by
    let _ := hI q
    exact injective_tower_transition_split (I.X q) n
  let K : ℕ → CochainComplex A ℤ := fun n ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  let ev := HomologicalComplex.eval A (.up ℤ) q
  have hP : IsLimit (Fan.mk ((roosP I).X q) (fun n ↦ (P.proj n).f q)) :=
    (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (limit.isLimit _))
  exact (fan_shift_splitEpi (fun n : ℕ ↦ (I.X q).obj (op n)) _ hP
    (fun n : ℕ ↦ (I.X q).map (homOfLE (Nat.le_succ n)).op)
    ((roosU I).f q) (roosU_f_π I q)).epi

omit [HasLimitsOfShape ℕᵒᵖ A] in
@[reassoc]
private lemma roosχ_fst (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosχ I p).hom ≫ biprod.fst =
      (CochainComplex.mappingCocone.snd (roosU I)).v (p + 1) p (by omega) := by
  have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
      HomologicalComplex.homotopyCofiber.sndX (roosU I) r =
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU I) r q hq).hom ≫
          biprod.snd := by
    obtain rfl := (ComplexShape.up ℤ).next_eq' hq
    dsimp only [HomologicalComplex.homotopyCofiber.sndX]
    rw [dif_pos hq]
  simp [roosχ, CochainComplex.mappingCocone.snd,
    CochainComplex.HomComplex.Cochain.leftShift_v,
    show Int.negOnePow 2 = 1 by rfl, CochainComplex.mappingCone.snd,
    hs p (p + 1) rfl]

omit [HasLimitsOfShape ℕᵒᵖ A] in
@[reassoc]
private lemma roosχ_snd (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosχ I p).hom ≫ biprod.snd =
      (CochainComplex.mappingCocone.fst (roosU I)).f (p + 1) :=
  (roosProj_f I p).symm

omit [HasLimitsOfShape ℕᵒᵖ A] in
private theorem shift_forward :
∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := roosCommShift) m).hom.app I).f (p + 1) ≫
            ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom =
          (roosχ (I⟦m⟧) p).hom ≫ biprod.map
            (m.negOnePow •
              (((Functor.commShiftIso productFunctor
                (self := productShift) m).hom.app I).f p ≫
                ((roosP I).shiftFunctorObjXIso m p (p + m) rfl).hom))
            (((Functor.commShiftIso productFunctor
                (self := productShift) m).hom.app I).f (p + 1) ≫
              ((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom) := by
  intro I m p
  have hu := roosShift_u_at'' I m (p + 1) ((p + m) + 1) p (p + m)
    (by omega) (by omega) rfl
  have hv := roosShift_v_at I m (p + 1) ((p + m) + 1) (by omega)
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, roosχ_fst, roosχ_fst_assoc,
      Linear.comp_units_smul]
    simpa only [ucoord, roosShiftMap_eq, productShiftComponentAt_eq] using hu
  · simp only [Category.assoc, biprod.map_snd, roosχ_snd, roosχ_snd_assoc]
    simpa only [v_eq_fst, roosShiftMap_eq, productShiftComponentAt_eq] using hv

omit [HasLimitsOfShape ℕᵒᵖ A] in
private theorem shift_inverse :
∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := roosCommShift) m).inv.app I).f (p + 1) ≫
            (roosχ (I⟦m⟧) p).hom =
          ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom ≫ biprod.map
              (m.negOnePow •
                (((roosP I).shiftFunctorObjXIso m p (p + m) rfl).inv ≫
                  ((Functor.commShiftIso productFunctor
                    (self := productShift) m).inv.app I).f p))
              (((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).inv ≫
                ((Functor.commShiftIso productFunctor
                  (self := productShift) m).inv.app I).f (p + 1)) := by
  intro I m p
  let ev := HomologicalComplex.eval A (.up ℤ)
  let eP : (roosP (I⟦m⟧)).X p ≅ (roosP I).X (p + m) := (ev p).mapIso
      ((Functor.commShiftIso productFunctor (self := productShift) m).app I) ≪≫
    (roosP I).shiftFunctorObjXIso m p (p + m) rfl
  let eQ : (roosP (I⟦m⟧)).X (p + 1) ≅ (roosP I).X ((p + m) + 1) :=
    (ev (p + 1)).mapIso
      ((Functor.commShiftIso productFunctor (self := productShift) m).app I) ≪≫
    (roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)
  let eC : (roosF.obj (I⟦m⟧)).X (p + 1) ≅ (roosF.obj I).X ((p + m) + 1) :=
    (ev (p + 1)).mapIso
      ((Functor.commShiftIso roosF (self := roosCommShift) m).app I) ≪≫
    (roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)
  let eD := biprod.mapIso (m.negOnePow • eP) eQ
  have h : eC.hom ≫ (roosχ I (p + m)).hom =
      (roosχ (I⟦m⟧) p).hom ≫ eD.hom := by
    simpa only [eC, eD, eP, eQ, ev, Iso.trans_hom, Functor.mapIso_hom,
      Preadditive.smul_iso_hom, biprod.mapIso_hom, HomologicalComplex.eval_map,
      Iso.app_hom, Category.assoc, HomologicalComplex.eval_obj, Functor.comp_obj] using
        shift_forward I m p
  have hi : eC.inv ≫ (roosχ (I⟦m⟧) p).hom =
      (roosχ I (p + m)).hom ≫ eD.inv := by
    apply (cancel_epi eC.hom).1
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi' := congrArg (fun f ↦
    ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫ f) hi
  simpa [eC, eD, eP, eQ, ev, productFunctor,
    Int.units_inv_eq_self, Category.assoc] using hi'

private lemma roosι_u (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q p : ℤ)
    (h : q - 1 = p) : (roosι I).f q ≫ ucoord I q p h = 0 := by
  simp [roosι, roosLift, ucoord]

private lemma inclusion_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    InjectiveTowerRoos.inclusion (I⟦m⟧) ≫
        (Functor.commShiftIso productFunctor (self := productShift) m).hom.app I =
      (Functor.commShiftIso roosLimitFunctor (self := limitShift) m).hom.app I ≫
        (InjectiveTowerRoos.inclusion I)⟦m⟧' := by
  ext q
  apply product_ext I (q + m)
  intro n
  simp only [HomologicalComplex.comp_f, shiftFunctor_map_f', Category.assoc]
  rw [productShift_hom_f, ← productShiftComponent_eq, productShift_π]
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :
      (InjectiveTowerRoos.inclusion I).f q ≫ π I q n =
        (limit.π I.asFunctor (op n)).f q :=
    congrArg (fun f ↦ f.f q) (Pi.lift_π (fun n : ℕ ↦ limit.π I.asFunctor (op n)) n)
  simp only [← Category.assoc, hi]
  have h := limitShift_π I m q n
  erw [Category.id_comp] at h
  exact h.symm

private lemma augmentation_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    roosι (I⟦m⟧) ≫ roosShiftMap I m =
      (Functor.commShiftIso roosLimitFunctor (self := limitShift) m).hom.app I ≫
        (roosι I)⟦m⟧' := by
  ext q
  apply roos_ext_at (q + m) ((q - 1) + m) (by omega)
  · have hv := roosShift_v I m q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hv
    erw [Category.id_comp] at hv
    simp only [HomologicalComplex.comp_f, Category.assoc, shiftFunctor_map_f']
    erw [hv]
    have hi := congrArg (fun f ↦ f.f q) (inclusion_shift I m)
    simp only [HomologicalComplex.comp_f, shiftFunctor_map_f'] at hi
    have hf (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : ℤ) :
        (roosι N).f j ≫ (mappingCocone.fst (roosU N)).f j =
          (InjectiveTowerRoos.inclusion N).f j :=
      congrArg (fun f ↦ f.f j) (roosι_fst N)
    simp only [v_eq_fst, ← Category.assoc, hf, productShiftComponent_eq]
    simpa only [productShift_hom_f] using hi
  · have hu := roosShift_u I m q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hu
    erw [Category.id_comp] at hu
    simp only [HomologicalComplex.comp_f, Category.assoc, shiftFunctor_map_f']
    erw [hu]
    simp only [Linear.comp_units_smul, ← Category.assoc, roosι_u,
      zero_comp, smul_zero, comp_zero]

private lemma injective_roos_quasiIso [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (hI : ∀ q : ℤ, Injective (I.X q)) :
    QuasiIso (roosι I) := by
  obtain ⟨h, ⟨hk⟩⟩ := roos_kernel I
  let e : limit I.asFunctor ≅ kernel (roosU I) :=
    hk.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (roosU I) = InjectiveTowerRoos.inclusion I :=
    hk.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  obtain ⟨κ, hκ, hq, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi
      (roosU I) (roosU_degreewise_epi I hI)
  have hκfst (q : ℤ) : κ.f q ≫ (mappingCocone.fst (roosU I)).f q =
      (kernel.ι (roosU I)).f q := by
    have h := (hκ q).2
    simp only [Int.sub_eq_add_neg] at h
    simpa [mappingCocone.fst, HomComplex.Cocycle.homOf,
      HomComplex.Cocycle.leftShift, HomComplex.Cochain.leftShift,
      mappingCone.fst, Int.sub_eq_add_neg] using h
  have hκsnd (q : ℤ) : κ.f q ≫ ucoord I q (q - 1) rfl = 0 := by
    have h := (hκ q).1
    simp only [Int.sub_eq_add_neg] at h
    simpa [ucoord, mappingCocone.snd, HomComplex.Cochain.leftShift,
      show Int.negOnePow 2 = 1 by rfl, mappingCone.snd, Int.sub_eq_add_neg] using h
  have hcomp : e.hom ≫ κ = roosι I := by
    ext q
    apply roos_ext_at q (q - 1) rfl
    · simp only [HomologicalComplex.comp_f, Category.assoc, v_eq_fst]
      rw [hκfst, ← HomologicalComplex.comp_f, he]
      exact (congrArg (fun f ↦ f.f q) (roosι_fst I)).symm
    · simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [hκsnd, comp_zero, roosι_u]
  rw [← hcomp]
  let _ := hq
  infer_instance

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma roos_cone_distinguished [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Triangle.mk (DerivedCategory.Q.map (roosProj I))
      (DerivedCategory.Q.map (roosU I))
      (DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I)) ∈
          distTriang (DerivedCategory.{w} A) := by
  exact DerivedCategory.mappingCocone_triangle_distinguished (roosU I)

private noncomputable def normalizedBoundary [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    DerivedCategory.Q.{w}.obj (roosP I) ⟶
      (DerivedCategory.Q.{w}.obj (limit I.asFunctor))⟦(1 : ℤ)⟧ := by
  classical
  exact if h : IsIso (DerivedCategory.Q.{w}.map (roosι I)) then
    DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ≫
        (inv (DerivedCategory.Q.map (roosι I)))⟦(1 : ℤ)⟧' else 0

private lemma normalizedBoundary_eq [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [QuasiIso (roosι I)] :
    normalizedBoundary I ≫ (DerivedCategory.Q.map (roosι I))⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) := by
  have hi : IsIso (DerivedCategory.Q.{w}.map (roosι I)) := inferInstance
  simp [normalizedBoundary, hi, Category.assoc]

private lemma normalizedBoundary_distinguished [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [QuasiIso (roosι I)] :
    Triangle.mk (InjectiveTowerRoos.projection I) (DerivedCategory.Q.map (roosU I))
      (normalizedBoundary I) ∈ distTriang (DerivedCategory.{w} A) := by
  have hi : IsIso (DerivedCategory.Q.map (roosι I)) := inferInstance
  let e := asIso (DerivedCategory.Q.map (roosι I))
  let T := Triangle.mk (InjectiveTowerRoos.projection I)
    (DerivedCategory.Q.map (roosU I)) (normalizedBoundary I)
  let U := Triangle.mk (DerivedCategory.Q.map (roosProj I))
    (DerivedCategory.Q.map (roosU I))
    (DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I))
  let h : T ≅ U := Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    (by
      change InjectiveTowerRoos.projection I ≫ 𝟙 _ =
        DerivedCategory.Q.map (roosι I) ≫ DerivedCategory.Q.map (roosProj I)
      rw [Category.comp_id, ← Functor.map_comp]
      exact congrArg DerivedCategory.Q.map (roosι_fst I).symm)
    (by simp [T, U])
    (by simpa [T, U, e] using normalizedBoundary_eq I)
  exact isomorphic_distinguished _ (roos_cone_distinguished I) _ h

private lemma localized_inclusion_shift [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    InjectiveTowerRoos.projection (I⟦m⟧) ≫
        InjectiveTowerRoos.localizedShift productFunctor productShift I m =
      InjectiveTowerRoos.localizedShift roosLimitFunctor limitShift I m ≫
        (InjectiveTowerRoos.projection I)⟦m⟧' := by
  simp only [InjectiveTowerRoos.localizedShift, InjectiveTowerRoos.projection,
    Category.assoc]
  rw [← Functor.map_comp_assoc, inclusion_shift, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

private lemma localized_augmentation_shift [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    DerivedCategory.Q.{w}.map (roosι (I⟦m⟧)) ≫
        InjectiveTowerRoos.localizedShift roosF roosCommShift I m =
      InjectiveTowerRoos.localizedShift roosLimitFunctor limitShift I m ≫
        (DerivedCategory.Q.map (roosι I))⟦m⟧' := by
  simp only [InjectiveTowerRoos.localizedShift, Category.assoc]
  rw [← Functor.map_comp_assoc, ← roosShiftMap_eq, augmentation_shift,
    Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]

omit [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A] in
private lemma localized_commuting_shifts [HasDerivedCategory.{w} A]
    (K : CochainComplex A ℤ) (m : ℤ) :
    DerivedCategory.Q.map
        ((shiftFunctorComm (CochainComplex A ℤ) (1 : ℤ) m).hom.app K) ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (K⟦m⟧) ≫
        ((DerivedCategory.Q.commShiftIso m).hom.app K)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Q.commShiftIso m).hom.app (K⟦(1 : ℤ)⟧) ≫
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦m⟧' ≫
          (shiftFunctorComm (DerivedCategory.{w} A) (1 : ℤ) m).hom.app
            (DerivedCategory.Q.obj K) := by
  rw [Functor.map_shiftFunctorComm_hom_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [Functor.map_id, Category.comp_id]

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma localized_boundary_shift [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    (DerivedCategory.Q.map (InjectiveTowerRoos.boundary (I⟦m⟧)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj (I⟦m⟧))) ≫
        (InjectiveTowerRoos.localizedShift roosF roosCommShift I m)⟦(1 : ℤ)⟧' =
      m.negOnePow •
        (InjectiveTowerRoos.localizedShift productFunctor productShift I m ≫
          (DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
            (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I))⟦m⟧' ≫
              (shiftFunctorComm (DerivedCategory.{w} A) (1 : ℤ) m).hom.app
                (DerivedCategory.Q.obj (roosF.obj I))) := by
  simp only [InjectiveTowerRoos.localizedShift, Functor.map_comp, Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc]
  have h := congrArg DerivedCategory.Q.{w}.map (boundary_shift I m)
  simp only [roosShiftMap_eq] at h
  rw [h]
  simp only [Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp,
    Category.assoc]
  congr 1
  simp only [Functor.comp_obj]
  rw [localized_commuting_shifts]
  rw [Functor.commShiftIso_hom_naturality_assoc]

private lemma normalizedBoundary_shift [HasDerivedCategory.{w} A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ)
    [QuasiIso (roosι I)] [QuasiIso (roosι (I⟦m⟧))] :
    normalizedBoundary (I⟦m⟧) ≫
        (InjectiveTowerRoos.localizedShift roosLimitFunctor limitShift I m)⟦(1 : ℤ)⟧' =
      m.negOnePow •
        (InjectiveTowerRoos.localizedShift productFunctor productShift I m ≫
          (normalizedBoundary I)⟦m⟧' ≫
            (shiftFunctorComm (DerivedCategory.{w} A) (1 : ℤ) m).hom.app
              (DerivedCategory.Q.obj (limit I.asFunctor))) := by
  have haug := congrArg ((shiftFunctor (DerivedCategory.{w} A) (1 : ℤ)).map)
    (localized_augmentation_shift I m)
  simp only [Functor.map_comp] at haug
  have hcomm := (shiftFunctorComm (DerivedCategory.{w} A) (1 : ℤ) m).hom.naturality
    (DerivedCategory.Q.map (roosι I))
  change ((DerivedCategory.Q.map (roosι I))⟦(1 : ℤ)⟧')⟦m⟧' ≫ _ =
    _ ≫ ((DerivedCategory.Q.map (roosι I))⟦m⟧')⟦(1 : ℤ)⟧' at hcomm
  apply (cancel_mono (((DerivedCategory.Q.{w}.map (roosι I))⟦m⟧')⟦(1 : ℤ)⟧')).1
  rw [Category.assoc, ← haug, ← Category.assoc, normalizedBoundary_eq]
  rw [localized_boundary_shift]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [← hcomm, ← Functor.map_comp_assoc, normalizedBoundary_eq]

omit [HasLimitsOfShape ℕᵒᵖ A] in
private lemma boundary_natural {I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : I ⟶ I') :
    roosPmap f ≫ InjectiveTowerRoos.boundary I' =
      InjectiveTowerRoos.boundary I ≫ (roosF.map f)⟦(1 : ℤ)⟧' := by
  exact (((Pretriangulated.invRotate _).map
    (CochainComplex.mappingCone.triangleMap _ _ (roosPmap f) (roosPmap f)
      (roosU_natural f))).comm₃).symm

private lemma normalizedBoundary_natural [HasDerivedCategory.{w} A]
    {I I' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    [QuasiIso (roosι I)] [QuasiIso (roosι I')] (f : I ⟶ I') :
    DerivedCategory.Q.map (roosPmap f) ≫ normalizedBoundary I' =
      normalizedBoundary I ≫ (DerivedCategory.Q.map (roosLimitFunctor.map f))⟦(1 : ℤ)⟧' := by
  have he : DerivedCategory.Q.{w}.map (roosLimitFunctor.map f) ≫
      DerivedCategory.Q.map (roosι I') =
        DerivedCategory.Q.map (roosι I) ≫ DerivedCategory.Q.map (roosF.map f) := by
    simpa only [← Functor.map_comp, roosLimitFunctor, Functor.comp_map] using
      congrArg DerivedCategory.Q.{w}.map (roosι_natural f)
  apply (cancel_mono ((DerivedCategory.Q.{w}.map (roosι I'))⟦(1 : ℤ)⟧')).1
  rw [Category.assoc, normalizedBoundary_eq]
  conv_rhs =>
    rw [Category.assoc, ← Functor.map_comp, he, Functor.map_comp,
      ← Category.assoc, normalizedBoundary_eq]
  rw [← Functor.map_comp_assoc, boundary_natural, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]
  simp only [Category.assoc]

private lemma derived_representative [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} (C := A) ⟶
      DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ A) ⋙ RF)
    (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : X ⟶ I)
    [QuasiIso q] [I.IsKInjective] [QuasiIso (roosι I)] :
    ∃ d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅ RF.obj (DerivedCategory.Q.{w}.obj X),
      d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I ∧
      Triangle.mk (d.inv ≫ InjectiveTowerRoos.projection I)
        (DerivedCategory.Q.{w}.map (roosU I)) (normalizedBoundary I ≫ d.hom⟦(1 : ℤ)⟧') ∈
          distTriang (DerivedCategory.{w} A) := by
  have := hη I inferInstance
  let d := asIso (η.app I) ≪≫ (RF.mapIso (asIso (DerivedCategory.Q.{w}.map q))).symm
  refine ⟨d, ?_, ?_⟩
  · simp [d]
  · let T := Triangle.mk (InjectiveTowerRoos.projection I)
      (DerivedCategory.Q.{w}.map (roosU I)) (normalizedBoundary I)
    let U := Triangle.mk (d.inv ≫ InjectiveTowerRoos.projection I)
      (DerivedCategory.Q.{w}.map (roosU I)) (normalizedBoundary I ≫ d.hom⟦(1 : ℤ)⟧')
    let e : T ≅ U := Triangle.isoMk _ _ d (Iso.refl _) (Iso.refl _)
      (by simp [T, U]) (by simp [T, U]) (by simp [T, U])
    exact isomorphic_distinguished _ (normalizedBoundary_distinguished I) _ e.symm

/-- The injective-tower comparison uses the actual kernel inclusion and the normalized
signed shifts, including the boundary sign, without exactness of arbitrary products.

Source: Stacks Project, sites-cohomology.tex, Tag 0941; derived.tex, Tags 070I,
08BJ, 0BK6 and 014E; homology.tex, Tag 011G; blueprint main-20261015,
sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md, coefficient comparisons.
(blueprint: lem-pur-injective-tower-roos-shifts)

Proof plan:
1. For an injective tower J, the prefix tower E_n(J_n) embeds monomorphically in
E_{n+1}(J_n). Extend the map to J corresponding to id at level n. Its level n+1
component splits the transition (def-sp-injective-resolutions and levelwise abelianness).
2. Evaluate the K-injective tower using lem-weil-tower-evaluation-kinjective. Apply
lem-pc-ringed-space-product-kinjective to its evaluated complexes: their termwise product
is K-injective and its localized projections form a product fan.
3. Write h=1-s. Its kernel is the actual termwise limit, with inclusion j. Choose
transition splittings u_n in each degree. The recursion a_0=0,
a_{n+1}=u_n(a_n-pr_n) gives h a=id. Thus h is degreewise split epi.
4. Apply lem-weil-degreewise-epi-kernel-cocone-qis. Its kernel comparison is precisely
roosι=(0,j), and is a quasi-isomorphism with all actual limit-cone components.
5. Inverse-rotate the cone triangle with third arrow -pr_x. The first arrow is pr_x,
and the boundary is insertion in y. Localize and transport by Q(roosι). This gives the
displayed distinguished Roos triangle with first arrow Qj and middle arrow Q(1-s).
The total-derived-limit computation in lem-weil-pbc-ringed-strict-tower-homotopy-limit
identifies its first object with L(N); the final normalization equation retains q:X→I.
6. Apply the endomorphism-fibre coordinate calculus to h and reorder (v,u) as (y,x).
The shift comparison is ((-1)^r y,x), its inverse has the same signs, and augmentation
commutes with it. Zero and addition coherence are the CommShift laws. Shifts preserve
K-injectivity by shifting acyclic sources back, and preserve injective terms by reindexing.
7. Projection to x commutes with shift. Insertion in y acquires (-1)^r. Conjugate the
second identity by Q(roosι)[1] to obtain exactly the signed boundary identity below,
using shiftFunctorComm for [1][r]=[r][1].
8. For maps of chosen resolutions, universal properties give naturality of j and of
the cone maps. The unique normalized transported boundary is therefore natural too.
K-injective Hom_K=Hom_D (lem-weil-pbc-kinjective-hom-derived) and the compatible tower
homotopy functor (lem-pur-strict-roos-homotopy-functor) descend these identities through
localization and make them independent of a resolution comparison up to homotopy.
The formulas apply to all integer r, zero complexes, and the zero coefficient ring. -/
theorem injectiveTowerRoosShifts
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] (R : Sheaf J RingCat.{r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{r, r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R)] :
    ∃ (csP : (InjectiveTowerRoos.productFunctor
        (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (csL : (roosLimitFunctor (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (csC : (roosF (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (δ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ,
        DerivedCategory.Q.{w}.obj (roosP I) ⟶
          (DerivedCategory.Q.{w}.obj (limit I.asFunctor))⟦(1 : ℤ)⟧),
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        (m q : ℤ) (n : ℕ),
        ((Functor.commShiftIso InjectiveTowerRoos.productFunctor (self := csP) m).hom.app I).f q ≫
            ((roosP I).shiftFunctorObjXIso m q (q + m) rfl).hom ≫
            (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f (q + m) =
          (Pi.π (fun k : ℕ ↦ (I⟦m⟧).asFunctor.obj (op k)) n).f q ≫
            ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        (m q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := csL) m).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) m q (q + m) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + m) =
          (limit.π (I⟦m⟧).asFunctor (op n)).f q ≫
            ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := csC) m).hom.app I).f (p + 1) ≫
            ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom =
          (roosχ (I⟦m⟧) p).hom ≫ biprod.map
            (m.negOnePow •
              (((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                (self := csP) m).hom.app I).f p ≫
                ((roosP I).shiftFunctorObjXIso m p (p + m) rfl).hom))
            (((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                (self := csP) m).hom.app I).f (p + 1) ≫
              ((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := csC) m).inv.app I).f (p + 1) ≫
            (roosχ (I⟦m⟧) p).hom =
          ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom ≫ biprod.map
              (m.negOnePow •
                (((roosP I).shiftFunctorObjXIso m p (p + m) rfl).inv ≫
                  ((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                    (self := csP) m).inv.app I).f p))
              (((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).inv ≫
                ((Functor.commShiftIso InjectiveTowerRoos.productFunctor
                  (self := csP) m).inv.app I).f (p + 1))) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m : ℤ),
        roosι (I⟦m⟧) ≫ (Functor.commShiftIso roosF (self := csC) m).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := csL) m).hom.app I ≫ (roosι I)⟦m⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        [I.IsKInjective] (_hIinj : ∀ i : ℤ, Injective (I.X i)),
        (∀ (i : ℤ) (n : ℕ), IsSplitEpi ((I.X i).map (homOfLE (Nat.le_succ n)).op)) ∧
        (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n))) ∧
        (roosP I).IsKInjective ∧
        Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone
          (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
        QuasiIso (roosι I) ∧
        ∃ ε : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.{w}.obj (roosF.obj I),
          ε.hom = DerivedCategory.Q.map (roosι I) ∧
          Triangle.mk (InjectiveTowerRoos.projection I) (DerivedCategory.Q.map (roosU I))
            (δ I) ∈ distTriang (DerivedCategory.{w} (ringedSiteModules.{r, r} R)) ∧
          δ I ≫ ε.hom⟦(1 : ℤ)⟧' =
            DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
              (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ∧
          (∀ m : ℤ,
            InjectiveTowerRoos.projection (I⟦m⟧) ≫
                InjectiveTowerRoos.localizedShift InjectiveTowerRoos.productFunctor csP I m =
              InjectiveTowerRoos.localizedShift roosLimitFunctor csL I m ≫
                (InjectiveTowerRoos.projection I)⟦m⟧' ∧
            δ (I⟦m⟧) ≫
                (InjectiveTowerRoos.localizedShift roosLimitFunctor csL I m)⟦(1 : ℤ)⟧' =
              m.negOnePow •
                (InjectiveTowerRoos.localizedShift InjectiveTowerRoos.productFunctor csP I m ≫
                  (δ I)⟦m⟧' ≫
                  (shiftFunctorComm (DerivedCategory.{w} (ringedSiteModules.{r, r} R))
                    (1 : ℤ) m).hom.app (DerivedCategory.Q.obj (limit I.asFunctor))))) ∧
      (∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        [I.IsKInjective] [I'.IsKInjective]
        (_hIinj : ∀ i : ℤ, Injective (I.X i)) (_hI'inj : ∀ i : ℤ, Injective (I'.X i))
        (f : I ⟶ I'),
        DerivedCategory.Q.map (roosPmap f) ≫ δ I' =
          δ I ≫ (DerivedCategory.Q.map (roosLimitFunctor.map f))⟦(1 : ℤ)⟧') ∧
      (∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ⥤
            DerivedCategory.{w} (ringedSiteModules.{r, r} R))
        (η : roosLimitFunctor ⋙
          DerivedCategory.Q.{w} (C := ringedSiteModules.{r, r} R) ⟶
          DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ⋙ RF)
        (_hRF : RF.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) (ComplexShape.up ℤ)))
        (_hη : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ,
          I.IsKInjective → IsIso (η.app I))
        (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (q : X ⟶ I)
        [QuasiIso q] [I.IsKInjective] (_hIinj : ∀ i : ℤ, Injective (I.X i)),
        ∃ d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅ RF.obj (DerivedCategory.Q.obj X),
          d.hom ≫ RF.map (DerivedCategory.Q.map q) = η.app I ∧
          Triangle.mk (d.inv ≫ InjectiveTowerRoos.projection I)
            (DerivedCategory.Q.map (roosU I)) (δ I ≫ d.hom⟦(1 : ℤ)⟧') ∈
              distTriang (DerivedCategory.{w} (ringedSiteModules.{r, r} R))) := by
  change ∃ (csP : (productFunctor
        (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (csL : (roosLimitFunctor (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (csC : (roosF (A := ringedSiteModules.{r, r} R)).CommShift ℤ)
      (δ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ,
        DerivedCategory.Q.{w}.obj (roosP I) ⟶
          (DerivedCategory.Q.{w}.obj (limit I.asFunctor))⟦(1 : ℤ)⟧),
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        (m q : ℤ) (n : ℕ),
        ((Functor.commShiftIso productFunctor (self := csP) m).hom.app I).f q ≫
            ((roosP I).shiftFunctorObjXIso m q (q + m) rfl).hom ≫
            (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f (q + m) =
          (Pi.π (fun k : ℕ ↦ (I⟦m⟧).asFunctor.obj (op k)) n).f q ≫
            ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        (m q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := csL) m).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) m q (q + m) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + m) =
          (limit.π (I⟦m⟧).asFunctor (op n)).f q ≫
            ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := csC) m).hom.app I).f (p + 1) ≫
            ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom =
          (roosχ (I⟦m⟧) p).hom ≫ biprod.map
            (m.negOnePow •
              (((Functor.commShiftIso productFunctor
                (self := csP) m).hom.app I).f p ≫
                ((roosP I).shiftFunctorObjXIso m p (p + m) rfl).hom))
            (((Functor.commShiftIso productFunctor
                (self := csP) m).hom.app I).f (p + 1) ≫
              ((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m p : ℤ),
        ((Functor.commShiftIso roosF (self := csC) m).inv.app I).f (p + 1) ≫
            (roosχ (I⟦m⟧) p).hom =
          ((roosF.obj I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).hom ≫
            (roosχ I (p + m)).hom ≫ biprod.map
              (m.negOnePow •
                (((roosP I).shiftFunctorObjXIso m p (p + m) rfl).inv ≫
                  ((Functor.commShiftIso productFunctor
                    (self := csP) m).inv.app I).f p))
              (((roosP I).shiftFunctorObjXIso m (p + 1) ((p + m) + 1) (by omega)).inv ≫
                ((Functor.commShiftIso productFunctor
                  (self := csP) m).inv.app I).f (p + 1))) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (m : ℤ),
        roosι (I⟦m⟧) ≫ (Functor.commShiftIso roosF (self := csC) m).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := csL) m).hom.app I ≫ (roosι I)⟦m⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        [I.IsKInjective] (_hIinj : ∀ i : ℤ, Injective (I.X i)),
        (∀ (i : ℤ) (n : ℕ), IsSplitEpi ((I.X i).map (homOfLE (Nat.le_succ n)).op)) ∧
        (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n))) ∧
        (roosP I).IsKInjective ∧
        Nonempty (IsLimit (DerivedCategory.Q.{w}.mapCone
          (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
        QuasiIso (roosι I) ∧
        ∃ ε : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.{w}.obj (roosF.obj I),
          ε.hom = DerivedCategory.Q.map (roosι I) ∧
          Triangle.mk (InjectiveTowerRoos.projection I) (DerivedCategory.Q.map (roosU I))
            (δ I) ∈ distTriang (DerivedCategory.{w} (ringedSiteModules.{r, r} R)) ∧
          δ I ≫ ε.hom⟦(1 : ℤ)⟧' =
            DerivedCategory.Q.map (InjectiveTowerRoos.boundary I) ≫
              (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (roosF.obj I) ∧
          (∀ m : ℤ,
            InjectiveTowerRoos.projection (I⟦m⟧) ≫
                InjectiveTowerRoos.localizedShift productFunctor csP I m =
              InjectiveTowerRoos.localizedShift roosLimitFunctor csL I m ≫
                (InjectiveTowerRoos.projection I)⟦m⟧' ∧
            δ (I⟦m⟧) ≫
                (InjectiveTowerRoos.localizedShift roosLimitFunctor csL I m)⟦(1 : ℤ)⟧' =
              m.negOnePow •
                (InjectiveTowerRoos.localizedShift productFunctor csP I m ≫
                  (δ I)⟦m⟧' ≫
                  (shiftFunctorComm (DerivedCategory.{w} (ringedSiteModules.{r, r} R))
                    (1 : ℤ) m).hom.app (DerivedCategory.Q.obj (limit I.asFunctor))))) ∧
      (∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ)
        [I.IsKInjective] [I'.IsKInjective]
        (_hIinj : ∀ i : ℤ, Injective (I.X i)) (_hI'inj : ∀ i : ℤ, Injective (I'.X i))
        (f : I ⟶ I'),
        DerivedCategory.Q.map (roosPmap f) ≫ δ I' =
          δ I ≫ (DerivedCategory.Q.map (roosLimitFunctor.map f))⟦(1 : ℤ)⟧') ∧
      (∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ⥤
            DerivedCategory.{w} (ringedSiteModules.{r, r} R))
        (η : roosLimitFunctor ⋙
          DerivedCategory.Q.{w} (C := ringedSiteModules.{r, r} R) ⟶
          DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ⋙ RF)
        (_hRF : RF.IsRightDerivedFunctor η
          (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) (ComplexShape.up ℤ)))
        (_hη : ∀ I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ,
          I.IsKInjective → IsIso (η.app I))
        (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r, r} R) ℤ) (q : X ⟶ I)
        [QuasiIso q] [I.IsKInjective] (_hIinj : ∀ i : ℤ, Injective (I.X i)),
        ∃ d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅ RF.obj (DerivedCategory.Q.obj X),
          d.hom ≫ RF.map (DerivedCategory.Q.map q) = η.app I ∧
          Triangle.mk (d.inv ≫ InjectiveTowerRoos.projection I)
            (DerivedCategory.Q.map (roosU I)) (δ I ≫ d.hom⟦(1 : ℤ)⟧') ∈
              distTriang (DerivedCategory.{w} (ringedSiteModules.{r, r} R)))
  classical
  refine ⟨productShift, limitShift, roosCommShift, normalizedBoundary, ?_, ?_,
    shift_forward, shift_inverse, ?_, ?_, ?_, ?_⟩
  · intro I m q n
    simp only [productShift_hom_f, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    erw [Category.id_comp]
    simpa only [productShiftComponent_eq, π, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom] using productShift_π I m q n
  · exact limitShift_π
  · intro I m
    simpa only [roosShiftMap_eq] using augmentation_shift I m
  · intro I hKI hI
    let := hKI
    let := injective_roos_quasiIso I hI
    obtain ⟨hp, hprod⟩ := injective_product I
    refine ⟨?_, (fun n ↦ tower_evaluation_isKInjective _ I (op n)), hp, hprod,
      inferInstance, asIso (DerivedCategory.Q.map (roosι I)), rfl,
      normalizedBoundary_distinguished I, normalizedBoundary_eq I, ?_⟩
    · intro i n
      let := hI i
      exact injective_tower_transition_split (I.X i) n
    · intro m
      have hshift (q : ℤ) : Injective ((I⟦m⟧).X q) := by
        change Injective (I.X (q + m))
        exact hI (q + m)
      let := injective_roos_quasiIso (I⟦m⟧) hshift
      exact ⟨localized_inclusion_shift I m, normalizedBoundary_shift I m⟩
  · intro I I' hKI hKI' hI hI' f
    let := injective_roos_quasiIso I hI
    let := injective_roos_quasiIso I' hI'
    exact normalizedBoundary_natural f
  · intro RF η hRF hη X I q hq hKI hI
    let := hq
    let := hKI
    let := injective_roos_quasiIso I hI
    exact derived_representative RF η hη X I q

end CategoryTheory

