/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import Submission.WeilConjectures.CategoryTheory.ProductShift.ProductCommShift
import Submission.WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Signed strict Roos shifts and prescribed localization

Source: Stacks Project, Tag 014E, definition-cone; Tag 011G,
definition-shift-cochain; Tag 04VG, localization universal property
(blueprint: lem-a1-strict-roos-shift-localization).

The strict functor and inclusion are `roosF` and `roosι`. Natural tower index `n`
represents positive index `n+1`. The localization categories, their universes and
localization functors are arbitrary prescribed choices.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uT vT uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open CochainComplex

namespace StrictRoosShiftProof

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

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

end LimitModel

private noncomputable abbrev π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :=
  (Pi.π (fun n : ℕ ↦ N.asFunctor.obj (op n)) n).f q

private noncomputable abbrev v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :=
  (roosProj N).f q

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

attribute [local irreducible] productShiftComponent

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

attribute [local irreducible] roosShiftMap

attribute [local irreducible] roosCommShift

variable [HasLimitsOfShape ℕᵒᵖ A]

end StrictRoosShiftProof

open StrictRoosShiftProof

end CategoryTheory
