/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import all WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement

/-!
# Termwise inverse image of strict semilinear systems

Given algebraic inverse images `I n` of the coefficient rings at every level, together with
comparisons `ρ` between inverse image and scalar restriction along the transitions, we
construct the termwise inverse image of strict semilinear systems. Its transitions are the
inverse images of the source transitions, transported along `ρ`. We show that it is exact
when every level inverse image is, and we compare it with ordinary singleton extension.

## Main definitions

* `SheafOfModules.strictRingSystemInverseImage`: the termwise inverse image of strict systems.
* `SheafOfModules.strictRingSystemInverseImageSingle`: the comparison from singleton
  extension of an inverse image to the inverse image of a singleton extension.

## Main results

* `SheafOfModules.AlgebraicInverseImage.exact_modules`: the module part of an algebraic
  inverse image along a geometric morphism is exact.
* `SheafOfModules.strictRingSystemInverseImage_exact`: the termwise inverse image is exact.
* `SheafOfModules.isIso_strictRingSystemInverseImageSingle`: the singleton comparison is an
  isomorphism.

## Implementation details

The comparison `ρ` and the scalar-extension comparisons are parameters, characterized by their
effect on underlying sheaves of sets; their existence is
`SheafOfModules.InverseImageScalarRestriction.exists_comparison` and
`SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent`. All identities
between module maps are checked after forgetting to sheaves of sets, where every map in
sight is an inverse image of a map of sheaves of sets.

## References

* Stacks Project, Tags 03D2, 03DA, 03EL
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

section Exact

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The module part of an algebraic inverse image along a geometric morphism is exact. -/
theorem AlgebraicInverseImage.exact_modules
    (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (A : AlgebraicInverseImage u.inverse R S) :
    PreservesFiniteLimits A.modules ∧ PreservesFiniteColimits A.modules := by
  have h := ((GeometricMorphism.geometric_inverse_image_exact J K u).2.2 R).2 S
    (GeometricMorphism.inverseImageUniverses (C := C) (D := D) (J := J) (K := K)
      (L := u.inverse) (R := R) (S := S) A)
  exact (exactFunctor_iff _).mp h.1

omit [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On underlying sheaves of sets, an algebraic inverse image acts on module maps by the
inverse image of sheaves of sets. -/
theorem AlgebraicInverseImage.map_modules_underlying
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (A : AlgebraicInverseImage L R S)
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (f : M ⟶ N) :
    (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
        (A.modules.map f) =
      A.moduleUnderlying.hom.app M ≫
        L.map ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map f) ≫
          A.moduleUnderlying.inv.app N := by
  calc _ = ((A.modules ⋙ _).map f ≫ A.moduleUnderlying.hom.app N) ≫
        A.moduleUnderlying.inv.app N := by simp
    _ = _ := by rw [A.moduleUnderlying.hom.naturality f]; rfl

omit [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Conjugating the inverse image of the identity by the underlying comparison gives the
identity. -/
theorem AlgebraicInverseImage.conj_eq_id {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (A : AlgebraicInverseImage L R S)
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (f : (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj M ⟶
      (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj M)
    (hf : f = 𝟙 _) :
    A.moduleUnderlying.hom.app M ≫ L.map f ≫ A.moduleUnderlying.inv.app M = 𝟙 _ := by
  subst hf
  simp

end Exact

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w}}
  {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
  (I : ∀ n : ℕ, AlgebraicInverseImage L (BY.obj (op n)) (BX.obj (op n)))
  (ρ : ∀ {m n : ℕ} (h : m ≤ n),
    (I m).modules ⋙ systemRestriction BX h ≅ systemRestriction BY h ⋙ (I n).modules)
  (hρ : ∀ {m n : ℕ} (h : m ≤ n) (M : systemLevel BY m),
    (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
        ((ρ h).hom.app M) ≫
      (I n).moduleUnderlying.hom.app ((systemRestriction BY h).obj M) =
    (I m).moduleUnderlying.hom.app M)

/-- Scalar restriction does not change underlying sheaves of sets. -/
theorem systemRestriction_map_underlying {T : Type uC} [Category.{vC} T]
    {τ : GrothendieckTopology T}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (B : ℕᵒᵖ ⥤ Sheaf τ CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)
    {M N : SheafOfModules.{w} ((sheafCompose τ (forget₂ CommRingCat.{w} RingCat.{w})).obj
      (B.obj (op m)))} (f : M ⟶ N) :
    (toSheaf (derivedChangeRingIndependentCoefficients τ (B.obj (op n))) ⋙
        sheafCompose τ (CategoryTheory.forget AddCommGrpCat.{w})).map
        ((systemRestriction B h).map f) =
      (toSheaf (derivedChangeRingIndependentCoefficients τ (B.obj (op m))) ⋙
        sheafCompose τ (CategoryTheory.forget AddCommGrpCat.{w})).map f := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] in
include hρ in
/-- The inverse of the restriction comparison is the identity of the underlying inverse
image of sheaves of sets. -/
theorem systemRestrictionInverseImage_inv_underlying {m n : ℕ} (h : m ≤ n)
    (M : systemLevel BY m) :
    (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
        ((ρ h).inv.app M) =
      (I n).moduleUnderlying.hom.app ((systemRestriction BY h).obj M) ≫
        (I m).moduleUnderlying.inv.app M := by
  rw [← cancel_epi ((toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
    ((ρ h).hom.app M)), ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id,
    ← Category.assoc, hρ h M, Iso.hom_inv_id_app]
  rfl

/-- The transition of the termwise inverse image of a strict system. -/
abbrev strictRingSystemInverseImageTransition (M : StrictRingSystem BY) {m n : ℕ}
    (h : m ≤ n) :
    (I n).modules.obj (M.level n) ⟶ (systemRestriction BX h).obj ((I m).modules.obj (M.level m)) :=
  (I n).modules.map (M.transition h) ≫ (ρ h).inv.app (M.level m)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] in
include hρ in
/-- On underlying sheaves of sets, the inverse-image transition is the inverse image of the
source transition. -/
theorem strictRingSystemInverseImageTransition_underlying (M : StrictRingSystem BY)
    {m n : ℕ} (h : m ≤ n) :
    (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
        (strictRingSystemInverseImageTransition I ρ M h) =
      (I n).moduleUnderlying.hom.app (M.level n) ≫
        L.map ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
          (M.transition h)) ≫ (I m).moduleUnderlying.inv.app (M.level m) := by
  rw [Functor.map_comp, systemRestrictionInverseImage_inv_underlying I ρ hρ,
    AlgebraicInverseImage.map_modules_underlying]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] in
include hρ in
/-- The inverse-image transition along an identity is the identity on sections. -/
theorem strictRingSystemInverseImageTransition_identity (M : StrictRingSystem BY) (n : ℕ)
    (U : Dᵒᵖ)
    (x : ((I n).modules.obj (M.level n)).val.obj U) :
    (strictRingSystemInverseImageTransition I ρ M (Nat.le_refl n)).val.app U x = x := by
  have h1 : (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
      (M.transition (Nat.le_refl n)) = 𝟙 _ := by
    ext V y
    exact M.identity n V y
  have h2 := strictRingSystemInverseImageTransition_underlying I ρ hρ M (Nat.le_refl n)
  rw [h1, L.map_id] at h2
  erw [Category.id_comp, Iso.hom_inv_id_app] at h2
  exact congrArg (fun f ↦ f.hom.app U x) h2

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}] in
include hρ in
/-- The inverse-image transitions compose on sections. -/
theorem strictRingSystemInverseImageTransition_compose (M : StrictRingSystem BY) {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n) (U : Dᵒᵖ) (x : ((I n).modules.obj (M.level n)).val.obj U) :
    (strictRingSystemInverseImageTransition I ρ M (h.trans k)).val.app U x =
      (strictRingSystemInverseImageTransition I ρ M h).val.app U
        ((strictRingSystemInverseImageTransition I ρ M k).val.app U x) := by
  have h1 : (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
      (M.transition (h.trans k)) =
        (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
          (M.transition k) ≫
        (toSheaf (derivedChangeRingIndependentCoefficients J (BY.obj (op m))) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map (M.transition h) := by
    ext V y
    exact M.compose h k V y
  have h2 : (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
      (strictRingSystemInverseImageTransition I ρ M (h.trans k)) =
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
          (strictRingSystemInverseImageTransition I ρ M k) ≫
        (toSheaf (derivedChangeRingIndependentCoefficients K (BX.obj (op m))) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
          (strictRingSystemInverseImageTransition I ρ M h) := by
    rw [strictRingSystemInverseImageTransition_underlying I ρ hρ,
      strictRingSystemInverseImageTransition_underlying I ρ hρ,
      strictRingSystemInverseImageTransition_underlying I ρ hρ, h1, L.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun f ↦ f.hom.app U x) h2

/-- The termwise inverse image of a strict system. -/
def strictRingSystemInverseImageObj (M : StrictRingSystem BY) : StrictRingSystem BX where
  level n := (I n).modules.obj (M.level n)
  transition h := strictRingSystemInverseImageTransition I ρ M h
  identity := strictRingSystemInverseImageTransition_identity I ρ hρ M
  compose := strictRingSystemInverseImageTransition_compose I ρ hρ M

/-- The termwise inverse image of strict semilinear systems. -/
def strictRingSystemInverseImage : StrictRingSystem BY ⥤ StrictRingSystem BX where
  obj := strictRingSystemInverseImageObj I ρ hρ
  map {M N} f :=
    { app := fun n ↦ (I n).modules.map (f.app n)
      comm := fun {m n} h ↦ by
        change (I n).modules.map (f.app n) ≫ ((I n).modules.map (N.transition h) ≫
            (ρ h).inv.app (N.level m)) =
          ((I n).modules.map (M.transition h) ≫ (ρ h).inv.app (M.level m)) ≫
            (systemRestriction BX h).map ((I m).modules.map (f.app m))
        rw [← Category.assoc, ← Functor.map_comp, f.comm h, Functor.map_comp,
          Category.assoc, Category.assoc]
        exact congrArg ((I n).modules.map (M.transition h) ≫ ·)
          ((ρ h).inv.naturality (f.app m)) }
  map_id M := strictRingSystem_hom_ext BX _ _ fun n ↦ (I n).modules.map_id _
  map_comp f g := strictRingSystem_hom_ext BX _ _ fun n ↦ (I n).modules.map_comp _ _

/-- The termwise inverse image followed by evaluation is evaluation followed by the level
inverse image. -/
theorem strictRingSystemInverseImage_evaluation (n : ℕ) :
    strictRingSystemInverseImage I ρ hρ ⋙ systemEvaluation BX n =
      systemEvaluation BY n ⋙ (I n).modules := rfl

/-- The termwise inverse image is additive when every level inverse image is. -/
instance strictRingSystemInverseImage_additive [∀ n, (I n).modules.Additive] :
    (strictRingSystemInverseImage I ρ hρ).Additive where
  map_add {M N f g} := strictRingSystem_hom_ext BX _ _ fun n ↦ by
    have h1 : (f + g).app n = f.app n + g.app n := (systemEvaluation BY n).map_add
    have h2 : ((strictRingSystemInverseImage I ρ hρ).map f +
        (strictRingSystemInverseImage I ρ hρ).map g).app n =
          ((strictRingSystemInverseImage I ρ hρ).map f).app n +
            ((strictRingSystemInverseImage I ρ hρ).map g).app n :=
      (systemEvaluation BX n).map_add
    change (I n).modules.map ((f + g).app n) = _
    rw [h2, h1, Functor.map_add]
    rfl

/-- The termwise inverse image is exact when every level inverse image is. -/
theorem strictRingSystemInverseImage_exact [∀ n, (I n).modules.Additive]
    [∀ n, PreservesFiniteLimits (I n).modules] [∀ n, PreservesFiniteColimits (I n).modules] :
    PreservesFiniteLimits (strictRingSystemInverseImage I ρ hρ) ∧
      PreservesFiniteColimits (strictRingSystemInverseImage I ρ hρ) := by
  have hP : JointlyReflectIsomorphisms (fun n ↦ systemEvaluation BX n) :=
    ⟨fun f _ ↦ (strictRingSystem_isIso_iff BX f).2 fun n ↦ inferInstance⟩
  exact (exactFunctor_iff _).mp (hP.exactFunctor_of_iso (F := fun n ↦ systemEvaluation BY n)
    (strictRingSystemInverseImage I ρ hρ) (fun n ↦ (I n).modules)
    (fun n ↦ (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩) (fun n ↦ Iso.refl _))

section Single

variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
  (e : ∀ {j n : ℕ} (h : j ≤ n),
    systemTensor SY BY h ⋙ (I j).modules ≅ (I n).modules ⋙ systemTensor SX BX h)
  (he : ∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    L.map ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
        ((systemTensorAdj SY BY h).unit.app P)) ≫
      (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P) ≫
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
          ((e h).hom.app P) =
      (I n).moduleUnderlying.inv.app P ≫
        (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
          ((systemTensorAdj SX BX h).unit.app ((I n).modules.obj P)))

include hρ he in
/-- The transpose of the inverse scalar-extension comparison is the inverse image of the
scalar unit, transported along the restriction comparison. -/
theorem systemTensorInverseImage_inv_transpose {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n) :
    (systemTensorAdj SX BX h).homEquiv _ _ ((e h).inv.app P) =
      (I n).modules.map ((systemTensorAdj SY BY h).unit.app P) ≫
        (ρ h).inv.app ((systemTensor SY BY h).obj P) := by
  apply (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map_injective
  have h2 : (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
      ((systemTensorAdj SX BX h).unit.app ((I n).modules.obj P)) =
        (I n).moduleUnderlying.hom.app P ≫
          L.map ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
            ((systemTensorAdj SY BY h).unit.app P)) ≫
          (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P) ≫
            (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
              ((e h).hom.app P) := by
    rw [he h P, Iso.hom_inv_id_app_assoc]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    systemRestrictionInverseImage_inv_underlying I ρ hρ,
    AlgebraicInverseImage.map_modules_underlying]
  change _ ≫ (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
    ((e h).inv.app P) = _
  rw [h2]
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_app_assoc]
  rfl

include he in
/-- The scalar-extension comparison sends the inverse image of a local tensor `b ⊗ x` to the
local tensor of the inverse images of `b` and `x`. -/
theorem systemTensorInverseImage_hom_tmul {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n)
    (Z : Sheaf J (Type w))
    (b : Z ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj (BY.obj (op j)))
    (x : Z ⟶ (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj P)
    (z : Z ⟶ (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj
      ((systemTensor SY BY h).obj P))
    (hz : ∀ U t, z.hom.app U t =
      systemModelTmul (SY (BY.map (homOfLE h).op)).model P U (b.hom.app U t) (x.hom.app U t))
    (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W) :
    ((e h).hom.app P).val.app W
        ((L.map z ≫ (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P)).hom.app W t) =
      systemModelTmul (SX (BX.map (homOfLE h).op)).model ((I n).modules.obj P) W
        ((L.map b ≫ (I j).ringUnderlying.hom).hom.app W t)
        ((L.map x ≫ (I n).moduleUnderlying.inv.app P).hom.app W t) := by
  have hsmul := (I j).moduleSMul ((systemTensor SY BY h).obj P) Z b
    (x ≫ (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
      ((systemTensorAdj SY BY h).unit.app P)) z (by
        intro U s
        rw [hz U s]
        erw [(SY (BY.map (homOfLE h).op)).unit_normalized]
        simp only [systemModelTmul, one_smul]
        rfl) W t
  simp only [id] at hsmul
  have hu := congrArg (fun f ↦ f.hom.app W ((L.map x).hom.app W t)) (he h P)
  simp only [Functor.map_comp] at hsmul
  refine (congrArg (((e h).hom.app P).val.app W) hsmul).trans ?_
  refine ((((e h).hom.app P).val.app W).hom.map_smul _ _).trans ?_
  simp only [systemModelTmul]
  congr 1
  refine hu.trans ?_
  refine ((SX (BX.map (homOfLE h).op)).unit_normalized ((I n).modules.obj P) W _).trans ?_
  simp only [systemModelTmul, one_smul]
  rfl

include hρ he in
/-- At the identity transition, the scalar-extension comparison is compatible with the
tensor units. -/
theorem systemTensorInverseImage_hom_unit (TY : SystemTensorCoherence SY)
    (TX : SystemTensorCoherence SX) (n : ℕ) (P : systemLevel BY n) :
    (e (Nat.le_refl n)).hom.app P ≫ (TX.ordinaryUnit BX n).hom.app ((I n).modules.obj P) =
      (I n).modules.map ((TY.ordinaryUnit BY n).hom.app P) := by
  rw [← cancel_epi ((e (Nat.le_refl n)).inv.app P), Iso.inv_hom_id_app_assoc]
  apply ((systemTensorAdj SX BX (Nat.le_refl n)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    systemTensorInverseImage_inv_transpose I ρ hρ SY SX e he]
  apply (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map_injective
  have hY : (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).map
      ((systemTensorAdj SY BY (Nat.le_refl n)).homEquiv _ _
        ((TY.ordinaryUnit BY n).hom.app P)) = 𝟙 _ := by
    ext U y
    rw [Adjunction.homEquiv_unit]
    change ((TY.ordinaryUnit BY n).hom.app P).val.app U
      (((systemTensorAdj SY BY (Nat.le_refl n)).unit.app P).val.app U y) = y
    rw [(SY (BY.map (homOfLE (Nat.le_refl n)).op)).unit_normalized, TY.unit_normalized,
      one_smul]
  have hX : (toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).map
      ((systemTensorAdj SX BX (Nat.le_refl n)).homEquiv _ _
        ((TX.ordinaryUnit BX n).hom.app ((I n).modules.obj P))) = 𝟙 _ := by
    ext U y
    rw [Adjunction.homEquiv_unit]
    change ((TX.ordinaryUnit BX n).hom.app ((I n).modules.obj P)).val.app U
      (((systemTensorAdj SX BX (Nat.le_refl n)).unit.app
        ((I n).modules.obj P)).val.app U y) = y
    rw [(SX (BX.map (homOfLE (Nat.le_refl n)).op)).unit_normalized, TX.unit_normalized,
      one_smul]
  rw [Adjunction.homEquiv_unit, Functor.map_comp, systemRestriction_map_underlying] at hY
  rw [hX, Functor.map_comp, Functor.map_comp, systemRestrictionInverseImage_inv_underlying I ρ hρ,
    AlgebraicInverseImage.map_modules_underlying]
  rw [systemRestriction_map_underlying, AlgebraicInverseImage.map_modules_underlying]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc, ← L.map_comp_assoc]
  exact (AlgebraicInverseImage.conj_eq_id (I n) P _ hY).symm

/-- The comparison from singleton extension of a level inverse image to the inverse image of
the singleton extension, transposed from the inverse image of the singleton unit. -/
def strictRingSystemInverseImageSingle (n : ℕ) :
    (I n).modules ⋙ systemSingleFunctor SX TX BX n ⟶
      systemSingleFunctor SY TY BY n ⋙ strictRingSystemInverseImage I ρ hρ where
  app P := ((systemSingleAdjunction SX TX BX n).homEquiv _ _).symm
    ((I n).modules.map ((systemSingleAdjunction SY TY BY n).unit.app P))
  naturality P Q f := by
    apply ((systemSingleAdjunction SX TX BX n).homEquiv _ _).injective
    change ((systemSingleAdjunction SX TX BX n).homEquiv _ _)
        ((systemSingleFunctor SX TX BX n).map ((I n).modules.map f) ≫ _) =
      ((systemSingleAdjunction SX TX BX n).homEquiv _ _)
        (_ ≫ (strictRingSystemInverseImage I ρ hρ).map ((systemSingleFunctor SY TY BY n).map f))
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (I n).modules.map f ≫ (I n).modules.map _ =
      (I n).modules.map _ ≫ (I n).modules.map (((systemSingleFunctor SY TY BY n).map f).app n)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (I n).modules.map ((systemSingleAdjunction SY TY BY n).unit.naturality f)

include he in
/-- Below the selected level, the singleton comparison is the inverse scalar-extension
comparison. -/
theorem strictRingSystemInverseImageSingle_app_below {j n : ℕ} (h : j ≤ n)
    (P : systemLevel BY n) :
    (systemSingleBelow SX TX BX n h).inv.app ((I n).modules.obj P) ≫
        ((strictRingSystemInverseImageSingle I ρ hρ SY TY SX TX n).app P).app j =
      (e h).inv.app P ≫ (I j).modules.map ((systemSingleBelow SY TY BY n h).inv.app P) := by
  have hY : (systemTensorAdj SY BY h).unit.app P ≫
      (systemRestriction BY h).map ((systemSingleBelow SY TY BY n h).inv.app P) =
        (systemSingleAdjunction SY TY BY n).unit.app P ≫
          ((systemSingleFunctor SY TY BY n).obj P).transition h := by
    have ht := systemSingleTranspose SY TY BY n h P ((systemSingleFunctor SY TY BY n).obj P)
      (𝟙 _)
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at ht
    erw [Category.comp_id] at ht
    exact ht
  apply ((systemTensorAdj SX BX h).homEquiv _ _).injective
  rw [systemSingleTranspose SX TX BX n h, Adjunction.homEquiv_naturality_right,
    systemTensorInverseImage_inv_transpose I ρ hρ SY SX e he]
  dsimp only [strictRingSystemInverseImageSingle]
  erw [Equiv.apply_symm_apply]
  erw [← Category.assoc, ← Functor.map_comp, ← hY]
  refine (congrArg (· ≫ _) ((I n).modules.map_comp _ _)).trans ?_
  simp only [Category.assoc]
  exact congrArg ((I n).modules.map ((systemTensorAdj SY BY h).unit.app P) ≫ ·)
    ((ρ h).inv.naturality ((systemSingleBelow SY TY BY n h).inv.app P))

include he in
/-- The singleton comparison is an isomorphism. -/
theorem isIso_strictRingSystemInverseImageSingle [∀ n, (I n).modules.Additive] (n : ℕ) :
    IsIso (strictRingSystemInverseImageSingle I ρ hρ SY TY SX TX n) := by
  have (P : systemLevel BY n) :
      IsIso ((strictRingSystemInverseImageSingle I ρ hρ SY TY SX TX n).app P) := by
    refine (strictRingSystem_isIso_iff BX _).2 fun j ↦ ?_
    change IsIso (((strictRingSystemInverseImageSingle I ρ hρ SY TY SX TX n).app P).app j)
    by_cases hj : j ≤ n
    · have hf := strictRingSystemInverseImageSingle_app_below I ρ hρ SY TY SX TX e he hj P
      rw [← Iso.app_inv, Iso.inv_comp_eq] at hf
      rw [hf]
      infer_instance
    · have hX := systemSingleLevelAbove SX BX n ((I n).modules.obj P) (Nat.lt_of_not_ge hj)
      have hY := (I j).modules.map_isZero
        (systemSingleLevelAbove SY BY n P (Nat.lt_of_not_ge hj))
      exact ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

end Single

end SheafOfModules
