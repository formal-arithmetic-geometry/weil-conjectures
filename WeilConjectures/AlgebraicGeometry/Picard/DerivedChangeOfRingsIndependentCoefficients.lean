/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Derived change of rings on a ringed site

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YT, 06YY, and
literature/stacks-project/derived.tex, Tag 06XN
(blueprint: lem-pur-derived-change-of-rings).

The change of rings `- ⊗_O O'` is the landed `SheafOfModules.changeOfRings φ` on objects
and `SheafOfModules.changeOfRingsHom φ` on morphisms (def-pur-sheaf-tensor-product); the
statement asserts an additive functor `E` with exactly these objects and maps, and uses
`E.mapHomologicalComplex` (termwise change of rings of complexes) and
`E.mapHomotopyCategory ⋙ DerivedCategory.Qh` (the functor `K(O) → D(O')`).

## Main definitions

- `derivedChangeRingIndependentCoefficients`: the underlying ring sheaf in independent site
  universes.

## Main statements

- `derivedChangeOfRingsIndependentCoefficients`: the full derived-change-of-rings statement without
  identifying the object and morphism universes of the site.
-/

@[expose] public section

universe w r u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

section IndependentTensor

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

-- Step 1: the same tensor abelian group, with the two scalar actions identified.
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionTensorIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (M : SheafOfModules.{r} (𝓡 O))
    (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X ≅
      (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X := by
  let e : (((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M)).obj X) ≃ₗ[O.obj.obj X]
      ((((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val).obj X) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => rfl
        | add x y hx hy => simpa only [smul_add] using congrArg₂ (· + ·) hx hy }
  exact e.toModuleIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def presheafTensorIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    (M : SheafOfModules.{r} (𝓡 O)) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
        (changeOfRingsPresheaf φ M) ≅
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (𝓡 O'))).val ⊗ M.val :=
  PresheafOfModules.isoMk (sectionTensorIso φ M) (by
    intro X Y f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      change changeOfRingsMap φ M f (s ⊗ₜ m) = _
      rw [show changeOfRingsMap φ M f (s ⊗ₜ m) = _ from
        Classical.choose_spec (exists_changeOfRingsMap φ M f) s m]
      rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

private noncomputable def changePresheafHom
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
  { app := fun X ↦ (ModuleCat.extendScalars (φ.hom.app X).hom).map (a.val.app X)
    naturality := changeOfRingsHom_naturality φ M a }

set_option backward.isDefEq.respectTransparency false in
private lemma presheafTensorIso_naturality
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O')
    {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
        (changePresheafHom φ a) ≫ (presheafTensorIso φ N).hom =
      (presheafTensorIso φ M).hom ≫
        ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit (𝓡 O'))).val ◁ a.val := by
  ext X x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

-- Step 2: compare the underlying abelian sheaves using the sheafification API.
private noncomputable def underlyingSheafificationIso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O') :
    PresheafOfModules.sheafification (𝟙 (𝓡 O').obj) ⋙ toSheaf (𝓡 O') ≅
      PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom ⋙
        (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj) ⋙ toSheaf (𝓡 O)) :=
  PresheafOfModules.sheafificationCompToSheaf (𝟙 (𝓡 O').obj) ≪≫
    (Functor.isoWhiskerRight (PresheafOfModules.restrictScalarsCompToPresheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom)
      (presheafToSheaf J AddCommGrpCat)).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (PresheafOfModules.sheafificationCompToSheaf (𝟙 (𝓡 O).obj)).symm

-- Step 3: naturality of the existing tensor comparison, from the counit and tensorator.
set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_naturality
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O : Sheaf J CommRingCat.{r}}
    (S : SheafOfModules.{r} (𝓡 O)) {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N) :
    letI := monoidalCategory O
    (PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)).map (S.val ◁ a.val) ≫
      (tensorObjIsoSheafification S N).inv =
    (tensorObjIsoSheafification S M).inv ≫ S ◁ a := by
  let := monoidalCategory O
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let ε : forget (𝓡 O) ⋙ A ≅ 𝟭 _ :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 O).obj)).counit
  let c (M : SheafOfModules.{r} (𝓡 O)) : A.obj M.val ≅ M := ε.app M
  apply (cancel_mono (tensorObjIsoSheafification S N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorObjIsoSheafification S M).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change ((c S).inv ⊗ₘ (c M).inv) ≫
      Functor.LaxMonoidal.μ A S.val M.val ≫ A.map (S.val ◁ a.val) =
    S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) ≫
      Functor.LaxMonoidal.μ A S.val N.val
  rw [← Functor.LaxMonoidal.μ_natural_right]
  have hn : (c M).inv ≫ A.map a.val = a ≫ (c N).inv :=
    (ε.inv.naturality a).symm
  have h : ((c S).inv ⊗ₘ (c M).inv) ≫
      (A.obj S.val ◁ A.map a.val) =
      S ◁ a ≫ ((c S).inv ⊗ₘ (c N).inv) := by
    calc
      _ = (c S).inv ⊗ₘ ((c M).inv ≫ A.map a.val) := by
        simpa only [Category.comp_id, id_tensorHom] using
          (tensorHom_comp_tensorHom (c S).inv (c M).inv
            (𝟙 (A.obj S.val)) (A.map a.val))
      _ = (c S).inv ⊗ₘ (a ≫ (c N).inv) :=
        congrArg (fun f ↦ (c S).inv ⊗ₘ f) hn
      _ = _ := by
        simpa only [Category.id_comp, id_tensorHom] using
          (tensorHom_comp_tensorHom (𝟙 S) a (c S).inv (c N).inv).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f ↦ f ≫ Functor.LaxMonoidal.μ A S.val N.val) h) |>.trans
      (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 03EK and Tag 06YY, degree-zero tensor comparison.

Proof: Put U = restriction along φ and S = U(O'). Before sheafification the
identity on pure tensors identifies the restricted sectionwise scalar extension
O'(V) tensor over O(V) M(V) with the sectionwise tensor of S and M. It respects
restrictions because both constructions restrict each tensor factor, and respects
module morphisms because both apply id tensor a. The standard natural isomorphisms
for forgetting scalar restriction and module sheafification identify their underlying
abelian sheaves. Sheafifying the presheaf tensor comparison therefore gives the
asserted isomorphisms of abelian sheaves, sufficient to detect acyclicity.
The counit at the already-sheaf module S and the monoidal localization comparison
identify the resulting sheafification with S tensor M. Naturality survives each
comparison and sheafification, giving the displayed equation for every a.
This uses no flatness; the identity on tensors also covers zero rings and modules.
(blueprint: lem-pur-change-of-rings-tensor-comparison) -/
private theorem exists_changeOfRings_tensor_comparison_independent
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {O O' : Sheaf J CommRingCat.{r}} (φ : O ⟶ O') :
    letI := monoidalCategory O
    let U := restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
    let S := U.obj (unit (𝓡 O'))
    ∃ e : ∀ M : SheafOfModules.{r} (𝓡 O),
      (toSheaf (𝓡 O')).obj (changeOfRings φ M) ≅ (toSheaf (𝓡 O)).obj (S ⊗ M),
      ∀ {M N : SheafOfModules.{r} (𝓡 O)} (a : M ⟶ N),
        (toSheaf (𝓡 O')).map (changeOfRingsHom φ M a) ≫ (e N).hom =
          (e M).hom ≫ (toSheaf (𝓡 O)).map (S ◁ a) := by
  let := monoidalCategory O
  let U := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let S := U.obj (unit (𝓡 O'))
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 O).obj)
  let V := toSheaf (𝓡 O)
  let e (M : SheafOfModules.{r} (𝓡 O)) :
      (toSheaf (𝓡 O')).obj (changeOfRings φ M) ≅ V.obj (S ⊗ M) :=
    (underlyingSheafificationIso φ).app (changeOfRingsPresheaf φ M) ≪≫
      V.mapIso (A.mapIso (presheafTensorIso φ M) ≪≫
        (tensorObjIsoSheafification S M).symm)
  refine ⟨e, ?_⟩
  intro M N a
  have hr := (underlyingSheafificationIso φ).hom.naturality (changePresheafHom φ a)
  have hp := congrArg (fun f ↦ V.map (A.map f)) (presheafTensorIso_naturality φ a)
  simp only [Functor.map_comp] at hp
  have ht := congrArg V.map (tensorComparison_naturality S a)
  simp only [Functor.map_comp] at ht
  change (toSheaf (𝓡 O')).map
      ((PresheafOfModules.sheafification (𝟙 (𝓡 O').obj)).map (changePresheafHom φ a)) ≫
        (e N).hom = (e M).hom ≫ V.map (S ◁ a)
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, reassoc_of% hp, ht]


section TensorAcyclicity

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {O : Sheaf J CommRingCat.{r}}

attribute [local instance] monoidalCategory symmetricCategory
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance] monoidalPreadditive_independent

end TensorAcyclicity


end IndependentTensor

end SheafOfModules
