/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-! # The unbounded scalar model of an ind-finite-free algebra sheaf

Source: Stacks Project, sites-modules.tex, Tags 03EU (2), 03EP (2), and Section 03EK;
sites-cohomology.tex, Tags 06YT and 06YY; derived.tex, Tag 015F.
(blueprint: lem-sfb-ind-finite-free-scalar-model).
The auxiliary functors spell out the coefficient diagram and its termwise tensor colimit.
All derived scalar extensions are the existing universal cochain models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS wT
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.IndFiniteFree

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module category at the coefficient universe.
Source: Stacks 03D2 (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- Ordinary scalar restriction, with the same sections and restricted action.
Source: Stacks 03D2 (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Forget the algebra structure of an algebra sheaf, retaining its R-module structure.
On morphisms this is the original section map, linear by the triangle over R.
Source: Stacks 03EK (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def algebraModules (R : Sheaf J CommRingCat.{r}) : Under R ⥤ Modules R where
  obj A := (restriction A.hom).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A.right))
  map {A B} f :=
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight f.right.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
          intro V x a
          change A.right.obj.obj V at a
          change R.obj.obj V at x
          change (f.right.hom.app V).hom ((A.hom.hom.app V).hom x * a) =
            (B.hom.hom.app V).hom x * (f.right.hom.app V).hom a
          rw [map_mul]
          congr 1
          exact congrArg (fun t ↦ t.hom.app V x) (Under.w f)) }

/-- Tensor a complex termwise with a coefficient module; coefficient maps act by tensor.
Source: Stacks 03EK (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorComplex (R : Sheaf J CommRingCat.{r}) :
    Modules R ⥤ (CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ) where
  obj M := (tensorLeft M).mapHomologicalComplex (.up ℤ)
  map f := ((curriedTensor (Modules R)).map f).mapHomologicalComplex (.up ℤ)
  map_id M := by simp
  map_comp f g := by simp

/-- The diagram i ↦ S_i tensor A, with all differentials and transitions termwise.
Source: Stacks 03EP (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorDiagram {R : Sheaf J CommRingCat.{r}} {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (A : CochainComplex (Modules R) ℤ) :
    I ⥤ CochainComplex (Modules R) ℤ :=
  (D ⋙ algebraModules R ⋙ tensorComplex R).flip.obj A

/-- The actual colimit functor on these complexes. Colimits of complexes are termwise.
Source: Stacks 03EP (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorColimit {R : Sheaf J CommRingCat.{r}} {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (D ⋙ algebraModules R ⋙ tensorComplex R).flip ⋙ colim

/-- A pure tensor in the sheaf tensor, using its presheaf-to-sheaf unit.
The supplied factor is the actual underlying module, not a choice of basis.
Source: Stacks 03EK, 03CY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def pureTensor {R : Sheaf J CommRingCat.{r}} (M N : Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) : (M ⊗ N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
      (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y) |>
    (tensorObjIsoSheafification M N).inv.val.app V

private theorem pureTensor_ext {R : Sheaf J CommRingCat.{r}}
    {M N P : Modules R} (f g : M ⊗ N ⟶ P)
    (h : ∀ (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (pureTensor M N V x y) = g.val.app V (pureTensor M N V x y)) :
    f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  ext t
  change f.val.app V ((tensorObjIsoSheafification M N).inv.val.app V
      ((adj.unit.app (M.val ⊗ N.val)).app V t)) =
    g.val.app V ((tensorObjIsoSheafification M N).inv.val.app V
      ((adj.unit.app (M.val ⊗ N.val)).app V t))
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h V x y
  | add t t' ht ht' => simp only [map_add, ht, ht']

variable {R : Sheaf J CommRingCat.{r}} in
/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom (A : Modules R)
    {T T' : Modules R} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

variable {R : Sheaf J CommRingCat.{r}} in
/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
private lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : Modules R}
    (f : A' ⟶ A) (T : Modules R) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).map (f.val ▷ T.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private theorem pureTensor_whiskerRight {R : Sheaf J CommRingCat.{r}}
    {M M' : Modules R} (f : M ⟶ M') (N : Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (f ▷ N).val.app V (pureTensor M N V x y) =
      pureTensor M' N V (f.val.app V x) y := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  have h : (tensorObjIsoSheafification M N).inv ≫ f ▷ N =
      (PresheafOfModules.sheafification (𝟙
        (derivedChangeRingIndependentCoefficients J R).obj)).map (f.val ▷ N.val) ≫
          (tensorObjIsoSheafification M' N).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerRight_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] y))
    (adj.unit.naturality (f.val ▷ N.val))
  have he := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y))) h
  exact he.trans (congrArg ((tensorObjIsoSheafification M' N).inv.val.app V) hh.symm)

private theorem pureTensor_whiskerLeft {R : Sheaf J CommRingCat.{r}}
    (M : Modules R) {N N' : Modules R} (f : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (M ◁ f).val.app V (pureTensor M N V x y) =
      pureTensor M N' V x (f.val.app V y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  have h : (tensorObjIsoSheafification M N).inv ≫ M ◁ f =
      (PresheafOfModules.sheafification (𝟙
        (derivedChangeRingIndependentCoefficients J R).obj)).map (M.val ◁ f.val) ≫
          (tensorObjIsoSheafification M N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerLeft_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] y))
    (adj.unit.naturality (M.val ◁ f.val))
  have he := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y))) h
  exact he.trans (congrArg ((tensorObjIsoSheafification M N').inv.val.app V) hh.symm)

private theorem tensorLeft_colimit_finiteLimits {R : Sheaf J CommRingCat.{r}}
    {K : Type r} [SmallCategory K] [HasExactColimitsOfShape K (Modules R)]
    (F : K ⥤ Modules R) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ k, PreservesFiniteLimits (tensorLeft (F.obj k))) :
    PreservesFiniteLimits (tensorLeft c.pt) := by
  have hcol (M : Modules R) : PreservesColimitsOfSize.{r, r} (tensorRight M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : PreservesColimit F (curriedTensor (Modules R)) :=
    MonoidalCategory.Limits.preservesCoLimit_curriedTensor F
  let e : tensorLeft c.pt ≅ (F ⋙ curriedTensor (Modules R)).flip ⋙ colim :=
    (curriedTensor (Modules R)).mapIso (hc.coconePointUniqueUpToIso (colimit.isColimit F)) ≪≫
      preservesColimitIso (curriedTensor (Modules R)) F ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((F ⋙ curriedTensor (Modules R)).flip) :=
    preservesFiniteLimits_of_evaluation _ h
  have : PreservesFiniteLimits ((F ⋙ curriedTensor (Modules R)).flip ⋙ colim) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso e.symm

private theorem tensorLeft_finiteFree_finiteLimits {R : Sheaf J CommRingCat.{r}}
    (M : Modules R) (d : ℕ)
    (e : M ≅ ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)) :
    PreservesFiniteLimits (tensorLeft M) := by
  have : HasFiniteBiproducts (Modules R) := Abelian.hasFiniteBiproducts
  let U : Modules R := unit (derivedChangeRingIndependentCoefficients J R)
  let F : Discrete (ULift.{r} (Fin d)) ⥤ Modules R :=
    Discrete.functor (fun _ ↦ U)
  have : PreservesFiniteLimits (tensorLeft U) :=
    preservesFiniteLimits_of_natIso (leftUnitorNatIso (Modules R)).symm
  have : PreservesFiniteLimits (tensorLeft (colimit F)) :=
    tensorLeft_colimit_finiteLimits F (colimit.cocone F) (colimit.isColimit F)
      (fun _ ↦ inferInstanceAs (PreservesFiniteLimits (tensorLeft U)))
  let e' : M ≅ colimit F := e ≪≫
    (Pi.whiskerEquiv (Equiv.ulift : ULift.{r} (Fin d) ≃ Fin d) (fun _ ↦ Iso.refl U)).symm ≪≫
      (HasBiproductsOfShape.colimIsoLim.app F).symm
  exact preservesFiniteLimits_of_natIso ((curriedTensor (Modules R)).mapIso e').symm

section OrdinaryComparison

variable {R S : Sheaf J CommRingCat.{r}}

private def restrictedTensorPresheafIso (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⊗ M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf.{v, u, r} φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (φ.hom.app V).hom
    let T := TensorProduct (R.obj.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
      (M.val.obj V)
    change ModuleCat.of (R.obj.obj V) T ≅
      (ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) T)
    exact (LinearEquiv.refl (R.obj.obj V) T).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

section
variable {R₀ B₀ : Sheaf J RingCat.{r}}

private noncomputable def restrictionSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictionSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{r}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_unit
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj)
    (W : Cᵒᵖ) (x : P.obj W) :
    (restrictionSheafificationComparison α P).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app
          ((PresheafOfModules.restrictScalars α.hom).obj P)).app W x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P).app W x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars α.hom).obj P)
    (F := (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P))
    (𝟙 R₀.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))
  exact congrArg (fun k ↦ (k.app W) x) h

end

/-- The canonical map from the presheaf tensor to the underlying sheaf tensor.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
private def tensorPresheafUnit
    (M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
      (tensorObjIsoSheafification M N).inv.val

set_option maxHeartbeats 50000 in
-- Mixed tensor coefficient structures require additional elaboration.
/-- Restricted extension of scalars is tensoring with the restricted target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison).

Proof: the presheaf tensor of the restricted target ring with M has exactly the
same section modules as restricted sectionwise scalar extension. Both restriction
maps send s tensor m to the tensor of the two restrictions, so the identity maps
form an isomorphism. Sheafify it over R. Restriction commutes with sheafification:
after forgetting to abelian sheaves the comparison is the identity of the same
sheafification, and forgetting reflects isomorphisms. Compose with the canonical
tensor-sheafification comparison. Naturality of the sheafification unit gives the
pure-tensor formula. No flatness or localization assumption is used. -/
private theorem exists_extensionTensorComparison (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (monoidalCategory R).tensorObj
        ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M ≅
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (changeOfRings.{v, u, r} φ M),
      ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
        e.hom.val.app V
          ((tensorPresheafUnit
            ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
              (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M).app V
            ((show ((restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
                  (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val.obj V
              from s) ⊗ₜ[R.obj.obj V] m)) =
        (toSheafify J (changeOfRingsPresheaf.{v, u, r} φ M).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) := by
  let N := (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let P := changeOfRingsPresheaf.{v, u, r} φ M
  let SR := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := restrictedTensorPresheafIso φ M
  have := restrictionSheafificationComparison_isIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P
  let e := tensorObjIsoSheafification N M ≪≫ SR.mapIso eP ≪≫
    asIso (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P)
  have he : (tensorObjIsoSheafification N M).inv ≫ e.hom =
      SR.map eP.hom ≫ restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    simp only [Iso.inv_hom_id_assoc]
  clear_value e
  refine ⟨e, ?_⟩
  intro V s m
  have hn := adj.unit.naturality eP.hom
  have hn' := congrArg (fun k ↦ (k.app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) hn
  have hr' := restrictionSheafificationComparison_unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
  change ((tensorPresheafUnit N M ≫ e.hom.val).app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m) = _
  unfold tensorPresheafUnit
  rw [Category.assoc]
  change ((adj.unit.app (N.val ⊗ M.val) ≫
    ((tensorObjIsoSheafification N M).inv ≫ e.hom).val).app V) _ = _
  rw [he]
  change (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V
    ((SR.map eP.hom).val.app V
      ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m))) = _
  change (adj.unit.app ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P)).app V
        (eP.hom.app V ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) =
      (SR.map eP.hom).val.app V ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) at hn'
  exact (congrArg ((restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V) hn'.symm).trans hr'


end OrdinaryComparison

variable {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]

/-- The pure tensor in the ordinary functor of the existing derived scalar model.
Source: Stacks 03EK, 06YY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def extensionPure (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (M : Modules R) (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (m.E.obj M).val.obj V :=
  (eqToHom (m.obj_eq M).symm).val.app V
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))

private theorem extensionPure_naturality
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    {M N : Modules R} (f : M ⟶ N) (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (m.E.map f).val.app V (extensionPure m M V s a) =
      extensionPure m N V s (f.val.app V a) := by
  let g : changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
    { app := fun W ↦ (ModuleCat.extendScalars (φ.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality φ M f }
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)
  have hn := congrArg (fun k ↦ k.app V (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))
    (adj.unit.naturality g)
  have hh : eqToHom (m.obj_eq M).symm ≫ m.E.map f =
      changeOfRingsHom φ M f ≫ eqToHom (m.obj_eq N).symm := by
    rw [m.map_eq]
    simp
  have he := congrArg (fun k ↦ k.val.app V
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))) hh
  exact he.trans (congrArg ((eqToHom (m.obj_eq N).symm).val.app V) hn.symm)

private theorem extensionPure_smul
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) (M : Modules R)
    (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    extensionPure m M V s a = s • extensionPure m M V 1 a := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)
  change (eqToHom (m.obj_eq M).symm).val.app V
      ((adj.unit.app (changeOfRingsPresheaf φ M)).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a)) = _
  change _ = s • (eqToHom (m.obj_eq M).symm).val.app V
    ((adj.unit.app (changeOfRingsPresheaf φ M)).app V
      ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))
  rw [← (eqToHom (m.obj_eq M).symm).val.app V |>.hom.map_smul]
  rw [← ((adj.unit.app (changeOfRingsPresheaf φ M)).app V).hom.map_smul]
  congr 2
  exact ((ModuleCat.ExtendScalars.smul_tmul (φ.hom.app V).hom s 1 a).trans
    (congrArg (fun t ↦ t ⊗ₜ[R.obj.obj V,(φ.hom.app V).hom] a) (mul_one s))).symm

private theorem ordinaryAdjunction_pure
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (a : m.E ⊣ restriction φ)
    (ha : ∀ (M : Modules R) (N : Modules S)
      (f : changeOfRings φ M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V),
      (a.homEquiv M N (eqToHom (m.obj_eq M) ≫ f)).val.app V x =
        f.val.app V ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V,(φ.hom.app V).hom] x)))
    (M : Modules R) (N : Modules S) (f : m.E.obj M ⟶ N) (V : Cᵒᵖ)
    (x : M.val.obj V) :
    (a.homEquiv M N f).val.app V x = f.val.app V (extensionPure m M V 1 x) := by
  have h := ha M N (eqToHom (m.obj_eq M).symm ≫ f) V x
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at h
  simpa only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, extensionPure]
    using h

private noncomputable def restrictionComposition
    {T : Sheaf J CommRingCat.{r}} (ψ : S ⟶ T) (γ : R ⟶ T) (hγ : γ = φ ≫ ψ) :
    restriction ψ ⋙ restriction φ ≅ restriction γ :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦
      (ModuleCat.restrictScalarsComp'App (φ.hom.app V).hom (ψ.hom.app V).hom
        (γ.hom.app V).hom (congrArg (fun f ↦ (f.hom.app V).hom) hγ)
        (M.val.obj V)).symm) (by intros; ext x; rfl)))
    (by intros; ext V x; rfl)

private noncomputable def coefficientMap
    {T : Sheaf J CommRingCat.{r}} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [HasDerivedCategory.{wT} (Modules T)]
    (m' : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wT} γ)
    (adj : m.E ⊣ restriction φ) (adj' : m'.E ⊣ restriction γ) :
    m.E ⟶ m'.E ⋙ restriction ψ where
  app M := (adj.homEquiv _ _).symm
    (adj'.unit.app M ≫ (restrictionComposition ψ γ hγ).inv.app (m'.E.obj M))
  naturality {M N} f := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (f ≫ adj'.unit.app N) ≫ (restrictionComposition ψ γ hγ).inv.app _ =
      (adj'.unit.app M ≫ (restrictionComposition ψ γ hγ).inv.app _) ≫
        (restriction ψ ⋙ restriction φ).map (m'.E.map f)
    have hn := adj'.unit.naturality f
    change f ≫ adj'.unit.app N =
      adj'.unit.app M ≫ (restriction γ).map (m'.E.map f) at hn
    rw [hn, Category.assoc]
    rw [(restrictionComposition ψ γ hγ).inv.naturality]
    rfl

private theorem exists_coefficientMap
    {T : Sheaf J CommRingCat.{r}} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [HasDerivedCategory.{wT} (Modules T)]
    (m' : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wT} γ) :
    ∃ β : m.E ⟶ m'.E ⋙ restriction ψ,
      ∀ (M : Modules R) (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V),
      (β.app M).val.app V (extensionPure m M V s x) =
        extensionPure m' M V (ψ.hom.app V s) x := by
  obtain ⟨_, _, h⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adj, hadj⟩ := h m.E m.obj_eq m.map_eq
  obtain ⟨_, _, h'⟩ := sheafRingCoefficientOrdinaryAdjunction γ
  obtain ⟨adj', hadj'⟩ := h' m'.E m'.obj_eq m'.map_eq
  let β := coefficientMap hγ m m' adj adj'
  refine ⟨β, ?_⟩
  intro M V s x
  have hβ : (β.app M).val.app V (extensionPure m M V 1 x) =
      extensionPure m' M V 1 x := by
    rw [← ordinaryAdjunction_pure m adj hadj]
    change ((adj.homEquiv _ _) ((adj.homEquiv _ _).symm _)).val.app V x = _
    rw [Equiv.apply_symm_apply]
    change (adj'.unit.app M).val.app V x = _
    rw [← adj'.homEquiv_id]
    have hp := ordinaryAdjunction_pure m' adj' hadj' M (m'.E.obj M) (𝟙 _) V x
    exact hp
  rw [extensionPure_smul m]
  rw [((β.app M).val.app V).hom.map_smul]
  change (ψ.hom.app V s) •
    (show (m'.E.obj M).val.obj V from (β.app M).val.app V (extensionPure m M V 1 x)) = _
  rw [hβ]
  exact (extensionPure_smul m' M V (ψ.hom.app V s) x).symm

private noncomputable def ordinaryIso
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) (M : Modules R) :
    (algebraModules R).obj (Under.mk φ) ⊗ M ≅ (restriction φ).obj (m.E.obj M) :=
  (exists_extensionTensorComparison φ M).choose ≪≫
    (restriction φ).mapIso (eqToIso (m.obj_eq M).symm)

private theorem ordinaryIso_pure
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) (M : Modules R)
    (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (ordinaryIso m M).hom.val.app V
        (pureTensor ((algebraModules R).obj (Under.mk φ)) M V s a) =
      extensionPure m M V s a := by
  exact congrArg ((eqToHom (m.obj_eq M).symm).val.app V)
    ((exists_extensionTensorComparison φ M).choose_spec V s a)

private noncomputable def ordinaryComparison
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) :
    tensorLeft ((algebraModules R).obj (Under.mk φ)) ≅ m.E ⋙ restriction φ :=
  NatIso.ofComponents (ordinaryIso m) (by
    intro M N f
    apply pureTensor_ext
    intro V s a
    change (ordinaryIso m N).hom.val.app V
        ((((algebraModules R).obj (Under.mk φ)) ◁ f).val.app V
          (pureTensor _ M V s a)) =
      (m.E.map f).val.app V
        ((ordinaryIso m M).hom.val.app V (pureTensor _ M V s a))
    rw [pureTensor_whiskerLeft, ordinaryIso_pure, ordinaryIso_pure,
      extensionPure_naturality])

private noncomputable def moduleChainComparison
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) :
    (tensorLeft ((algebraModules R).obj (Under.mk φ))).mapHomologicalComplex (.up ℤ) ≅
      m.E.mapHomologicalComplex (.up ℤ) ⋙ (restriction φ).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (ordinaryComparison m) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

private noncomputable def tensorCocone {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D) (A : CochainComplex (Modules R) ℤ) :
    Cocone (tensorDiagram D A) where
  pt := ((tensorComplex R).obj ((algebraModules R).obj c.pt)).obj A
  ι :=
    { app := fun i ↦ ((tensorComplex R).map ((algebraModules R).map (c.ι.app i))).app A
      naturality := by
        intro i j f
        change (((tensorComplex R).map ((algebraModules R).map (D.map f))).app A) ≫
          (((tensorComplex R).map ((algebraModules R).map (c.ι.app j))).app A) = _
        rw [← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, c.w f]
        simp }

private noncomputable def tensorCoconeIsColimit {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit ((algebraModules R).mapCocone c))
    (A : CochainComplex (Modules R) ℤ) : IsColimit (tensorCocone D c A) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  have := tensorLeft_preservesColimits_independentCoefficients R (A.X n)
  have : PreservesColimitsOfSize.{r, r} (tensorRight (A.X n)) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (A.X n))
  exact isColimitOfPreserves (tensorRight (A.X n)) hc

private noncomputable def chainColimitComparison {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit ((algebraModules R).mapCocone c)) :
    tensorColimit D ≅ (tensorComplex R).obj ((algebraModules R).obj c.pt) :=
  NatIso.ofComponents
    (fun A ↦ (colimit.isColimit (tensorDiagram D A)).coconePointUniqueUpToIso
      (tensorCoconeIsColimit D c hc A)) (by
    intro A B f
    apply colimit.hom_ext
    intro i
    change colimit.ι (tensorDiagram D A) i ≫
        colimMap ((D ⋙ algebraModules R ⋙ tensorComplex R).flip.map f) ≫ _ = _
    change colimit.ι ((D ⋙ algebraModules R ⋙ tensorComplex R).flip.obj A) i ≫
      colim.map ((D ⋙ algebraModules R ⋙ tensorComplex R).flip.map f) ≫ _ = _
    rw [colimit.ι_map_assoc]
    have hA := (colimit.isColimit (tensorDiagram D A)).comp_coconePointUniqueUpToIso_hom
      (tensorCoconeIsColimit D c hc A) i
    have hB := (colimit.isColimit (tensorDiagram D B)).comp_coconePointUniqueUpToIso_hom
      (tensorCoconeIsColimit D c hc B) i
    dsimp only [tensorDiagram] at hA hB ⊢
    change colimit.ι _ i ≫ _ = _ at hA hB
    erw [hB, ← Category.assoc, hA]
    exact (((tensorComplex R).map ((algebraModules R).map (c.ι.app i))).naturality f))

omit [HasDerivedCategory.{wR} (Modules R)] in
private theorem chainColimitComparison_leg {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit ((algebraModules R).mapCocone c))
    (A : CochainComplex (Modules R) ℤ) (i : I) :
    colimit.ι (tensorDiagram D A) i ≫ (chainColimitComparison D c hc).hom.app A =
      ((tensorComplex R).map ((algebraModules R).map (c.ι.app i))).app A :=
  (colimit.isColimit (tensorDiagram D A)).comp_coconePointUniqueUpToIso_hom
    (tensorCoconeIsColimit D c hc A) i

private theorem ordinary_exact {I : Type r} [SmallCategory I]
    [HasExactColimitsOfShape I (Modules R)]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit ((algebraModules R).mapCocone c))
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty ((algebraModules R).obj (D.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom) :
    PreservesFiniteLimits m.E ∧ PreservesFiniteColimits m.E ∧
      PreservesFiniteLimits (restriction c.pt.hom) ∧
      PreservesFiniteColimits (restriction c.pt.hom) := by
  obtain ⟨hU, hU', ha⟩ := sheafRingCoefficientOrdinaryAdjunction c.pt.hom
  have := hU
  have := hU'
  obtain ⟨adj, _⟩ := ha m.E m.obj_eq m.map_eq
  have : PreservesColimits m.E := adj.leftAdjoint_preservesColimits
  have hstage (i : I) :
      PreservesFiniteLimits (tensorLeft ((algebraModules R).obj (D.obj i))) := by
    obtain ⟨d, ⟨e⟩⟩ := hfree i
    exact tensorLeft_finiteFree_finiteLimits _ d e
  have : PreservesFiniteLimits (tensorLeft ((algebraModules R).obj c.pt)) :=
    tensorLeft_colimit_finiteLimits (D ⋙ algebraModules R)
      ((algebraModules R).mapCocone c) hc hstage
  have : PreservesFiniteLimits
      (tensorLeft ((algebraModules R).obj (Under.mk c.pt.hom))) := by
    change PreservesFiniteLimits (tensorLeft ((algebraModules R).obj c.pt))
    infer_instance
  have : PreservesFiniteLimits (m.E ⋙ restriction c.pt.hom) :=
    preservesFiniteLimits_of_natIso (ordinaryComparison m)
  have : (restriction c.pt.hom).ReflectsIsomorphisms := by
    have : (restriction c.pt.hom ⋙ toSheaf
        (derivedChangeRingIndependentCoefficients J R)).ReflectsIsomorphisms :=
      inferInstanceAs ((toSheaf
        (derivedChangeRingIndependentCoefficients J c.pt.right)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp _ (toSheaf _)
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves m.E (restriction c.pt.hom),
    inferInstance, hU, hU'⟩

private theorem counit_isIso
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [PreservesFiniteLimits m.E] [PreservesFiniteColimits m.E] : IsIso m.ε := by
  have h := (m.E.exactFunctor_derivedFunctor m.E.mapDerivedCategory
    m.E.mapDerivedCategoryFactors).2.2.2.1 m.T m.ε m.universal
  have (A : CochainComplex (Modules R) ℤ) : IsIso (m.ε.app A) := h A
  exact NatIso.isIso_of_isIso_app _

private noncomputable def normalizedComparison {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit ((algebraModules R).mapCocone c))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom) :
    tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ) :=
  chainColimitComparison D c hc ≪≫ moduleChainComparison m

private theorem normalizedComparison_leg {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit ((algebraModules R).mapCocone c))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    (A : CochainComplex (Modules R) ℤ) (i : I) (n : ℤ) (V : Cᵒᵖ)
    (s : (D.obj i).right.obj.obj V) (a : (A.X n).val.obj V) :
    (((colimit.ι (tensorDiagram D A) i) ≫
      (normalizedComparison D c hc m).hom.app A).f n).val.app V
        (pureTensor ((algebraModules R).obj (D.obj i)) (A.X n) V s a) =
      extensionPure m (A.X n) V ((c.ι.app i).right.hom.app V s) a := by
  have h := chainColimitComparison_leg D c hc A i
  change (((colimit.ι (tensorDiagram D A) i ≫
    (chainColimitComparison D c hc).hom.app A) ≫ (moduleChainComparison m).hom.app A).f n
      ).val.app V _ = _
  rw [h]
  change (ordinaryIso m (A.X n)).hom.val.app V
    ((((algebraModules R).map (c.ι.app i)) ▷ (A.X n)).val.app V
      (pureTensor ((algebraModules R).obj (D.obj i)) (A.X n) V s a)) = _
  rw [pureTensor_whiskerRight]
  change (ordinaryIso m (A.X n)).hom.val.app V
    (pureTensor ((algebraModules R).obj (Under.mk c.pt.hom)) (A.X n) V
      ((c.ι.app i).right.hom.app V s) a) = _
  exact ordinaryIso_pure m (A.X n) V _ a

/-- Normalization of the chain comparison on the sheafification-unit images of local
pure tensors. The coprojections are those of the supplied algebra colimit.
Source: Stacks 03EP, 03CY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def Normalized {I : Type r} [SmallCategory I] (D : I ⥤ Under R) (c : Cocone D)
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    (κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (A : CochainComplex (Modules R) ℤ) (i : I) (n : ℤ) (V : Cᵒᵖ)
    (s : (D.obj i).right.obj.obj V) (a : (A.X n).val.obj V),
    (((colimit.ι (tensorDiagram D A) i) ≫ κ.hom.app A).f n).val.app V
        (pureTensor ((algebraModules R).obj (D.obj i)) (A.X n) V s a) =
      extensionPure m (A.X n) V ((c.ι.app i).right.hom.app V s) a

/-- Compatibility of the chain comparison and the derived counit with coefficient
maps, also allowing a functor between the indexing categories. Both ordinary maps are
specified by their local tensors or their colimit legs. The derived map is specified by
its square with the counits after exact restriction along S → S'; its naturality includes
inverted quasi-isomorphisms. The underlying R-linear map has the same section maps.
Source: Stacks 03EP, 06YY, and localization 04VK
(blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def CoefficientCompatible {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    [PreservesFiniteLimits (restriction c.pt.hom)]
    [PreservesFiniteColimits (restriction c.pt.hom)]
    (κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (I' : Type r) [SmallCategory I'] [IsFiltered I']
    [HasExactColimitsOfShape I' (Modules R)]
    (D' : I' ⥤ Under R) (c' : Cocone D'),
    IsColimit c' → IsColimit ((algebraModules R).mapCocone c') →
    (∀ i : I', ∃ d : ℕ, Nonempty ((algebraModules R).obj (D'.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R))) →
    ∀ [HasDerivedCategory.{wT} (Modules c'.pt.right)]
      (m' : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wT} c'.pt.hom)
      (κ' : tensorColimit D' ≅ m'.E.mapHomologicalComplex (.up ℤ) ⋙
        (restriction c'.pt.hom).mapHomologicalComplex (.up ℤ)),
      Normalized D' c' m' κ' →
      ∀ (F : I ⥤ I') (τ : D ⟶ F ⋙ D') (h : c.pt ⟶ c'.pt),
        (∀ i : I, c.ι.app i ≫ h = τ.app i ≫ c'.ι.app (F.obj i)) →
        ∃ (_ : PreservesFiniteLimits (restriction c'.pt.hom))
          (_ : PreservesFiniteColimits (restriction c'.pt.hom))
          (_ : PreservesFiniteLimits (restriction h.right))
          (_ : PreservesFiniteColimits (restriction h.right))
          (βS : m.E ⟶ m'.E ⋙ restriction h.right)
          (β : m.E ⋙ restriction c.pt.hom ⟶ m'.E ⋙ restriction c'.pt.hom)
          (L : tensorColimit D ⟶ tensorColimit D')
          (βD : m.T ⟶ m'.T ⋙ (restriction h.right).mapDerivedCategory),
          (∀ (M : Modules R) (V : Cᵒᵖ) (z : (m.E.obj M).val.obj V),
            (β.app M).val.app V z = (βS.app M).val.app V z) ∧
          (∀ (M : Modules R) (V : Cᵒᵖ) (s : c.pt.right.obj.obj V) (a : M.val.obj V),
            (βS.app M).val.app V (extensionPure m M V s a) =
              extensionPure m' M V (h.right.hom.app V s) a) ∧
          (∀ (A : CochainComplex (Modules R) ℤ) (i : I),
            colimit.ι (tensorDiagram D A) i ≫ L.app A =
              (((tensorComplex R).map ((algebraModules R).map (τ.app i))).app A) ≫
                colimit.ι (tensorDiagram D' A) (F.obj i)) ∧
          (∀ A : CochainComplex (Modules R) ℤ,
            L.app A ≫ κ'.hom.app A =
              κ.hom.app A ≫ (β.mapHomologicalComplex (.up ℤ)).app A) ∧
          (∀ A : CochainComplex (Modules R) ℤ,
            m.ε.app A ≫ DerivedCategory.Q.map ((βS.mapHomologicalComplex (.up ℤ)).app A) =
              βD.app (DerivedCategory.Q.obj A) ≫
                (restriction h.right).mapDerivedCategory.map (m'.ε.app A) ≫
                (restriction h.right).mapDerivedCategoryFactors.hom.app
                  ((m'.E.mapHomologicalComplex (.up ℤ)).obj A))

private noncomputable def underlyingCoefficientMap
    {T : Sheaf J CommRingCat.{r}} {ψ : S ⟶ T} {γ : R ⟶ T}
    (hγ : γ = φ ≫ ψ)
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [HasDerivedCategory.{wT} (Modules T)]
    (m' : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wT} γ)
    (βS : m.E ⟶ m'.E ⋙ restriction ψ) :
    m.E ⋙ restriction φ ⟶ m'.E ⋙ restriction γ :=
  Functor.whiskerRight βS (restriction φ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft m'.E (restrictionComposition ψ γ hγ).hom

private theorem coefficientCompatible {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    [PreservesFiniteLimits m.E] [PreservesFiniteColimits m.E]
    [PreservesFiniteLimits (restriction c.pt.hom)]
    [PreservesFiniteColimits (restriction c.pt.hom)]
    (κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ))
    (hκ : Normalized D c m κ) :
    CoefficientCompatible.{u, v, r, wR, wS, wT} D c m κ := by
  classical
  intro I' _ _ _ D' c' hc' hcModules' hfree' _ m' κ' hκ' F τ h hh
  obtain ⟨hE', hE'', hU', hU''⟩ := ordinary_exact D' c' hcModules' hfree' m'
  have := hE'
  have := hE''
  have := hU'
  have := hU''
  obtain ⟨hH, hH', _⟩ := sheafRingCoefficientOrdinaryAdjunction h.right
  have := hH
  have := hH'
  have heq : c'.pt.hom = c.pt.hom ≫ h.right := (Under.w h).symm
  obtain ⟨βS, hβS⟩ := exists_coefficientMap heq m m'
  let β := underlyingCoefficientMap heq m m' βS
  have hβ (M : Modules R) (V : Cᵒᵖ) (z : (m.E.obj M).val.obj V) :
      (β.app M).val.app V z = (βS.app M).val.app V z := rfl
  let L : tensorColimit D ⟶ tensorColimit D' :=
    κ.hom ≫ β.mapHomologicalComplex (.up ℤ) ≫ κ'.inv
  have hL (A : CochainComplex (Modules R) ℤ) :
      L.app A ≫ κ'.hom.app A =
        κ.hom.app A ≫ (β.mapHomologicalComplex (.up ℤ)).app A := by
    simp [L]
  have hleg (A : CochainComplex (Modules R) ℤ) (i : I) :
      colimit.ι (tensorDiagram D A) i ≫ L.app A =
        (((tensorComplex R).map ((algebraModules R).map (τ.app i))).app A) ≫
          colimit.ι (tensorDiagram D' A) (F.obj i) := by
    apply (cancel_mono (κ'.hom.app A)).mp
    rw [Category.assoc, hL]
    apply HomologicalComplex.Hom.ext
    funext n
    apply pureTensor_ext
    intro V s a
    have hn := hκ A i n V s a
    have hn' := hκ' A (F.obj i) n V ((τ.app i).right.hom.app V s) a
    change (β.app (A.X n)).val.app V
        ((((colimit.ι (tensorDiagram D A) i) ≫ κ.hom.app A).f n).val.app V
          (pureTensor _ _ V s a)) = _
    rw [hn, hβ, hβS]
    change _ = (((colimit.ι (tensorDiagram D' A) (F.obj i) ≫ κ'.hom.app A).f n).val.app V
      ((((algebraModules R).map (τ.app i)) ▷ A.X n).val.app V
        (pureTensor _ _ V s a)))
    rw [pureTensor_whiskerRight]
    change _ = (((colimit.ι (tensorDiagram D' A) (F.obj i) ≫ κ'.hom.app A).f n).val.app V
      (pureTensor _ _ V ((τ.app i).right.hom.app V s) a))
    rw [hn']
    congr 1
    exact congrArg (fun f ↦ f.right.hom.app V s) (hh i)
  have hε := counit_isIso m
  have hε' := counit_isIso m'
  have := hε
  have := hε'
  let H := restriction h.right
  let e : DerivedCategory.Q ⋙ (m'.T ⋙ H.mapDerivedCategory) ≅
      (m'.E ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso m'.ε) H.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (m'.E.mapHomologicalComplex (.up ℤ))
        H.mapDerivedCategoryFactors
  let δ : DerivedCategory.Q ⋙ m.T ⟶
      DerivedCategory.Q ⋙ (m'.T ⋙ H.mapDerivedCategory) :=
    m.ε ≫ Functor.whiskerRight (βS.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q ≫ e.inv
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) (DerivedCategory (Modules c.pt.right))
  let βD : m.T ⟶ m'.T ⋙ H.mapDerivedCategory := ff.preimage δ
  have hβD : Functor.whiskerLeft DerivedCategory.Q βD = δ := ff.map_preimage δ
  refine ⟨hU', hU'', hH, hH', βS, β, L, βD, hβ, hβS, hleg, hL, ?_⟩
  intro A
  have hd := congrArg (fun t ↦ t.app A) hβD
  change βD.app (DerivedCategory.Q.obj A) = δ.app A at hd
  rw [hd]
  have he : e.hom.app A = H.mapDerivedCategory.map (m'.ε.app A) ≫
      H.mapDerivedCategoryFactors.hom.app ((m'.E.mapHomologicalComplex (.up ℤ)).obj A) := by
    simp [e]
  change _ = δ.app A ≫ H.mapDerivedCategory.map (m'.ε.app A) ≫
    H.mapDerivedCategoryFactors.hom.app ((m'.E.mapHomologicalComplex (.up ℤ)).obj A)
  erw [← he]
  dsimp only [δ, NatTrans.comp_app, Functor.whiskerRight_app]
  simp

/-- An ind-finite-free coefficient algebra has an exact ordinary scalar-extension model
on all unbounded complexes, with the canonical counit and normalized colimit comparison.
Source: Stacks Project, sites-modules.tex, Tags 03EU (2), 03EP (2), Section 03EK;
sites-cohomology.tex, Tags 06YT, 06YY; derived.tex, Tag 015F.
(blueprint: lem-sfb-ind-finite-free-scalar-model).

Proof:
1. A finite product of units is a finite coproduct of units. Tensor preservation of
   colimits identifies its tensor functor with a finite discrete colimit of the identity.
   Finite biproducts are exact, including rank zero.
2. Identify restricted extension with tensor by the restricted coefficient algebra.
   The private comparison sheafifies the identity on presheaf pure tensors and uses
   conservativity of the forgetful functor to abelian sheaves. Its normalization and
   naturality follow from sheafification and pure-tensor generation.
3. Exact I-colimits and Step 1 prove left exactness of tensor by the colimit algebra.
   Step 2 and exact conservative restriction transfer left exactness to E. The ordinary
   scalar adjunction makes E a left adjoint, so it is also right exact.
4. Tensor preservation of coefficient-small colimits gives a colimit cocone in each
   degree. Naturality in the differentials assembles the chain comparison. Its legs
   have the required pure-tensor formula.
5. For coefficient maps, transpose the target extension unit through the source
   ordinary adjunction. The normalized units give the formula at 1 tensor a; scalar
   linearity gives it at s tensor a. Restrict this map to obtain the R-linear map.
6. Exact functors preserve homology and hence quasi-isomorphisms on all unbounded
   complexes. Transport this assertion through the chain comparison for tensorColimit.
7. The exact-functor-derived-functor theorem makes the supplied universal counit
   invertible at every complex. Counit naturality computes its model along any
   quasi-isomorphism p:P to A, in particular along any supplied K-flat resolution.
   No choice or existence of a resolution is required.
8. Compose the counit with the canonical derived restriction factorization and the
   inverse chain comparison to construct theta. For two coefficient diagrams, conjugate
   the ordinary coefficient map by the normalized comparisons to define L. Equality
   on pure tensors proves its colimit-leg formula. Fully faithful precomposition with
   localization descends the ordinary coefficient map conjugated by the derived
   counits; its defining equation is the asserted derived-counit square. -/
theorem ind_finite_free_scalar_model
    {I : Type r} [SmallCategory I] [IsFiltered I]
    [HasExactColimitsOfShape I (Modules R)]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit c) (hcModules : IsColimit ((algebraModules R).mapCocone c))
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty ((algebraModules R).obj (D.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom) :
    ∃ (_ : PreservesFiniteLimits m.E) (_ : PreservesFiniteColimits m.E)
      (_ : PreservesFiniteLimits (restriction c.pt.hom))
      (_ : PreservesFiniteColimits (restriction c.pt.hom)),
      (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
        QuasiIso f → QuasiIso ((m.E.mapHomologicalComplex (.up ℤ)).map f)) ∧
      IsIso m.ε ∧
      (∀ (P A : CochainComplex (Modules R) ℤ) (p : P ⟶ A) [QuasiIso p],
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        ∃ e : m.T.obj (DerivedCategory.Q.obj A) ≅
            DerivedCategory.Q.obj ((m.E.mapHomologicalComplex (.up ℤ)).obj P),
          e.hom = m.T.map (inv (DerivedCategory.Q.map p)) ≫ m.ε.app P ∧
          e.hom ≫ DerivedCategory.Q.map ((m.E.mapHomologicalComplex (.up ℤ)).map p) =
            m.ε.app A) ∧
      ∃ κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
          (restriction c.pt.hom).mapHomologicalComplex (.up ℤ),
        Normalized D c m κ ∧
        (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
          QuasiIso f → QuasiIso ((tensorColimit D).map f)) ∧
        (∃ (KD : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R))
          (θ : DerivedCategory.Q ⋙ KD ≅ tensorColimit D ⋙ DerivedCategory.Q)
          (κD : KD ≅ m.T ⋙ (restriction c.pt.hom).mapDerivedCategory),
          ∀ A : CochainComplex (Modules R) ℤ,
            θ.hom.app A ≫ DerivedCategory.Q.map (κ.hom.app A) =
              κD.hom.app (DerivedCategory.Q.obj A) ≫
                (restriction c.pt.hom).mapDerivedCategory.map (m.ε.app A) ≫
                (restriction c.pt.hom).mapDerivedCategoryFactors.hom.app
                  ((m.E.mapHomologicalComplex (.up ℤ)).obj A)) ∧
        CoefficientCompatible.{u, v, r, wR, wS, wT} D c m κ := by
  classical
  have _hcAlgebra := hc
  obtain ⟨hE, hE', hU, hU'⟩ := ordinary_exact D c hcModules hfree m
  have := hE
  have := hE'
  have := hU
  have := hU'
  have hε : IsIso m.ε := counit_isIso m
  have := hε
  let κ := normalizedComparison D c hcModules m
  refine ⟨hE, hE', hU, hU', ?_, hε, ?_, κ, ?_, ?_, ?_, ?_⟩
  · intro A B f hf
    have := hf
    infer_instance
  · intro P A p hp hP
    let e := m.T.mapIso (asIso (DerivedCategory.Q.map p)).symm ≪≫
      (asIso m.ε).app P
    refine ⟨e, ?_, ?_⟩
    · simp [e]
    · dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        asIso_inv, Iso.app_hom, asIso_hom]
      have hn := m.ε.naturality p
      change m.T.map (DerivedCategory.Q.map p) ≫ m.ε.app A =
        m.ε.app P ≫ DerivedCategory.Q.map ((m.E.mapHomologicalComplex (.up ℤ)).map p) at hn
      rw [Category.assoc, ← hn, ← Category.assoc, ← m.T.map_comp]
      simp
  · exact normalizedComparison_leg D c hcModules m
  · intro A B f hf
    have := hf
    have : QuasiIso
        (((m.E.mapHomologicalComplex (.up ℤ) ⋙
          (restriction c.pt.hom).mapHomologicalComplex (.up ℤ))).map f) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology _ _
    have hn := κ.hom.naturality f
    have hh : QuasiIso ((tensorColimit D).map f ≫ κ.hom.app B) := by
      rw [hn]
      infer_instance
    exact (quasiIso_iff_comp_right _ (κ.hom.app B)).mp hh
  · let U := restriction c.pt.hom
    let EC := m.E.mapHomologicalComplex (.up ℤ)
    let θ : DerivedCategory.Q ⋙ (m.T ⋙ U.mapDerivedCategory) ≅
        tensorColimit D ⋙ DerivedCategory.Q :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso m.ε) U.mapDerivedCategory ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft EC U.mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight κ.symm DerivedCategory.Q
    refine ⟨m.T ⋙ U.mapDerivedCategory, θ, Iso.refl _, ?_⟩
    intro A
    simp only [θ, Iso.trans_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, asIso_hom, Iso.symm_hom, Category.id_comp,
      Category.assoc]
    rw [← DerivedCategory.Q.map_comp, κ.inv_hom_id_app]
    dsimp only [U, EC]
    simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    rw [DerivedCategory.Q.map_id]
    erw [Category.comp_id]
  · exact coefficientCompatible D c m κ (normalizedComparison_leg D c hcModules m)


end SheafOfModules.IndFiniteFree
