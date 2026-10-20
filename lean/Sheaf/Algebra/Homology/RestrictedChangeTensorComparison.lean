/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Restricted scalar extension at independent site universes

Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-pbc-restricted-change-tensor-independent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
attribute [local instance] monoidalCategory symmetricCategory
attribute [local irreducible] monoidalCategory

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
  have : IsIso ((toSheaf R₀).map (restrictionSheafificationComparison α P)) := by
    unfold restrictionSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    change IsIso (((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{r}).homEquiv
      P.presheaf _).symm
        ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{r}).unit.app P.presheaf))
    rw [Adjunction.homEquiv_symm_unit]
    infer_instance
  exact isIso_of_reflects_iso _ (toSheaf R₀)

attribute [local irreducible] restrictionSheafificationComparison

end

private theorem counitTensorComparison_natural
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (L : D ⥤ E) [L.Monoidal] (V : E ⥤ D) (ε : V ⋙ L ≅ 𝟭 E)
    (S : E) {M N : E} (f : M ⟶ N) :
    (ε.inv.app S ⊗ₘ ε.inv.app M) ≫
        Functor.LaxMonoidal.μ L (V.obj S) (V.obj M) ≫ L.map (V.obj S ◁ V.map f) =
      S ◁ f ≫ (ε.inv.app S ⊗ₘ ε.inv.app N) ≫
        Functor.LaxMonoidal.μ L (V.obj S) (V.obj N) := by
  let c (X : E) : L.obj (V.obj X) ≅ X := ε.app X
  rw [← Functor.LaxMonoidal.μ_natural_right]
  have hn : (c M).inv ≫ L.map (V.map f) = f ≫ (c N).inv :=
    (ε.inv.naturality f).symm
  have h : ((c S).inv ⊗ₘ (c M).inv) ≫
      (L.obj (V.obj S) ◁ L.map (V.map f)) =
      S ◁ f ≫ ((c S).inv ⊗ₘ (c N).inv) := by
    calc
      _ = (c S).inv ⊗ₘ ((c M).inv ≫ L.map (V.map f)) := by
        simpa only [Category.comp_id, id_tensorHom] using
          (tensorHom_comp_tensorHom ((c S).inv) ((c M).inv)
            (𝟙 (L.obj (V.obj S))) (L.map (V.map f)))
      _ = (c S).inv ⊗ₘ (f ≫ (c N).inv) :=
        congrArg (fun g ↦ (c S).inv ⊗ₘ g) hn
      _ = _ := by
        simpa only [Category.id_comp, id_tensorHom] using
          (tensorHom_comp_tensorHom (𝟙 S) f ((c S).inv) ((c N).inv)).symm
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun g ↦ g ≫ Functor.LaxMonoidal.μ L (V.obj S) (V.obj N)) h) |>.trans
      (Category.assoc _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorComparison_naturality
    (S : SheafOfModules.{r} (𝓡 R)) {M N : SheafOfModules.{r} (𝓡 R)} (a : M ⟶ N) :
    letI := monoidalCategory R
    (PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)).map (S.val ◁ a.val) ≫
      (tensorObjIsoSheafification S N).inv =
    (tensorObjIsoSheafification S M).inv ≫ S ◁ a := by
  let := monoidalCategory R
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  let ε : forget (𝓡 R) ⋙ A ≅ 𝟭 _ :=
    asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 R).obj)).counit
  apply (cancel_mono (tensorObjIsoSheafification S N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorObjIsoSheafification S M).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change (ε.inv.app S ⊗ₘ ε.inv.app M) ≫
      Functor.LaxMonoidal.μ A S.val M.val ≫ A.map (S.val ◁ a.val) =
    S ◁ a ≫ (ε.inv.app S ⊗ₘ ε.inv.app N) ≫
      Functor.LaxMonoidal.μ A S.val N.val
  exact counitTensorComparison_natural A (forget (𝓡 R)) ε S a

private def changePresheafHom (φ : R ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 R)} (f : M ⟶ N) :
    changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
  { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
    naturality := changeOfRingsHom_naturality φ M f }

omit [EssentiallySmall.{r} C] in
private lemma restrictedTensorPresheafIso_natural (φ : R ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 R)} (f : M ⟶ N) :
    (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit (𝓡 S))).val ◁ f.val) ≫ (restrictedTensorPresheafIso φ N).hom =
    (restrictedTensorPresheafIso φ M).hom ≫
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).map
          (changePresheafHom φ f) := by
  ext U x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

section
variable {R₀ B₀ : Sheaf J RingCat.{r}}


omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private lemma restrictionSheafificationComparison_natural
    (α : R₀ ⟶ B₀) {P Q : PresheafOfModules.{r} B₀.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).map
        ((PresheafOfModules.restrictScalars α.hom).map f) ≫
      restrictionSheafificationComparison α Q =
    restrictionSheafificationComparison α P ≫ (restrictScalars α).map
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)
  let V := PresheafOfModules.restrictScalars α.hom
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  change V.map f ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj))
        (restrictionSheafificationComparison α Q) =
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj))
        (restrictionSheafificationComparison α P) ≫
      V.map ((PresheafOfModules.sheafification (𝟙 B₀.obj)).map f).val
  dsimp only [restrictionSheafificationComparison]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg V.map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.naturality f)

end

private def restrictedChangeIso (φ : R ⟶ S) (M : SheafOfModules.{r} (𝓡 R)) :
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit (𝓡 S))) ⊗ M ≅
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (changeOfRings φ M) := by
  let α := (sheafCompose J (forget₂ CommRingCat RingCat)).map φ
  have := restrictionSheafificationComparison_isIso α (changeOfRingsPresheaf φ M)
  exact tensorObjIsoSheafification _ M ≪≫
    (PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)).mapIso
      (restrictedTensorPresheafIso φ M) ≪≫
    asIso (restrictionSheafificationComparison α (changeOfRingsPresheaf φ M))

private lemma restrictedChangeIso_natural (φ : R ⟶ S)
    {M N : SheafOfModules.{r} (𝓡 R)} (f : M ⟶ N) :
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit (𝓡 S))) ◁ f ≫ (restrictedChangeIso φ N).hom =
    (restrictedChangeIso φ M).hom ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
        (changeOfRingsHom φ M f) := by
  let α := (sheafCompose J (forget₂ CommRingCat RingCat)).map φ
  let B := (restrictScalars α).obj (unit (𝓡 S))
  let A := PresheafOfModules.sheafification (𝟙 (𝓡 R).obj)
  change B ◁ f ≫ (restrictedChangeIso φ N).hom =
    (restrictedChangeIso φ M).hom ≫ (restrictScalars α).map
      ((PresheafOfModules.sheafification (𝟙 (𝓡 S).obj)).map (changePresheafHom φ f))
  apply (cancel_epi (tensorObjIsoSheafification B M).inv).mp
  have ht := tensorComparison_naturality B f
  have hp := congrArg (fun g ↦ A.map g) (restrictedTensorPresheafIso_natural φ f)
  have hr := restrictionSheafificationComparison_natural α (changePresheafHom φ f)
  dsimp only [restrictedChangeIso, changeOfRings,
    Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc]
  erw [(tensorObjIsoSheafification B M).inv_hom_id_assoc]
  rw [← reassoc_of% ht]
  erw [(tensorObjIsoSheafification B N).inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, hp, Functor.map_comp, Category.assoc, hr]

/-- Restricted scalar extension is ordinary tensor with the restricted target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-pbc-restricted-change-tensor-independent).

Proof: the two presheaves have identical section tensors and restriction maps.
Sheafifying this identity over the source ring gives an isomorphism: restriction
commutes with sheafification, since the comparison becomes the identity after
forgetting to abelian sheaves. The tensor-sheafification comparison identifies
this with left tensor by the restricted target ring. Naturality follows from
naturality of all three comparisons. Transport along the supplied object and
map equalities, then use the braiding to put the fixed factor on the right.
No flatness is used, and zero rings and zero modules satisfy the same identities. -/
theorem nonempty_restrictedChangeTensorIso (φ : R ⟶ S)
    (E : SheafOfModules.{r} (𝓡 R) ⥤ SheafOfModules.{r} (𝓡 S))
    (hobj : ∀ M, E.obj M = changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm) :
    let := cochainModulesMonoidal R
    Nonempty (E ⋙ restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      tensorRight ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj (unit (𝓡 S)))) := by
  let := cochainModulesMonoidal R
  let := cochainModulesSymmetric R
  let U := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let B := U.obj (unit (𝓡 S))
  let e : tensorLeft B ≅ E ⋙ U := NatIso.ofComponents
    (fun M ↦ restrictedChangeIso φ M ≪≫ U.mapIso (eqToIso (hobj M)).symm) (by
      intro M N f
      dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, eqToIso.inv]
      rw [Functor.comp_map, hmap]
      simp only [Functor.map_comp, Category.assoc]
      rw [← U.map_comp_assoc, eqToHom_trans]
      simp only [eqToHom_refl]
      exact congrArg (fun g ↦ g ≫ U.map (eqToHom (hobj N).symm))
        (restrictedChangeIso_natural φ f))
  exact ⟨e.symm ≪≫ BraidedCategory.tensorLeftIsoTensorRight B⟩

end SheafOfModules
