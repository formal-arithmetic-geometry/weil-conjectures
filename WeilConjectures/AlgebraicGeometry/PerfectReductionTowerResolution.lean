/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.SystemEvaluationKFlat

/-! # Simultaneous flat K-flat resolutions for constant-coefficient towers

Source: Stacks Tags 06YS and 0G7E; Zheng, Construction 4.1.
(blueprint: lem-sp-constant-tower-kflat-resolution).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wA a b w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone

namespace CategoryTheory.PerfectReductionRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

private abbrev constantRings : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r} :=
  (Functor.const ℕᵒᵖ).obj R

private def constantRestrictionIso {m n : ℕ} (h : m ≤ n) (M : Modules R) :
    (systemRestriction (constantRings R) h).obj M ≅ M where
  hom := { val := {
    app := fun U ↦ ModuleCat.ofHom {
      toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    naturality := by intros; ext; rfl } }
  inv := { val := {
    app := fun U ↦ ModuleCat.ofHom {
      toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    naturality := by intros; ext; rfl } }
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

private def constantSystemToTowerObj (M : StrictRingSystem (constantRings R)) :
    ℕᵒᵖ ⥤ Modules R where
  obj n := M.level n.unop
  map {n m} f := M.transition (leOfHom f.unop) ≫
    (constantRestrictionIso R (leOfHom f.unop) (M.level m.unop)).hom
  map_id n := by
    ext U x
    exact M.identity n.unop U x
  map_comp f g := by
    ext U x
    exact M.compose (leOfHom g.unop) (leOfHom f.unop) U x

private def constantSystemToTower :
    StrictRingSystem (constantRings R) ⥤ (ℕᵒᵖ ⥤ Modules R) where
  obj := constantSystemToTowerObj R
  map f := {
    app := fun n ↦ f.app n.unop
    naturality := by
      intro n m h
      ext U x
      exact (congrArg (fun z ↦ z.val.app U x) (f.comm (leOfHom h.unop))).symm }
  map_id M := by rfl
  map_comp f g := by rfl

private def constantTowerToSystemObj (M : ℕᵒᵖ ⥤ Modules R) :
    StrictRingSystem (constantRings R) where
  level n := M.obj (op n)
  transition {m n} h := M.map (homOfLE h).op ≫
    (constantRestrictionIso R h (M.obj (op m))).inv
  identity n U x := by
    change (M.map (𝟙 (op n))).val.app U x = x
    rw [M.map_id]
    rfl
  compose h k U x := by
    change (M.map (homOfLE (h.trans k)).op).val.app U x =
      (M.map (homOfLE h).op).val.app U ((M.map (homOfLE k).op).val.app U x)
    have hm := M.map_comp (homOfLE k).op (homOfLE h).op
    exact congrArg (fun z ↦ z.val.app U x) hm

private def constantTowerToSystem :
    (ℕᵒᵖ ⥤ Modules R) ⥤ StrictRingSystem (constantRings R) where
  obj := constantTowerToSystemObj R
  map f := {
    app := fun n ↦ f.app (op n)
    comm := by
      intro m n h
      ext U x
      exact (congrArg (fun z ↦ z.val.app U x) (f.naturality (homOfLE h).op)).symm }
  map_id M := by rfl
  map_comp f g := by rfl

private def constantSystemsEquivalence :
    (ℕᵒᵖ ⥤ Modules R) ≌ StrictRingSystem (constantRings R) where
  functor := constantTowerToSystem R
  inverse := constantSystemToTower R
  unitIso := NatIso.ofComponents (fun M ↦
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro n m f
      ext U x
      rfl)) (by
        intro M N f
        ext n U x
        rfl)
  counitIso := NatIso.ofComponents (fun M ↦ {
    hom := { app := fun _ ↦ 𝟙 _
             comm := by intros; ext U x; rfl }
    inv := { app := fun _ ↦ 𝟙 _
             comm := by intros; ext U x; rfl }
    hom_inv_id := by
      apply strictRingSystem_hom_ext
      intro n
      change (𝟙 _) ≫ 𝟙 _ = 𝟙 _
      simp
    inv_hom_id := by
      apply strictRingSystem_hom_ext
      intro n
      change (𝟙 _) ≫ 𝟙 _ = 𝟙 _
      simp }) (by
      intro M N f
      apply strictRingSystem_hom_ext
      intro n
      change f.app n ≫ 𝟙 _ = 𝟙 _ ≫ f.app n
      simp)
  functor_unitIso_comp M := by
    apply strictRingSystem_hom_ext
    intro n
    rfl

private instance : (constantTowerToSystem R).Additive where
  map_add {M N} f g := by
    apply strictRingSystem_hom_ext
    intro n
    change (f + g).app (op n) =
      (systemEvaluation (constantRings R) n).map
        ((constantTowerToSystem R).map f + (constantTowerToSystem R).map g)
    rw [Functor.map_add]
    rfl

private instance : (constantSystemToTower R).Additive where
  map_add {M N} f g := by
    apply NatTrans.ext
    funext n
    simpa only [constantSystemToTower, NatTrans.app_add, systemEvaluation] using
      (systemEvaluation (constantRings R) n.unop).map_add (f := f) (g := g)

/-- One strict resolution works simultaneously at every constant-coefficient level.
Its terms are flat and its evaluated complexes are K-flat, while its augmentation
is a quasi-isomorphism of whole strict towers.

Source: Stacks Tags 06YS and 0G7E; Zheng, Construction 4.1
(blueprint: lem-sp-constant-tower-kflat-resolution).

Proof: Ordinary R-module towers are the strict semilinear systems for the constant
ring system R. The two functors leave all levels unchanged; their transitions only
insert or remove restriction along the identity, and are mutually inverse on sections.
Transport a tower to that category, apply its sequence-site flat-term K-flat resolution,
and transport the augmentation back using the equivalence unit. Exactness preserves
the quasi-isomorphism. Evaluation of the transported complex is the original system
evaluation, so its K-flatness and the flatness of every term hold simultaneously. -/
theorem constantTower_kFlatResolution
    (K : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :
    ∃ (L : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (f : L ⟶ K),
      (∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R)
        (L.asFunctor.obj (op n)) ∧
          ∀ i, IsFlatOnSite (R := R) ((L.asFunctor.obj (op n)).X i)) ∧ QuasiIso f := by
  let E := constantSystemsEquivalence R
  let e := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, q, hP, hq⟩ :=
    strictRingSystem_kFlatResolution (constantRings R) (e.functor.obj K)
  let L := e.inverse.obj P
  let f : L ⟶ K := e.inverse.map q ≫ e.unitIso.inv.app K
  have : QuasiIso q := hq
  have : QuasiIso (e.inverse.map q) := by
    change QuasiIso ((E.inverse.mapHomologicalComplex (.up ℤ)).map q)
    infer_instance
  refine ⟨L, f, ?_, ?_⟩
  · intro n
    exact hP n
  · dsimp only [f]
    infer_instance

end CategoryTheory.PerfectReductionRoos
