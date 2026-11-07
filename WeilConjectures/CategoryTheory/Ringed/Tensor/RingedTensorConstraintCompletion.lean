/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Completion of tensor constraints specified on K-flat pairs

Source: Stacks Project, Tag 0FPT
(blueprint: lem-sfb-ringed-tensor-constraint-completion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures SheafOfModules
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
private abbrev Mod := RingedTensorModules.{c, v, r} J R

private def pure (A B : Mod.{c, v, r} J R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) : (A ⊗ B).val.obj U :=
  (tensorObjIsoSheafification A B).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
      (A.val ⊗ B.val)).app U (x ⊗ₜ[R.obj.obj U] y))

private theorem pure_restrict (A B : Mod.{c, v, r} J R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.val.obj U) (y : B.val.obj U) :
    (A ⊗ B).val.map f (pure.{c, v, r} J R A B U x y) =
      pure.{c, v, r} J R A B V (A.val.map f x) (B.val.map f y) := by
  let η := ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
    (A.val ⊗ B.val)) ≫ (tensorObjIsoSheafification A B).inv.val
  exact (PresheafOfModules.naturality_apply η f (x ⊗ₜ[R.obj.obj U] y)).symm

private theorem pure_ext (A B N : Mod.{c, v, r} J R) {f g : A ⊗ B ⟶ N}
    (h : ∀ U x y, f.val.app U (pure.{c, v, r} J R A B U x y) =
      g.val.app U (pure.{c, v, r} J R A B U x y)) : f = g := by
  apply (cancel_epi (tensorObjIsoSheafification A B).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
  apply (adj.homEquiv (A.val ⊗ B.val) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private theorem pure_braiding (A B : Mod.{c, v, r} J R) (U : Cᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (β_ A B).hom.val.app U (pure.{c, v, r} J R A B U x y) = pure.{c, v, r} J R B A U y x := by
  exact CochainPullback.moduleTmul_braiding A B U x y

private theorem pure_map
    {M M' N N' : Mod.{c, v, r} J R} (f : M ⟶ M') (g : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (f ⊗ₘ g).val.app V (pure.{c, v, r} J R M N V x y) =
      pure.{c, v, r} J R M' N' V (f.val.app V x) (g.val.app V y) := by
  exact CochainPullback.moduleTmul_map f g V x y

private theorem pure_ext₃ (A B D N : Mod.{c, v, r} J R)
    {f g : (A ⊗ B) ⊗ D ⟶ N}
    (h : ∀ U x y z,
      f.val.app U (pure.{c, v, r} J R (A ⊗ B) D U (pure.{c, v, r} J R A B U x y) z) =
        g.val.app U (pure.{c, v, r} J R (A ⊗ B) D U (pure.{c, v, r} J R A B U x y) z)) : f = g := by
  apply (cancel_epi (β_ D (A ⊗ B)).hom).mp
  apply (SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N).injective
  change (SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N
      ((β_ D (A ⊗ B)).hom ≫ f)) = _
  refine pure_ext.{c, v, r} J R A B (SheafOfModules.homObjSmall_kfi (R := R) D N)
    (f := SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N ((β_ D (A ⊗ B)).hom ≫ f))
    (g := SheafOfModules.tensorHomEquiv_kfi (R := R) D (A ⊗ B) N ((β_ D (A ⊗ B)).hom ≫ g)) ?_
  intro U x y
  apply (PresheafOfModules.homEquivSmall_kfi.{max c v r, c, v} D.val N.val U).injective
  change PresheafOfModules.homEquivSmall_kfi.{max c v r, c, v} D.val N.val U
      ((PresheafOfModules.tensorHomCurry_kfi.{max c v r, c, v} _).app U
        (pure.{c, v, r} J R A B U x y)) =
    PresheafOfModules.homEquivSmall_kfi.{max c v r, c, v} D.val N.val U
      ((PresheafOfModules.tensorHomCurry_kfi.{max c v r, c, v} _).app U
        (pure.{c, v, r} J R A B U x y))
  rw [PresheafOfModules.tensorHomCurry_app_apply_kfi.{max c v r, c, v},
    PresheafOfModules.tensorHomCurry_app_apply_kfi.{max c v r, c, v}]
  apply PresheafOfModules.hom_ext
  intro W
  ext z
  change f.val.app (op W.unop.left)
      ((β_ D (A ⊗ B)).hom.val.app (op W.unop.left)
        (pure.{c, v, r} J R D (A ⊗ B) (op W.unop.left) z
          ((A ⊗ B).val.map W.unop.hom.op (pure.{c, v, r} J R A B U x y)))) =
    g.val.app (op W.unop.left)
      ((β_ D (A ⊗ B)).hom.val.app (op W.unop.left)
        (pure.{c, v, r} J R D (A ⊗ B) (op W.unop.left) z
          ((A ⊗ B).val.map W.unop.hom.op (pure.{c, v, r} J R A B U x y))))
  rw [pure_braiding, pure_restrict]
  exact h (op W.unop.left) _ _ z

private abbrev Complex := CochainComplex (Mod.{c, v, r} J R) ℤ

private theorem tensorGenerator_ext
    (P Q F : Complex.{c, v, r} J R)
    (φ ψ : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶ F)
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (φ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y) =
        (ψ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R P Q p q k hpq U x y)) :
    φ = ψ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := Q) (F := curriedTensor (Mod.{c, v, r} J R)) (c := .up ℤ)
  intro p q hpq
  apply pure_ext.{c, v, r} J R (P.X p) (Q.X q) (F.X k)
  intro U x y
  exact h p q k hpq U x y

private theorem tensorGenerator_ext₃
    (P Q N F : Complex.{c, v, r} J R)
    (φ ψ : (coefficientTotalTensor.{r, c, v} J R).obj
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ⟶ F)
    (h : ∀ (p q t i k : ℤ) (hpq : p + q = i) (hit : i + t = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X t).val.obj U),
      (φ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N i t k hit U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
      (ψ.f k).val.app U (coefficientTensorGenerator.{r, c, v} J R
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N i t k hit U
        (coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z)) : φ = ψ := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
    (K₁ := P) (K₂ := Q) (K₃ := N)
    (F₁₂ := curriedTensor (Mod.{c, v, r} J R))
    (G := curriedTensor (Mod.{c, v, r} J R)) (c₁₂ := .up ℤ) (c₄ := .up ℤ)
  intro p q t hpqt
  have hpqt' : (p + q) + t = k := hpqt
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor (Mod.{c, v, r} J R)) (curriedTensor (Mod.{c, v, r} J R))
    P Q N (.up ℤ) (.up ℤ) p q t (p + q) k rfl hpqt']
  apply pure_ext₃.{c, v, r} J R (P.X p) (Q.X q) (N.X t) (F.X k)
  intro U x y z
  have hm := pure_map.{c, v, r} J R
    (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q (p + q) rfl)
    (𝟙 (N.X t)) U (pure.{c, v, r} J R (P.X p) (Q.X q) U x y) z
  simp only [tensorHom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at hm
  have hh := h p q t (p + q) k rfl hpqt' U x y z
  let j := HomologicalComplex.ιMapBifunctor
    ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N
    (curriedTensor (Mod.{c, v, r} J R)) (.up ℤ) (p + q) t k hpqt'
  exact (congrArg (fun a ↦ (φ.f k).val.app U (j.val.app U a)) hm).trans
    (hh.trans (congrArg (fun a ↦ (ψ.f k).val.app U (j.val.app U a)) hm).symm)

end CategoryTheory
