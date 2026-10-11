/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The fibre of a free sheaf at a point

Let `Φ` be a point of a site `(C, J)`, `X : C` and `R` a commutative ring. The free presheaf
`R[X] = Presheaf.freeYoneda X R`, sending `U` to the free `R`-module on `U ⟶ X`, has fibre at
`Φ` the free `R`-module on the fibre `Φ.fiber.obj X`; the same holds for the free sheaf
`Sheaf.freeYoneda J X R`, whose fibre is that of its presheaf. The basis element attached to
`x : Φ.fiber.obj X` is the germ at `(X, x)` of the generator, the image of `𝟙 X`.

## Main definitions

- `CategoryTheory.GrothendieckTopology.Point.presheafFiberFreeYonedaIso`
- `CategoryTheory.GrothendieckTopology.Point.sheafFiberFreeYonedaEquiv`
-/

@[expose] public section

universe w w' v u

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  (R : Type w') [CommRing R] [HasColimitsOfSize.{w, w} (ModuleCat.{w'} R)]
  [HasCoproducts.{v} (ModuleCat.{w'} R)]

/-- The generator of the free presheaf `R[X]` over `X`: the basis element attached to `𝟙 X`. -/
noncomputable def freeYonedaGen (X : C) :
    (Presheaf.freeYoneda X (ModuleCat.of R R)).obj (op X) :=
  (Sigma.ι (fun _ : (yoneda.obj X).obj (op X) ↦ ModuleCat.of R R) (𝟙 X)).hom (1 : R)

lemma freeYoneda_ι_apply (X U : C) (f : U ⟶ X) (r : R) :
    (Sigma.ι (fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R) f).hom r =
      r • (Presheaf.freeYoneda X (ModuleCat.of R R)).map f.op (freeYonedaGen R X) := by
  have h := congrArg (fun k ↦ k.hom r) (Sigma.ι_comp_map'
    (f := fun _ : (yoneda.obj X).obj (op X) ↦ ModuleCat.of R R)
    (g := fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R)
    ((yoneda.obj X).map f.op) (fun _ ↦ 𝟙 _) (𝟙 X))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_id,
    LinearMap.id_coe, id_eq] at h
  rw [freeYonedaGen, ← map_smul, smul_eq_mul, mul_one]
  simpa using h.symm

/-- The map from the fibre of the free presheaf `R[X]` to the free module on `Φ.fiber.obj X`,
sending the germ at `(U, u)` of the basis element `f : U ⟶ X` to the basis element
`Φ.fiber.map f u`. -/
noncomputable def presheafFiberFreeYonedaDesc (X : C) :
    Φ.presheafFiber.obj (Presheaf.freeYoneda X (ModuleCat.of R R)) ⟶
      ModuleCat.of R (Φ.fiber.obj X →₀ R) :=
  Φ.presheafFiberDesc (P := Presheaf.freeYoneda X (ModuleCat.of R R))
    (fun U u ↦ Sigma.desc fun f ↦ ModuleCat.ofHom (Finsupp.lsingle (Φ.fiber.map f u)))
    (fun U U' g u ↦ by
      refine Sigma.hom_ext _ _ fun f ↦ ?_
      simp [Presheaf.freeYoneda_map])

lemma presheafFiberFreeYonedaDesc_toPresheafFiber (X U : C) (u : Φ.fiber.obj U)
    (f : U ⟶ X) (r : R) :
    (Φ.presheafFiberFreeYonedaDesc R X).hom (Φ.toPresheafFiber U u _
      ((Sigma.ι (fun _ : (yoneda.obj X).obj (op U) ↦ ModuleCat.of R R) f).hom r)) =
      Finsupp.single (Φ.fiber.map f u) r := by
  have h := Φ.toPresheafFiber_presheafFiberDesc (P := Presheaf.freeYoneda X (ModuleCat.of R R))
    (fun U u ↦ Sigma.desc fun f ↦ ModuleCat.ofHom (Finsupp.lsingle (Φ.fiber.map f u)))
    (fun U U' g u ↦ by
      refine Sigma.hom_ext _ _ fun f ↦ ?_
      simp [Presheaf.freeYoneda_map]) U u
  have h' := congrArg (fun k ↦ (Sigma.ι (fun _ : (yoneda.obj X).obj (op U) ↦
    ModuleCat.of R R) f ≫ k).hom r) h
  simpa [presheafFiberFreeYonedaDesc] using h'

/-- The map from the free module on `Φ.fiber.obj X` to the fibre of the free presheaf `R[X]`,
sending `x` to the germ at `(X, x)` of the generator. -/
noncomputable def presheafFiberFreeYonedaLift (X : C) :
    ModuleCat.of R (Φ.fiber.obj X →₀ R) ⟶
      Φ.presheafFiber.obj (Presheaf.freeYoneda X (ModuleCat.of R R)) :=
  ModuleCat.ofHom (Finsupp.linearCombination R fun x ↦
    Φ.toPresheafFiber X x _ (freeYonedaGen R X))

/-- The fibre of the free presheaf `R[X]` at a point `Φ` is the free `R`-module on the fibre
`Φ.fiber.obj X`. -/
noncomputable def presheafFiberFreeYonedaIso (X : C) :
    Φ.presheafFiber.obj (Presheaf.freeYoneda X (ModuleCat.of R R)) ≅
      ModuleCat.of R (Φ.fiber.obj X →₀ R) where
  hom := Φ.presheafFiberFreeYonedaDesc R X
  inv := Φ.presheafFiberFreeYonedaLift R X
  hom_inv_id := by
    refine Φ.presheafFiber_hom_ext fun U u ↦ Sigma.hom_ext _ _ fun f ↦ ?_
    ext
    have := Φ.presheafFiberFreeYonedaDesc_toPresheafFiber R X U u f 1
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      Category.comp_id] at this ⊢
    rw [this]
    simp only [presheafFiberFreeYonedaLift, ModuleCat.hom_ofHom,
      Finsupp.linearCombination_single, one_smul, freeYoneda_ι_apply,
      toPresheafFiber_w_apply]
  inv_hom_id := by
    ext x : 2
    refine Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring ?_
    have := Φ.presheafFiberFreeYonedaDesc_toPresheafFiber R X X x (𝟙 X) 1
    simp only [presheafFiberFreeYonedaLift, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, one_smul, ModuleCat.hom_id, LinearMap.id_comp]
    rw [freeYonedaGen, this, CategoryTheory.Functor.map_id]
    rfl

lemma presheafFiberFreeYonedaIso_inv_single (X : C) (x : Φ.fiber.obj X) :
    (Φ.presheafFiberFreeYonedaIso R X).inv.hom (Finsupp.single x 1) =
      Φ.toPresheafFiber X x _ (freeYonedaGen R X) := by
  simp [presheafFiberFreeYonedaIso, presheafFiberFreeYonedaLift]

variable [HasWeakSheafify J (ModuleCat.{w'} R)]

/-- The generator of the free sheaf `R[X]` over `X`: the image of `𝟙 X`. -/
noncomputable def sheafFreeYonedaGen (X : C) :
    (Sheaf.freeYoneda J X (ModuleCat.of R R)).obj.obj (op X) :=
  (toSheafify J (Presheaf.freeYoneda X (ModuleCat.of R R))).app (op X) (freeYonedaGen R X)

/-- The fibre of the free sheaf `R[X]` at a point `Φ` is the free `R`-module on the fibre
`Φ.fiber.obj X`, the basis element `x` being the germ at `(X, x)` of the generator. -/
noncomputable def sheafFiberFreeYonedaEquiv (X : C) :
    (Φ.fiber.obj X →₀ R) ≃ₗ[R] Φ.sheafFiber.obj (Sheaf.freeYoneda J X (ModuleCat.of R R)) :=
  ((Φ.presheafFiberFreeYonedaIso R X).symm ≪≫
    ((Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{w'} R)).app
      (Presheaf.freeYoneda X (ModuleCat.of R R))).symm).toLinearEquiv

lemma sheafFiberFreeYonedaEquiv_single (X : C) (x : Φ.fiber.obj X) :
    Φ.sheafFiberFreeYonedaEquiv R X (Finsupp.single x 1) =
      Φ.toPresheafFiber X x _ (sheafFreeYonedaGen R X) := by
  simp only [sheafFiberFreeYonedaEquiv, Iso.toLinearEquiv_apply, Iso.trans_hom, Iso.symm_hom,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    presheafFiberFreeYonedaIso_inv_single, Iso.app_inv, sheafFreeYonedaGen]
  simp [presheafToSheafCompSheafFiberIso]

end CategoryTheory.GrothendieckTopology.Point
