/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.RingTheory.FiniteTypeApproximationFlatLoci
import WeilConjectures.RingTheory.FiniteTypeApproximationFlatStage
import WeilConjectures.RingTheory.LimitModuleFinitePresentation

/-! # A flat model of a scalar extension of a finitely presented module

If the scalar extension of a finitely presented module along `A → C ⊗[R] A` is flat, it is the
base change of a flat finitely presented module over a finitely presented algebra over a
finitely presented `ℤ`-algebra.

## Implementation details

The algebra and module are approximated by finitely presented models over finitely generated
integer algebras. The flat loci of the models are open and persist under base change and
localization; quasi-compactness gives a stage whose flat locus pulls back to everything, and
lifting a unit-ideal relation gives a later stage that is flat everywhere.

## References

* [Stacks, Tag 02JO] (1), with the tensor identifications in (3)
* [Stacks, Tag 00R1]
* [Stacks, Tag 00R6]
* [Stacks, Tag 00RC]
-/

@[expose] public section

universe v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A flat scalar extension has a flat model over a finitely presented integer algebra: if
`(C ⊗[R] A) ⊗[A] M` is flat over `C ⊗[R] A`, there are a finitely presented `ℤ`-algebra `P`, a
finitely presented `P`-algebra `Q` and a flat finitely presented `Q`-module `L` that recover
`C ⊗[R] B` and its module `(C ⊗[R] B) ⊗[B] M` by base change. -/
theorem exists_flat_module_tensor_model
    {R C : Type v} {A B M : Type w}
    [CommRing R] [CommRing C] [CommRing A] [CommRing B] [AddCommMonoid M]
    [Algebra R C] [Algebra R A] [Algebra R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]
    [Module B M] [Module.FinitePresentation B M] (f : A →ₐ[R] B)
    (hflat : letI : Module A M := Module.compHom M f.toRingHom
      letI : Algebra A (C ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      Module.Flat (C ⊗[R] A) ((C ⊗[R] A) ⊗[A] M)) :
    ∃ (P Q L : Type (max v w)) (_ : CommRing P) (_ : CommRing Q)
      (_ : Algebra P Q) (_ : AddCommMonoid L) (_ : Module Q L)
      (_ : Algebra P (C ⊗[R] A)),
      Algebra.FinitePresentation ℤ P ∧ Algebra.FinitePresentation P Q ∧
      Module.FinitePresentation Q L ∧
      (letI : Module P L := Module.compHom L (algebraMap P Q); Module.Flat P L) ∧
      ∃ e : (C ⊗[R] A) ⊗[P] Q ≃+* C ⊗[R] B,
        e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
          (Algebra.TensorProduct.map (Algebra.ofId C C) f).toRingHom ∧
        (letI : Algebra Q (C ⊗[R] B) :=
          (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
         letI : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
         Nonempty ((C ⊗[R] B) ⊗[Q] L ≃ₗ[C ⊗[R] B] (C ⊗[R] B) ⊗[B] M)) := by
  classical
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let : Module A M := Module.compHom M f.toRingHom
  let : Algebra A (C ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup B
  let X := C ⊗[R] A
  let Y := C ⊗[R] B
  let g : X →+* Y := (Algebra.TensorProduct.map (Algebra.ofId C C) f).toRingHom
  let : Algebra X Y := g.toAlgebra
  let e₀ := Algebra.IsPushout.cancelBaseChangeAlg R C A X B
  have he₀ : ∀ (c : C) (a : A) (b : B),
      e₀ ((c ⊗ₜ[R] a) ⊗ₜ[A] b) = c ⊗ₜ[R] (f a * b) := by
    intro c a b
    apply e₀.symm.injective
    simp only [AlgEquiv.symm_apply_apply, e₀,
      Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul]
    change (c ⊗ₜ[R] a) ⊗ₜ[A] b = (c ⊗ₜ[R] (1 : A)) ⊗ₜ[A] (a • b)
    rw [← TensorProduct.smul_tmul]
    congr 1
    change c ⊗ₜ[R] a = ((1 : C) ⊗ₜ[R] a) * (c ⊗ₜ[R] (1 : A))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have heLeft : ∀ x : X, e₀ (x ⊗ₜ[A] (1 : B)) = g x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]
    | tmul c a =>
      rw [he₀, mul_one]
      change c ⊗ₜ[R] f a = Algebra.TensorProduct.map (Algebra.ofId C C) f (c ⊗ₜ[R] a)
      rw [Algebra.TensorProduct.map_tmul]
      rfl
  let eX : X ⊗[A] B ≃ₐ[X] Y :=
    { e₀.toRingEquiv with
      commutes' := heLeft }
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  have : Algebra.FinitePresentation X Y := Algebra.FinitePresentation.equiv eX
  let : Algebra A Y := ((algebraMap B Y).comp f.toRingHom).toAlgebra
  have : IsScalarTower A X Y := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change g ((1 : C) ⊗ₜ[R] a) = (1 : C) ⊗ₜ[R] f a
    exact Algebra.TensorProduct.map_tmul (Algebra.ofId C C) f 1 a)
  have : IsScalarTower A B Y := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsPushout A X B Y := by
    constructor
    apply IsBaseChange.of_equiv eX.toLinearEquiv
    intro b
    change e₀ (((1 : C) ⊗ₜ[R] (1 : A)) ⊗ₜ[A] b) = (1 : C) ⊗ₜ[R] b
    simp only [he₀, map_one, one_mul]
  have : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  let : Module X (Y ⊗[B] M) := Module.compHom (Y ⊗[B] M) (algebraMap X Y)
  have : IsScalarTower X Y (Y ⊗[B] M) := IsScalarTower.of_compHom X Y _
  have hTflat : Module.Flat X (Y ⊗[B] M) := by
    exact (Module.Flat.equiv_iff
      (Algebra.IsPushout.cancelBaseChange A X B Y M)).mpr hflat
  obtain ⟨Λ, hpo, hne, hdir, P, Q, η, π, κ, D, ν, hmod, hmodel⟩ :=
    Algebra.limitModuleFinitePresentation X Y (Y ⊗[B] M)
  let := hpo
  let := hne
  let := hdir
  let := hmod
  rcases hmodel with ⟨hPcol, hQcol, hDcol, hcomm, hscalar, hν, hPft, hQft,
    hDfin, htransQ, htransD, hfinalQ, hfinalD, _⟩
  obtain ⟨U, hUopen, hUflat, hUpersist, hUcover⟩ :=
    Algebra.exists_flat_finiteType_approximation_loci
      X Y (Y ⊗[B] M) P Q η π κ D ν
      ⟨hPcol, hQcol, hDcol, hcomm, hscalar, hν, hPft, hQft, hDfin,
        htransQ, htransD, hfinalQ, hfinalD⟩ hTflat
  obtain ⟨i, hflatStage⟩ := Algebra.exists_flat_finiteType_approximation_stage
    Y P Q D (fun i ↦ (η.app i).hom) κ hQcol.some U hUopen hUflat hUpersist hUcover
  let : Algebra (P.obj i) (Q.obj i) := (η.app i).hom.toAlgebra
  let : Algebra (P.obj i) X := (π.app i).hom.toAlgebra
  have : Algebra.FiniteType ℤ (P.obj i) := hPft i
  have : Algebra.FiniteType (P.obj i) (Q.obj i) := hQft i
  have : IsNoetherianRing (P.obj i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsNoetherianRing (Q.obj i) := Algebra.FiniteType.isNoetherianRing (P.obj i) _
  have : Module.Finite (Q.obj i) (D.obj i) := hDfin i
  have hPfp : Algebra.FinitePresentation ℤ (P.obj i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hQfp : Algebra.FinitePresentation (P.obj i) (Q.obj i) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hDfp : Module.FinitePresentation (Q.obj i) (D.obj i) :=
    Module.finitePresentation_of_finite (Q.obj i) (D.obj i)
  obtain ⟨er, her⟩ := hfinalQ i
  let e := (Algebra.TensorProduct.comm (P.obj i) X (Q.obj i)).toRingEquiv.trans er
  have heLeft : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = g := by
    apply RingHom.ext
    intro x
    change er ((1 : Q.obj i) ⊗ₜ[P.obj i] x) = g x
    rw [her, map_one, one_mul]
    rfl
  refine ⟨P.obj i, Q.obj i, D.obj i, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hPfp, hQfp, hDfp, hflatStage,
    e, heLeft, ?_⟩
  have heRight : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      (κ.app i).hom := by
    ext q
    change er (q ⊗ₜ[P.obj i] (1 : X)) = (κ.app i).hom q
    rw [her, map_one, mul_one]
    rfl
  rw [heRight]
  exact ⟨(hfinalD i).choose⟩

end AlgebraicGeometry
