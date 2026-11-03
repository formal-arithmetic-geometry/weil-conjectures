/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import Mathlib.FieldTheory.KrullTopology

import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule

/-! # Finite generic multiplication fibres and the Galois action -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry


private theorem field_fibre_orbit_continuous
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosed Ω] [Algebra.IsAlgebraic K Ω] [Algebra.IsSeparable K Ω] (X : (Spec (.of K)).Etale)
    (z : (Scheme.galoisPoint K Ω).fiber.obj X) :
    let : TopologicalSpace ((Scheme.galoisPoint K Ω).fiber.obj X) := ⊥
    Continuous (fun σ : Gal(Ω/K) ↦ (Scheme.galoisPointAct K Ω σ).app X z) := by
  let F := (Scheme.galoisPoint K Ω).fiber
  let act := Scheme.galoisPointAct K Ω
  let : TopologicalSpace (F.obj X) := ⊥
  have : DiscreteTopology (F.obj X) := ⟨rfl⟩
  let : MulAction Gal(Ω/K) (F.obj X) :=
    { smul σ z := (act σ).app X z
      one_smul z := GrothendieckTopology.Point.act_one_app _ _ _ _
      mul_smul σ τ z := GrothendieckTopology.Point.act_mul_app _ _ _ _ _ _ }
  have : ContinuousSMul Gal(Ω/K) (F.obj X) := by
    apply continuousSMul_iff_stabilizer_isOpen.mpr
    intro w
    obtain ⟨L, _, g, rfl⟩ := Scheme.exists_galoisPoint_fiber_map_eq X w
    apply Subgroup.isOpen_mono (fun σ hσ ↦ ?_) L.fixingSubgroup_isOpen
    exact Scheme.galoisPointAct_fiber_map_galoisPointFiberSpec g hσ
  exact continuous_id.smul continuous_const

/-- A point in a finite generic multiplication fibre has a continuous orbit
map for the discrete topology on the morphism set.

Pull back [n] to the generic field and lift x to that etale scheme.
Use the existing geometric fibre action galoisPointAct. Every point of an
etale scheme over a field factors through the canonical point of a finite
separable intermediate field. Its open Krull fixing subgroup fixes the point;
hence every stabilizer is open and the action on the discrete fibre is
continuous. Projecting its orbit through the pullback gives the orbit on
underlying scheme morphisms. Forgetting an Over morphism is injective; its
partial inverse is a map between discrete spaces, so composing with it
recovers precisely the displayed continuous orbit map over k.
Source: step 3 of the multiplication tower in the scope counterexample.
(blueprint: lem-sf-elliptic-division-orbit-continuous) -/
theorem ellipticDivisionOrbitContinuous
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (n : ℕ) [IsFinite (𝟙 E ^ n).left] [Etale (𝟙 E ^ n).left]
    (x : ((Over.map E.hom).obj
      ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E))
    (hx : x ≫ (𝟙 E ^ n) = Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl) :
    let : TopologicalSpace ((Over.map E.hom).obj
      ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E) := ⊥
    Continuous (fun σ : SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
      SeparableClosure E.left.functionField ↦
      (Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
        (Scheme.ProEt.genericPointSepAut E.left σ)) ≫ x) := by
  classical
  let K : Type u := E.left.functionField
  let Ω := SeparableClosure K
  let T := (Over.map E.hom).obj
    ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left))
  let f := (𝟙 E ^ n).left
  let b : Spec (.of K) ⟶ E.left := E.left.fromSpecStalk (genericPoint E.left)
  let g := Scheme.specAlgebraMap K Ω
  let q := pullback.snd f b
  let j := pullback.fst f b
  have : Etale q := inferInstance
  let X := Scheme.Etale.mk q
  have hx' : x.left ≫ f = g ≫ b := congrArg Over.Hom.left hx
  let z : (Scheme.galoisPoint K Ω).fiber.obj X := ULift.up
    (Over.homMk (pullback.lift x.left g hx') (by
      change pullback.lift x.left g hx' ≫ q = g
      simp [q]))
  let : TopologicalSpace ((Scheme.galoisPoint K Ω).fiber.obj X) := ⊥
  have : DiscreteTopology ((Scheme.galoisPoint K Ω).fiber.obj X) := ⟨rfl⟩
  let : TopologicalSpace (Spec (.of Ω) ⟶ E.left) := ⊥
  have : DiscreteTopology (Spec (.of Ω) ⟶ E.left) := ⟨rfl⟩
  let : TopologicalSpace (T ⟶ E) := ⊥
  have : DiscreteTopology (T ⟶ E) := ⟨rfl⟩
  have hc := field_fibre_orbit_continuous K Ω X z
  let v (w : (Scheme.galoisPoint K Ω).fiber.obj X) : Spec (.of Ω) ⟶ E.left :=
    w.down.left ≫ j
  have hcomp := (continuous_of_discreteTopology : Continuous v).comp hc
  change Continuous (fun σ : Gal(Ω/K) ↦
    (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ pullback.lift x.left g hx') ≫ j) at hcomp
  dsimp only [j] at hcomp
  simp only [Category.assoc, pullback.lift_fst] at hcomp
  let J : (T ⟶ E) → (Spec (.of Ω) ⟶ E.left) := fun y ↦ y.left
  have hJ : Function.Injective J := fun y w h ↦ Over.OverMorphism.ext h
  have hh : Continuous (fun σ : Gal(Ω/K) ↦ Function.invFun J
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left)) :=
    (continuous_of_discreteTopology : Continuous (Function.invFun J)).comp hcomp
  convert hh using 1
  funext σ
  exact (Function.leftInverse_invFun hJ _).symm

end AlgebraicGeometry
