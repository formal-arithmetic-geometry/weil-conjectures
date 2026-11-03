/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection

/-!
# Projection formula for a constant Weil twist

Source: latest blueprint, `lem-wf-constant-twist-cohomology`, entire statement
and projection-formula proof (blueprint: lem-wf-constant-twist-cohomology).

The helpers only spell out the chosen compactification, the degree-zero line,
and the canonical Frobenius maps. The theorem uses strict pairs in the ordinary
module derived category, with the tensor Frobenius of `def-wf-tensor-product`.
The Frobenius structures on compact support are existentially packaged with
an equality fixing their homomorphisms to the canonical exchange composites;
no arbitrary Weil structures are allowed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Base change of a model compactification. Source: geometric base change and
compact-support operation (blueprint: lem-wf-constant-twist-cohomology). -/
def constantTwistGeometricCompactification
    (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (h₀ : X₀ ⟶ Y₀) (c₀ : Compactification h₀.left) :
    Compactification (D.geometricFiberMap h₀) where
  Z := (D.geometricFiber (nativeWeilCompactificationModel D h₀ c₀)).left
  g := D.geometricFiberMap (nativeWeilCompactificationProper D h₀ c₀)
  i := D.geometricFiberMap (nativeWeilCompactificationOpen D h₀ c₀)
  comm := by
    let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    have w : h₀ = nativeWeilCompactificationOpen D h₀ c₀ ≫
        nativeWeilCompactificationProper D h₀ c₀ := by
      apply Over.OverMorphism.ext
      exact c₀.comm
    change (F.map h₀).left = (F.map _).left ≫ (F.map _).left
    exact (congrArg (fun h ↦ (F.map h).left) w).trans
      (congrArg (fun h : F.obj X₀ ⟶ F.obj Y₀ ↦ h.left)
        (F.map_comp (nativeWeilCompactificationOpen D h₀ c₀)
          (nativeWeilCompactificationProper D h₀ c₀)))
  isProper := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (nativeWeilCompactificationProper D h₀ c₀) inferInstance
  isOpenImmersion := nativeWeilGeometricOpen D (nativeWeilCompactificationOpen D h₀ c₀)

/-- Pullback of a strict pair along a commuting Frobenius square, using the canonical
pullback compositor and the exact/left-derived comparison.
Source: h^* B_b and its Weil structure (blueprint: lem-wf-constant-twist-cohomology). -/
def constantTwistPullbackPair
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {gX : X ⟶ X} {gY : Y ⟶ Y} [IsIso gX] [IsIso gY]
    (sq : CommSq gX f f gY) (B : wfCondensedWeilPair Λ.X gY) :
    wfCondensedWeilPair Λ.X gX :=
  IsoAlgebra.mk ((CondensedRing.moduleObjectDerivedPullback Λ.X f).obj B.carrier)
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X gX).symm.app _ ≪≫
      (CondensedRing.moduleObjectDerivedPullbackSquareComparison Λ.X sq).symm.app B.carrier ≪≫
      (CondensedRing.moduleObjectDerivedPullback Λ.X f).mapIso
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X gY).app B.carrier ≪≫
          B.str))

end WeilConjectures
