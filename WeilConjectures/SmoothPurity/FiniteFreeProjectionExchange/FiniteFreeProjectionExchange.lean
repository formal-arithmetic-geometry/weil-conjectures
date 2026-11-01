/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFreeProjectionExchange.FiniteFreeProjectionExchangeDefinitions
import WeilConjectures.SmoothPurity.FiniteFreeProjectionExchange.FiniteFreeProjectionExchangeDefinitions

/-!
# Finite-free scalar extension of the specified projection and exchange maps

Source: blueprint main-20261015, sk-thm-purity-transport, proof Steps 1 and 3;
Stacks 07A4, 0E47, 0GL1, 03S6, 0F7I and 0GL6
(blueprint: lem-pur-finite-free-projection-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open WeilConjectures.FiniteFreeCoefficients
namespace WeilConjectures.FiniteFreeProjectionExchange

attribute [local irreducible] Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  Functor.mapDerivedCategory Etale.lowerStar Etale.upperStar
  Functor.leftAdjoint Functor.rightAdjoint
  ProEtale.pbcFixedScalarExtension ProEtale.lowerStar
  ProEtale.finiteCoefficientChangeDirectImageMap Etale.finiteCoefficientDirectImageMap
private theorem direct_naturality (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Sites.D pro A X} (r : M ⟶ N) :
    (Sites.scalar pro φ Y).map ((Sites.push pro A f).map r) ≫ Sites.direct pro φ f N =
      Sites.direct pro φ f M ≫
        (Sites.push pro B f).map ((Sites.scalar pro φ X).map r) := by
  cases pro <;> dsimp only [Sites.direct, Sites.scalar, Sites.push]
  · exact Etale.finiteCoefficientDirectImageMap_naturality φ f r
  · exact ProEtale.finiteCoefficientDirectImageMap_naturality
      (T := X) (X := Y) (K := M) (L := N) φ f r

private theorem comparison_naturality (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Sites.D pro A X} (r : M ⟶ N) :
    (Sites.scalar pro φ Y).map ((support pro A c).map r) ≫ comparison pro φ c N =
      comparison pro φ c M ≫
        (support pro B c).map ((Sites.scalar pro φ X).map r) := by
  dsimp only [comparison, support, Functor.comp_map]
  rw [← Category.assoc, direct_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun s ↦ Sites.direct pro φ c.g ((openExtension pro A c.i).obj M) ≫
    (Sites.push pro B c.g).map s) ((scalarOpen pro φ c.i).hom.naturality r)

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] Sites.scalar Sites.push Sites.direct Sites.tensor
  pull openExtension scalarPull scalarOpen comparison support tensorPullTarget

end WeilConjectures.FiniteFreeProjectionExchange
