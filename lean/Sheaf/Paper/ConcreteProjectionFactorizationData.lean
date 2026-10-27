/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ConcreteProjectionReductionData
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! # Proper and open factors of the concrete coefficient square

Source: Stacks Tags 0B56, 0E48, 0GL1 and 0GL6
(blueprint: def-sf-concrete-projection-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConcreteProjectionReduction
open AlgebraicGeometry.ProEtale.OpenScalarTensor
variable (m : Models.{u})

/-- Exact open extension in the specified ringed presentation.
Source: Stacks 03DI (blueprint: def-sf-concrete-projection-factors). -/
abbrev openImage (A : Type u) [CommRing A] {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] := (PurCompactSupport.openExtension (coefficients A) j).mapDerivedCategory

/-- Separately derived direct image in constant-ring coordinates.
Source: Stacks 07A5 (blueprint: def-sf-concrete-projection-factors). -/
abbrev properImage (A : Type u) [CommRing A] {Z Y : Scheme.{u}} (g : Z ⟶ Y) :=
  PurCompactSupport.push (coefficients A) g

/-- The normalized scalar-adjunction mate for proper direct image.
Source: Stacks 0B56, 0E48 (blueprint: def-sf-concrete-projection-factors). -/
def properScalar {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    properImage A g ⋙ scalar m φ Y ⟶ scalar m φ Z ⋙ properImage B g :=
  Functor.whiskerLeft (properImage A g) (scalarIso m φ Y).hom ≫
    PurCompactSupport.properComparison (coefficientChange φ) g ≫
    Functor.whiskerRight (scalarIso m φ Z).inv (properImage B g)

/-- The normalized open scalar mate.
Source: Stacks 0GL1 (blueprint: def-sf-concrete-projection-factors). -/
def openScalar {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    openImage A j ⋙ scalar m φ Z ⟶ scalar m φ X ⋙ openImage B j :=
  Functor.whiskerLeft (openImage A j) (scalarIso m φ Z).hom ≫
    PurCompactSupport.openComparison (coefficientChange φ) j ≫
    Functor.whiskerRight (scalarIso m φ X).inv (openImage B j)

/-- The counit-defined proper projection. No invertibility is assumed.
Source: Stacks 0B56 (blueprint: def-sf-concrete-projection-factors). -/
def properProjection (A : Type u) [CommRing A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : proEtaleDerivedCategory Z A) (L : proEtaleDerivedCategory Y A) :
    (tensor m A Y).obj ((properImage A g).obj M, L) ⟶
      (properImage A g).obj (input m A g M L) :=
  (proEtaleRingDerivedAdjunction g (proEtaleConstantRing Y A)
    (proEtaleConstantRing Z A) (proEtaleConstantRingComparison g A)).homEquiv _ _
    ((restrictionTensor m A g).hom.app ((properImage A g).obj M, L) ≫
      (tensor m A Z).map (Prod.mkHom
        ((proEtaleRingDerivedAdjunction g (proEtaleConstantRing Y A)
          (proEtaleConstantRing Z A) (proEtaleConstantRingComparison g A)).counit.app M)
        (𝟙 _)))

/-- The open tensor map, including the actual compactification pullback compositor.
Source: Stacks 0GL1 (blueprint: def-sf-concrete-projection-factors). -/
def openFactor (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : proEtaleDerivedCategory X A)
    (L : proEtaleDerivedCategory Y A) :
    input m A c.g ((openImage A c.i).obj K) L ≅
      (openImage A c.i).obj (input m A f K L) :=
  PurCompactSupport.projectionOpenFactor (coefficients A) c
    (tensorModel m A X) (tensorModel m A c.Z)
    (proEtaleConstantRingCompositeCoefficients_eq c.i c.g A).symm K L

end WeilConjectures.ConcreteProjectionReduction
