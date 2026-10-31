/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint

/-! # Normalized endpoints for ordinary etale derived coefficient extension

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts; Stacks Project, Tags 03EK, 03PK and 06YY
(blueprint: def-sp-p1-kummer-scalar-endpoints).

The record specifies the canonical unit and finite Tate-line identifications through
ordinary coefficient insertion and the actual derived scalar adjunction. It asserts
no existence theorem. Chern images and shifted identifications are actual composites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Derive a specified coefficient insertion by the actual extension/restriction adjunction.
This is the single-degree-zero comparison, with its ordinary map as input.
Source: Stacks 06YY (blueprint: def-sp-p1-kummer-scalar-endpoints). -/
def p1KummerDerivedInsertion {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) :
    (scalarExtension φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj G :=
  SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology φ η

/-- The endpoints of the scalar comparison, fixed on generators and by derived adjunction.
The two isomorphisms are constrained derived maps, rather than arbitrary identifications.
Source: Stacks 03EK, 03PK, 06YY; blueprint Charts, balanced endpoint formulas
(blueprint: def-sp-p1-kummer-scalar-endpoints). -/
structure P1KummerScalarEndpoints {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) where
  /-- Insertion of the coefficient image in the constant sheaf. -/
  unitInsertion : ordinaryFiniteConstant A T ⟶
    (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant B T)
  /-- Insertion in the roots tensor line. -/
  lineInsertion : Scheme.finiteEtaleTateLine T N A hA ⟶
    (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (Scheme.finiteEtaleTateLine T N B hB)
  /-- Constants send a to phi(a); the adjoint is multiplication. -/
  unit_normalization : ∀ (W : T.Etaleᵒᵖ) (a : A),
    unitInsertion.hom.app W
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app W (φ a)
  /-- The balanced root map sends a tensor z to phi(a) tensor z. -/
  line_normalization : ∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf N).obj.obj W),
    lineInsertion.hom.app W (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z
  /-- Derived multiplication on the unit. -/
  unitIso : (scalarExtension φ T).obj (ordinaryFiniteUnit A T) ≅ ordinaryFiniteUnit B T
  /-- Derived balancing on the Tate line. -/
  lineIso : (scalarExtension φ T).obj (ordinaryFiniteLine A N hA T) ≅
    ordinaryFiniteLine B N hB T
  /-- The unit is the derived ordinary insertion. -/
  unit_derived : unitIso.hom = p1KummerDerivedInsertion φ T unitInsertion
  /-- The line is the derived ordinary insertion. -/
  line_derived : lineIso.hom = p1KummerDerivedInsertion φ T lineInsertion

/-- Shift the normalized line comparison using the canonical adjoint shift comparison.
Source: Stacks 0D6D, shifted K-flat representatives
(blueprint: def-sp-p1-kummer-scalar-endpoints). -/
def P1KummerScalarEndpoints.shiftedLineIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {T : Scheme.{u}} (e : P1KummerScalarEndpoints φ N hA hB T) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  (Adjunction.LeftAdjointCommShift.iso
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)) (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso e.lineIso

/-- Transport one fixed derived Chern arrow by its canonical unit and Tate identifications.
Source: blueprint Charts, scalar images of the same residue-coefficient class
(blueprint: def-sp-p1-kummer-scalar-endpoints). -/
def P1KummerScalarEndpoints.chernImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {T : Scheme.{u}} (e : P1KummerScalarEndpoints φ N hA hB T)
    (c : ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) :
    ordinaryFiniteUnit B T ⟶ (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  e.unitIso.inv ≫ (scalarExtension φ T).map c ≫ e.shiftedLineIso.hom

/-- The residue ring, lifted to the coefficient universe of the ordinary etale categories.
Source: blueprint Charts, the common residue coefficients
(blueprint: def-sp-p1-kummer-scalar-endpoints). -/
abbrev p1KummerResidue (N : ℕ) := ULift.{u + 1} (ZMod N)

/-- The unique unital coefficient map from the lifted residue ring.
Source: blueprint Charts, common residue coefficients
(blueprint: def-sp-p1-kummer-scalar-endpoints). -/
def p1KummerResidueMap (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    p1KummerResidue.{u} N →+* A :=
  (Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom

end AlgebraicGeometry.Etale
