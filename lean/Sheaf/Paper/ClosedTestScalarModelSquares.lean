/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.ClosedTestScalarModelDiagrams

/-! Scalar squares of the normalized section models.
Source: Stacks Tags 070Y, 0D6F and 09BL
(blueprint: lem-sfb-closed-test-scalar-model-squares). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
open ClosedTestKInjectiveSectionModels
open ClosedTestDerivedExchangeModel (restrict restrictPush scalarUnit adj pullComp)
variable {Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj S] [IsCommMonObj S]
  (c : Λ ⟶ S) [IsMonHom c]

/-- Paste the universal scalar comparisons with the closed-unit and model isomorphisms.
Source: Stacks Tags 070Y, 0D6F and 09BL
(blueprint: lem-sfb-closed-test-scalar-model-squares).
Proof: use the K-injective section-model theorem for N and for its scalar
restriction, which remains bounded below by exactness of restriction. Identify
sourceModel with eUnit.inv followed by eLeft.inv: its closed-unit section is
the inverse of the specified actual closed-unit inverse, and its remaining
factors are the direct-image section identity. Identify targetModel with
(eRight composed with eUnitRight).inv. These identifications and the existing
section-model isomorphisms give the first four IsIso clauses. Each
localizationModel is the composite of the evaluation computation-unit iso on
a K-injective complex, the derived localization iso, and the image of its
representative iso. These give the next four clauses, at source and pullback.

For the source scalar square, restriction preserves the underlying closed-unit
section map and therefore its inverse. Apply hs to that map and hc to the
pushforward computation units, then paste with the evaluation computation-unit
equations. This gives the source square with exactly sourceCoefficient.
The same computation for fZ and the exact pullback/scalar comparison gives
the target square. For the chain square, use the chain-mate formula identifying
the normalized exchange arrow with Q(j on the fibre composed with the section
unit). Paste the preceding two squares around the exchange square supplied by
hc; cancel only the normalized model isomorphisms. Finally the degreewise
localization identity commutes with restriction. Its derived computation-unit
normalization, combined with the same model computation, gives both remaining
localization squares. No scalar comparison is inverted. -/
theorem closed_test_scalar_model_squares (hc : UniversalCoherence c) (hs : SectionCoherence c)
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    (N : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (M : TestModel S h N.obj) (P : TestModel Λ h ((restrict c X).obj N.obj)) :
    ModelCoherence c A a f h fZ w V N.obj M P := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence
