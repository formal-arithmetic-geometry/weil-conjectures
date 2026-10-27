/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.SemilinearFieldOperationLifts

/-! # Agreement of the two normalized common-stage Frobenius squares

Source: purity/trace equivariance proof Step 1, canonical pullback compositors.
(blueprint: lem-pur-common-frobenius-square-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The Weil pullback square uses the same normalized composition components as
pullback/tensor coherence.
Source: purity/trace equivariance proof Step 1 and the pullback composition conventions.
(blueprint: lem-pur-common-frobenius-square-normalization).
Proof: both composition comparisons are the localization of
integralPullbackComposition, conjugated by the recorded pullback identifications.
At the literal finite stage of the argument, use the defining normalization of
zlPullComp and pullbackTensorCommonComposition to identify their hom components;
the integral comparison is literally the same chosen family in both definitions.
The common-stage scalar cocycles identify the three conjugating comparisons.
Thus the two composition components and their inverses agree. Apply this to the
two factorizations of the geometric Frobenius square. The middle eqToIso factors
agree by their scheme-map equality and proof irrelevance. Composition gives the
claimed isomorphism equality. No smoothness, Tate line or purity map is involved. -/
theorem commonFrobeniusSquare_eq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    (zlFrobeniusSquare D l hl Ω f₀).app K =
      podCommonSquarePullbackComponent l Ω (zlFiberMap D f₀)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K := by
  sorry

end WeilConjectures
