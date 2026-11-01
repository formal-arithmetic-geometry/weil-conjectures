/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceNormalization

/-! # Semilinear compatibility of the canonical source reductions

Source: blueprint smooth-purity transport, adic stage; source-object argument, Steps 3--6.
(blueprint: lem-pur-adic-source-transition-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [hYsep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The specified source reduction intertwines the actual semilinear quotient maps.
Source: blueprint smooth-purity transport, adic stage; the source-object proof, Steps 3--6
(blueprint: lem-pur-adic-source-transition-square).

Proof: the integral pullback comparison is the evaluation of the reduction/limit
counit, transported through its prescribed Roos model. Counit naturality gives its
square for every direct quotient. Compute tensor by the integral rank-one line on a
flat-term K-flat representative. The normalized line reduction square sends each
local tensor (x tensor u) tensor v to x tensor q(u)v in either order. The prescribed
root quotients commute with direct quotient maps, including exponent one. Transpose
this equality under the scalar extension/restriction adjunction; its bijectivity
identifies the result with the defined adicPurityTwistReduction, rather than an
unspecified isomorphism. Shift the square termwise and paste with the canonical
finite-source identification. Its root-normalized finite comparison is precisely
purAdicFiniteSourceNormalization. Transposing the pasted square gives the displayed
semilinear equality. Equal indices, d = 0, the zero complex and the empty scheme use
the same unit and tensor formulas. No cocycle law is assumed in this argument. -/
theorem purAdicSourceReduction_transition_square
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    purAdicSourceReduction D C E f d K hK m ≫
        purAdicFiniteSourceTransition D C E f d K hK h =
      normalizedDVRReductionTransition C.l E X D C.different h
          (purAdicSource D C E f d K) ≫
        (normalizedDVRRes C.l E X h).map (purAdicSourceReduction D C E f d K hK n) := by
  sorry

end WeilConjectures
