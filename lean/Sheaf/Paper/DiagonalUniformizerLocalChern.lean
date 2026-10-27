/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.DiagonalUniformizerAdjunctConditions

/-! # Reduction of a local completed Chern class

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]


namespace UniformizerChernNormalizationData

/-- The completed local Chern class has the positive finite Kummer normalization.

Source: latest blueprint, diagonal tower coefficient changes proof (1), applying
coefficient extension to the section class; trace proof (1), Kummer construction.
(blueprint: lem-diagonal-uniformizer-local-chern).

Proof: represent the line-bundle extension of O(1) by one K-flat complex. The
normalization hz identifies z, after restriction to constant scalars, with the
limit of the simultaneous Kummer reduction of that complex. The coefficient
cone projections send one to one, and the root cone projections are the actual
power-compatible root projections. Derived reduction of the regular completed
unit modulo l^(n+1) is its ordinary quotient, since l is regular. Tensoring the
same complex further with O_E/(pi^(n+1)) is therefore the direct coefficient
reduction, by hA and associativity of derived extension. The two Endpoint
normalizations identify its unit and line maps with the two displayed scalar
comparisons, including the nonflat quotient comparison. CompletedRealization's
underlying and projection equations identify the first realization; finite
realization's coefficient-one equation identifies the last unit. The integral
root projections in lineP and its finite kernel inclusion identify the last
line map with the positive finite root-to-tensor map. Naturality of the Kummer
connecting morphism consequently gives exactly the finite Kummer class of O(1).
The finite Chern specification determines that module-derived arrow by its
integral adjunct. This argument is entirely on P: there is no direct image,
completed Chern adjunct c, trace, or degree calculation. Exponent n+1 is positive
at n=0; no equality of arbitrary arrows is deduced from levelwise equality. -/
theorem localChern
    (s : UniformizerChernNormalizationData l Y)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧)
    (hz : s.LocalNormalized l Y
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
        (SpTowerClasses.hyperplanePic Y)) z) : s.LocalChernNormalized l Y z := by sorry

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
