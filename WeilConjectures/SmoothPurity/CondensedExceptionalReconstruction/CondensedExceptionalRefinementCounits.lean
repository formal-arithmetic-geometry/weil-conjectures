/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.CondensedExceptionalReconstructionData

/-! # CondensedExceptionalRefinementCounits

Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-refinement-counits). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel

/-- Refinement preserves the actual system counit and its scalar-extended transpose.
Source: blueprint sk-prop-sp-unique-adjoint-categorical, Transposes, Naturality and
Uniqueness; parent reconstruction proof Step 6.
(blueprint: lem-pur-condensed-exceptional-refinement-counits).

Proof: express each supplied system using its theta and the normalized strict
quotient coordinates. The ordinary proper/open refinement is constructed on the
ringed sequence site by the open-adjoint construction and proper compositors.
Its right-adjoint mate is invertible and preserves the Brown counits. Conjugate
this mate by the two theta isomorphisms and the input isomorphism b to construct
a in the displayed direction. The reconstructed-pair refinement coherence theorem
identifies its counit square in the canonical coordinates. Transport through the
two recorded presentation equivalences, using their mate and localization
normalizations, gives precisely the first equation, including leftAdjointUniq
for the supplied reduction packages. Apply the actual total limit and its
reconstruction unit to this whole-system equation. Naturality of the coefficient
model unit and counit gives the integral trace square. Rational realization and
closure scalar extension carry that square through their specified support
comparisons. Projection mate pasting and the bounded inclusion comparisons
identify the resulting refinement with condensedRefinement, giving the second
equation. Both support comparisons are the specified members of the same
ComparisonFamily, so its refinement coherence fixes their relative normalization.
Transpose this raw square using the specified adjunctions. Apply the inverse
homEquiv on the target compactification: conjugateEquiv_counit, counit naturality
and refinement naturality turn both sides into that raw square. Injectivity yields
the asserted right-adjoint square. No equality of system morphisms is inferred
from their evaluations. -/
theorem condensed_exceptional_refinement_counits
    (C : CompactSupportCondensedRealization.ComparisonFamily l k)
    (X Y : Base k) (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    (c d : Compactification f) (r : c.Refinement d)
    (Pc : Context l k X Y f c) (Pd : Context l k X Y f d)
    (hc : Pc.reduction = (C.coefficient (Field.{u} l)).reduction)
    (hd : Pd.reduction = (C.coefficient (Field.{u} l)).reduction)
    (qc : AtCompactification l k (C.coefficient (Field.{u} l)).realization Pc
      (specifiedSupport l k C Pc hc))
    (qd : AtCompactification l k (C.coefficient (Field.{u} l)).realization Pd
      (specifiedSupport l k C Pd hd))
    (v : Datum l k Pc) (w : Datum l k Pd)
    (hv : v.Admissible l k) (hw : w.Admissible l k) (b : v.L ≅ w.L) :
    RefinementCompatibility l k (C.coefficient (Field.{u} l)).realization X Y f c d r
      Pc Pd (specifiedSupport l k C Pc hc) (specifiedSupport l k C Pd hd)
      qc qd v w hv hw b := by
  sorry

end WeilConjectures.CondensedExceptionalReconstruction
