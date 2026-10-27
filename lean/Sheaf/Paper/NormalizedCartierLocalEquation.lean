/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-! # The local equation of a normalized Cartier Kummer representative

Source: blueprint lem-pur-divisor-class, local equation clause and its relative
Yoneda sign calculation (blueprint: lem-pur-normalized-cartier-local-equation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- A single normalized Cartier representative restricts to minus the principal
frame boundary, also in the singleton ordered-product presentation.

Source: blueprint lem-pur-divisor-class, clause (a), relative torsor sign computation;
DAG lem-pur-principal-torsor-yoneda-sign and lem-pur-divisor-normalized-realization.
(blueprint: lem-pur-normalized-cartier-local-equation).

Proof: use the canonical frame of the dual Cartier ideal on the complement. The
SupportedKummerBoundary witnesses and relative-extension uniqueness identify its
integral class with divisorRelativeExtension. The unique scalar realization gives
its finite module class. Pull back the framed pair to the specified etale chart,
using divisorRealization_pullback and the canonical ideal pullback identification.
For the equation f, the dual frame e=f^-1 has complementary section f e. Apply
principal_torsor_yoneda_sign: its relative extension is the inverse-unit pushout,
and splicing with the Kummer sequence is minus the localization boundary of f.
The normalized relative-cone comparison and root scalar/site comparisons carry
this boundary to frameBoundary, with the same minus sign. The ordered product
for Fin 1 begins with the supported unit and appends this sole factor; the cup
unit law, tensor left unitor, and canonical closed-support intersection comparison
identify it with frameBoundary after Set.range_const support transport. This gives
both HEq clauses. No quasi-compactness of the etale chart is needed. A unit f gives
empty support and zero on both sides; an empty chart is covered by the same formulas. -/
theorem normalizedCartier_localEquation (P : PurityFiniteSetting.{u})
    {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2)
    (α : P.FunctorialCupH false i 2 1) (hα : HEq κ.hom α)
    (hκ : Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a) κ)
    (U : Scheme.{u}) (e : U ⟶ T) [Etale e] (f : Γ(U, ⊤))
    (t : U.zeroLocusSubscheme {f} ⟶ D)
    (sq : ChosenCartesianSquare t (U.zeroLocusSubschemeι {f}) i e) :
    HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.functorialCupCompare i 2 1 α))
      (-(P.frameBoundary U (e ≫ a) f)) ∧
    HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
      a 2 1 (P.functorialCupCompare i 2 1 α))
      (-(P.frameBoundaryProduct U (e ≫ a) 1 (fun _ : Fin 1 ↦ f))) := by sorry

end WeilConjectures.PurityFiniteSetting
