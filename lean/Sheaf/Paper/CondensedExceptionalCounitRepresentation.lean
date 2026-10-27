/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.CondensedExceptionalReconstructionData

/-! # CondensedExceptionalCounitRepresentation

Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-counit-representation). -/

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
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  (P : Context l k X Y f c)

variable (D : CondensedERealization.Data l (Field.{u} l) k)
  (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)

/-- The raw extended counits represent Hom and respect supplied system maps.
Source: blueprint sk-prop-sp-integral-adjunction, Hom display and counit paragraph;
sk-prop-sp-rational, localized Hom display; sk-thm-sp-qbar, filtered Hom display.
Parent reconstruction proof Steps 3--5.
(blueprint: lem-pur-condensed-exceptional-counit-representation).

Proof: express the supplied system in the normalized coordinates of the integral
representing-pair theorem. Paste the supplied open and proper presentation mates;
their localization equations identify supportSequence with the normalized beta
comparison. The actual reduction/limit adjunction then identifies the published
integral trace with Datum.integralCounit. Localize its integral-linear Hom
bijections. At each finite extension, including a ramified one, transpose the
extended trace to get the Brown-system scalar comparison and the finite-field
representing bijections. These comparisons preserve the trace by their defining
counit equations and commute with further extensions. The filtered condensed
representing-pair theorem now gives bijections on all closure-coefficient tests.
Its projection-normalized extended trace is exactly Datum.condensedCounit:
use the bounded inclusion comparison and the specified omega projection mate.
For a supplied system map, naturality of the actual Brown and reduction/limit
counits gives the integral trace square. Localization and scalar extension carry
that square to the condensed one below; projection naturality supplies its left
comparison. Every equality is transported as an actual morphism equality. -/
theorem condensed_exceptional_counit_representation :
    (∀ (d : Datum l k P) (hd : d.Admissible l k)
      (s : SystemIdentification l k d hd) (Z : Omega l X.scheme),
      Function.Bijective (fun a : Z ⟶ (realization l k D X).obj
          (d.integral l k hd.reconstructs) ↦
        (CondensedRing.boundedConstructibleLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj l) l (f := X.map Y f) c).map a ≫
            d.condensedCounit l k D hd.reconstructs A s.reduction s.theta
              s.originUnit s.originSupport)) ∧
    (∀ (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
      (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
      (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower),
      d.SystemMap l k b a sd.theta se.theta →
      (CondensedRing.boundedConstructibleLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) l (f := X.map Y f) c).map
          ((realization l k D X).map (Datum.LimitMap l k a hd.reconstructs he.reconstructs)) ≫
        e.condensedCounit l k D he.reconstructs A se.reduction se.theta
          se.originUnit se.originSupport =
      d.condensedCounit l k D hd.reconstructs A sd.reduction sd.theta
          sd.originUnit sd.originSupport ≫ (realization l k D Y).map b) := by
  sorry

end WeilConjectures.CondensedExceptionalReconstruction
