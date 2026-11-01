/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.CondensedExceptionalReconstructionData

/-! # Integral representation of the reconstructed counit

Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-integral-counit-bijective). -/

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

/-- The reconstructed integral counit represents the integral compact-support Hom functor.
Source: current blueprint sk-prop-sp-integral-adjunction, displayed Hom chain and
final unit/counit paragraph; parent reconstruction proof Step 1.
(blueprint: lem-pur-condensed-exceptional-integral-counit-bijective).

Proof: transport the recorded pro-etale systems to the fixed quotient coordinates
of the integral representing-pair theorem. The ordinary section normalization fixes
proper pushforward; its adjunction mate fixes pullback. Localizing the specified
ordinary square fixes the derived comparison. Paste the proper and open mates to
identify supportSequence with the canonical beta in those coordinates. The supplied
normalization, intrinsic constructibility, bounds and reconstruction give Supplied;
s.theta supplies its first recognition alternative and s.levels gives its evaluated
normalization. Apply reconstructedRepresentingPair. The fixed coordinate equivalence
and coefficient-model counit identify its reconstructed object with d.integral.
Its trace_reduction formula, the alpha_transport equation, and the two adjunction
triangles identify the image of the identity with Datum.integralCounit, using the
actual inverses of s.reduction and the specified site units. Naturality in a test
map h then identifies every Hom image with integralSupport.map h followed by that
counit. The published linear Hom equivalence is bijective; transport through the
fixed object isomorphism proves the claim. This argument also covers zero objects
and empty schemes, and does not assume that evaluations lift arbitrary system maps. -/
theorem condensed_exceptional_integral_counit_bijective
    (d : Datum l k P) (hd : d.Admissible l k)
    (s : SystemIdentification l k d hd)
    (K : Integral l (Field.{u} l) X.scheme) :
    Function.Bijective (fun a : K ⟶ d.integral l k hd.reconstructs ↦
      (integralSupport l (Field.{u} l) c P.reduction A.integral).map a ≫
        d.integralCounit l k D hd.reconstructs A s.reduction s.theta
          s.originUnit s.originSupport) := by sorry

end WeilConjectures.CondensedExceptionalReconstruction
