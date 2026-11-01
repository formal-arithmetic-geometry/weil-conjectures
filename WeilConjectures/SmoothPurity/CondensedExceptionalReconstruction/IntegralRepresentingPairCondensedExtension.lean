/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.ExceptionalReconstructionPresentations

/-! # Scalar extension of integral representing pairs

Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-integral-representing-pair-condensed-extension). -/

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
  (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l (Field.{u} l) W)

variable (D : CondensedERealization.Data l (Field.{u} l) k)
  (A : RealizationAt l (Field.{u} l) k D R X Y f c)

/-- Extend an integral pairing using precisely the recorded rational realization,
closure scalar functor, projection mate, and bounded inclusion comparison.
Source: current blueprint sk-prop-sp-rational and sk-thm-sp-qbar, scalar-extended counits.
(blueprint: lem-pur-integral-representing-pair-condensed-extension). -/
def integralPairCondensedCounit
    (M : Integral l (Field.{u} l) X.scheme) (L : Integral l (Field.{u} l) Y.scheme)
    (t : (integralSupport l (Field.{u} l) c R A.integral).obj M ⟶ L) :
    (CondensedRing.boundedConstructibleLowerShriekOfCompactification
      l (f := X.map Y f) c).obj ((realization l k D X).obj M) ⟶
        (realization l k D Y).obj L :=
  ObjectProperty.homMk
    ((CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
        l (f := X.map Y f) c).hom.app ((realization l k D X).obj M) ≫
      @inv _ _ _ _
        ((condensedProjection (omegaMap l (Field.{u} l) (embedding l)) c).app
          ((D.atObject X).realization.functor.obj
            ((pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
              (pbcUniformizer l (Field.{u} l))).obj M)).obj)
        (omegaProjection_isIso l (Field.{u} l) k (embedding l) X Y f c _) ≫
      (omegaScalar l (Field.{u} l) (embedding l) Y.scheme).map
        (A.realization.inv.app
          ((pbcRationalization X.scheme (pbcIntegralDatum l (Field.{u} l))
            (pbcUniformizer l (Field.{u} l))).obj M) ≫
          ((D.atObject Y).realization.functor ⋙
            (boundedConstructible (Coefficient (Field.{u} l) Y.scheme)).ι).map
              ((pbcRationalization Y.scheme (pbcIntegralDatum l (Field.{u} l))
                (pbcUniformizer l (Field.{u} l))).map t)))

/-- An integral representing pairing remains representing after the prescribed
rational realization and extension to the finite-subfield-valued closure ring.
Source: current blueprint sk-prop-sp-rational, localized Hom display;
sk-lem-sp-field-extension, scalar-extended adjunctions; sk-thm-sp-qbar,
filtered Hom display and its model-independence paragraph.
(blueprint: lem-pur-integral-representing-pair-condensed-extension).

Proof: the integral pairing maps are linear, since integralSupport is linear and
composition is bilinear. Turn their bijectivity into linear equivalences and
localize them at the uniformizer. The localization's Hom formula and the recorded
realization equivalences identify the localized maps with the rational pairing
obtained by A.realization inverse followed by the realization of t. Every rational
test object has an integral model, so transport along that model gives the pairing
bijection for every rational test. For a finite extension of the coefficient field,
restriction preserves bounded constructibility. Finite-dimensional coefficient
duality identifies extension with coextension, compatibly with the tensor unit and
counit. The scalar/support projection mate then transports the rational pairing
bijection to all tests over that finite extension. The actual mate equations imply
compatibility on further extension, including ramified extensions. Use the range of
the fixed embedding as the finite base subfield, transporting along its coefficient
ring isomorphism. These finite pairings give Pair and Pair.IsCompatible for the
canonical ScalarComparisons of filtered_condensed_representing_pair. Apply its
filtered descent: every test object, map and equality descends to a finite overfield.
Finally the canonical normalization of ScalarComparisons.omega, followed by the
bounded inclusion comparison, identifies the descended trace with
integralPairCondensedCounit, as an actual morphism equality. Transport the resulting
Hom equivalences through the full-subcategory inclusions. No integral system or
Brown identification is part of this statement, and no choice of an arbitrary
representing object is made. For t = 0 the representing hypothesis forces both
relevant Hom groups to vanish; the same construction covers that case. -/
theorem integral_representing_pair_condensed_extension
    (M : Integral l (Field.{u} l) X.scheme) (L : Integral l (Field.{u} l) Y.scheme)
    (t : (integralSupport l (Field.{u} l) c R A.integral).obj M ⟶ L)
    (ht : ∀ K : Integral l (Field.{u} l) X.scheme,
      Function.Bijective (fun a : K ⟶ M ↦
        (integralSupport l (Field.{u} l) c R A.integral).map a ≫ t))
    (Z : Omega l X.scheme) :
    Function.Bijective (fun a : Z ⟶ (realization l k D X).obj M ↦
      (CondensedRing.boundedConstructibleLowerShriekOfCompactification
        l (f := X.map Y f) c).map a ≫ integralPairCondensedCounit l k R D A M L t) := by
  sorry

end WeilConjectures.CondensedExceptionalReconstruction
