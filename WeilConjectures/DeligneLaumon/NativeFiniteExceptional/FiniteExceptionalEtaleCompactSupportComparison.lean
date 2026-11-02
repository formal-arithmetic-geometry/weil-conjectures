/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeFiniteExceptional.NativeFiniteExceptionalConstructions
public import WeilConjectures.AlgebraicGeometry.CoefDualizingSiteMates.CoefDualizingSiteMates
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence

/-! # The ordinary etale normalization of finite compact-support reduction

Source: latest blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
lem-coef-finite-exceptional.proof.md, final paragraph; part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/lem-coef-finite-dualizing.md, counit normalization
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison).

The coefficient indices are predecessors of positive exponents, as in the native
finite exceptional construction. Universal tensor presentations are identified with
scalar extension by their scalar units, never by an independently chosen isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace WeilConjectures.NativeFiniteExceptional

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- Finiteness of the actual positive coefficient quotient, reused from the coefficient
library. Source: finite coefficient convention
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison). -/
local instance finiteRing (n : ℕ) : Finite (Ring ell E n) :=
  Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos n)

/-- The ordinary etale arrow in the structural compositor is the specified tensor
comparison, naturally in its input, with its proper and open factors retained.
Source: lem-coef-finite-exceptional.proof.md, final paragraph
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison).

Proof: write c=(j,p). By def-per-exceptional-coefficient-maps the ordinary arrow is
scalarMate at j_!K followed by Rp_* of the open balancing isomorphism. The proper
scalar normalization identifies the first factor with the ordered projection map;
the open scalar coherence identifies the second with the unit-normalized balancing
map. Apply the scalar Hom adjunction and precompose both candidates with its unit.
On K-flat representatives both apply the proper counit to the original factor and
retain the B factor in the same order. Injectivity of the Hom equivalence gives
B-linear equality. The canonical modelIso is itself the transpose of the universal
tensor unit, so the displayed transports preserve this calculation. Both factors
are natural, giving the final square. No flatness of the quotient is used. -/
theorem etaleCompactSupportComparison (D : FiniteFieldDatum.{u}) (_hell : ell ≠ D.p)
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) :
    let A := ULift.{u + 1} (Ring ell E (n + 1))
    let B := ULift.{u + 1} (Ring ell E n)
    let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (quotient ell E n.le_succ)
    ∀ (K : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (M : Etale.CoefficientTensorModel φ X K)
      (N : Etale.CoefficientTensorModel φ Y
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj K)),
    (_hK : finiteTorConstructibleEtale ell E (n + 1 + 1)
      (Nat.succ_pos (n + 1)) X K.obj) →
    let eX := ProEtale.CoefDualizingSiteMates.modelIso M
    let eY := ProEtale.CoefDualizingSiteMates.modelIso N
    let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let aA := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c
    let aB := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} B) c
    (Etale.ExceptionalCoefficients.compactSupportMap φ c K.obj =
      (Etale.scalarExtension φ Y).map (aA.inv.app K) ≫ eY.hom ≫
        (Etale.compactSupportCoefficientComparisonPlus c M N).hom ≫
        aB.hom.app M.obj ≫ FB.map eX.inv) ∧
    (Etale.ExceptionalCoefficients.compactSupportMap φ c K.obj =
      (Etale.scalarMate φ c.g).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K.obj) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        ((Etale.ExceptionalCoefficients.openIso φ c.i).hom.app K.obj)) ∧
    (∀ (L : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (_hL : finiteTorConstructibleEtale ell E (n + 1 + 1)
        (Nat.succ_pos (n + 1)) X L.obj) (a : K.obj ⟶ L.obj),
      (Etale.scalarExtension φ Y).map (FA.map a) ≫
          Etale.ExceptionalCoefficients.compactSupportMap φ c L.obj =
        Etale.ExceptionalCoefficients.compactSupportMap φ c K.obj ≫
          FB.map ((Etale.scalarExtension φ X).map a)) := by
  sorry

/-- At the structural dualizing object the same ordinary map occurs in the prescribed
counit identity; the scalar-unit comparison is retained explicitly.
Source: lem-coef-finite-dualizing.md, displayed adjunct and final sentence, and
lem-coef-finite-exceptional.proof.md, final paragraph
(blueprint: lem-sf-finite-exceptional-etale-compact-support-comparison).

Proof: specialize the preceding comparison to the structure compactification and
its dualizing input. Substitute that equality into the defining adjunct of the
finite dualizing coefficient map. The exceptional Hom equivalence sends this
adjunct to u. Its inverse sends u to F_B(u) followed by the B counit. Hence that
composite is exactly the inverse compact-support comparison, scalar image of the
A counit, and normalized regular-unit comparison, in the prescribed order.
This is substitution in lem-coef-finite-dualizing, with no new normalization or
invertibility assertion outside the domain of the coefficient-change theorem. -/
theorem etaleCompactSupportComparison_counit (n : ℕ)
    (D : FiniteFieldDatum.{u}) (_hell : ell ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    let A := ULift.{u + 1} (Ring ell E (n + 1))
    let B := ULift.{u + 1} (Ring ell E n)
    let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (quotient ell E n.le_succ)
    letI : Finite A := inferInstance
    letI : Finite B := inferInstance
    let adA := Etale.rightDerivedUpperShriekOfCompactificationAdjunction A c
    let adB := Etale.rightDerivedUpperShriekOfCompactificationAdjunction B c
    let GA := Etale.rightDerivedUpperShriekOfCompactification A c
    let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let omega := GA.obj (𝟙_ (Etale.DerivedCategoryModule A (Spec (.of D.k))))
    let word := Etale.ExceptionalCoefficients.comparisonInverse φ c omega ≫
      (Etale.scalarExtension φ (Spec (.of D.k))).map
        (adA.counit.app (𝟙_ (Etale.DerivedCategoryModule A (Spec (.of D.k))))) ≫
      (Etale.ExceptionalCoefficients.unitIso φ (Spec (.of D.k))).hom
    let u := adB.homEquiv _ _ word
    FB.map u ≫
        adB.counit.app (𝟙_ (Etale.DerivedCategoryModule B (Spec (.of D.k)))) = word := by
  sorry

end WeilConjectures.NativeFiniteExceptional
