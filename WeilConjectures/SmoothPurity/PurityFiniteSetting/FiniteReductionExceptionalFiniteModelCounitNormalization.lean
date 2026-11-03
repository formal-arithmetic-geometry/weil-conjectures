/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeFiniteExceptional.NativeFiniteExceptionalConstructions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence

/-! # The normalized finite exceptional counit in native coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 4
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization).

The native finite-Tor domain has module-object coefficients p_T^* A. The normalized
section-action encoding supplies its fixed-scalar coordinates. Right-adjoint uniqueness
compares the chosen etale adjoint with the standard adjoint used by the smooth counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u}) (r : ℕ)

local instance : TopologicalSpace (NativeFiniteExceptional.Ring P.coefficients.l P.extension r) := ⊥
local instance : DiscreteTopology (NativeFiniteExceptional.Ring P.coefficients.l P.extension r) :=
  ⟨rfl⟩
local instance : IsTopologicalRing (NativeFiniteExceptional.Ring P.coefficients.l P.extension r) :=
  inferInstance
local instance : Finite (NativeFiniteExceptional.Ring P.coefficients.l P.extension r) :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension (r + 1) (Nat.succ_pos r)

variable {X Y : Over (Spec (.of P.field.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]

local instance : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom

/-- The compactification specified by the finite-type-over-field theorem.
Source: blueprint finite-reduction proof, Step 4, standing compactification
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization). -/
def finiteCounitCompactification : Compactification f.left := by
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  letI : QuasiCompact (X.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact X.hom)
  letI : LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  letI : QuasiCompact (Y.left ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact Y.hom)
  letI := hasCompactification_of_finiteType_over_field P.field.k X.left Y.left f.left
  exact HasCompactification.compactification f.left

local instance :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (NativeFiniteExceptional.Ring P.coefficients.l P.extension r)))
      (P.finiteCounitCompactification f)).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ _

/-- The standard-to-chosen exceptional comparison, with its counit normalization fixed
by ordinary etale right-adjoint uniqueness. No comparison is selected from bare existence.
Source: blueprint finite-reduction proof, Step 4, fixedExceptionalIso cancellation
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization). -/
def finiteCounitRightAdjointComparison :
    let A := NativeFiniteExceptional.Ring P.coefficients.l P.extension r
    let c := P.finiteCounitCompactification f
    sfFiniteExceptionalFixed A c ≅ sfFiniteExceptionalAt (ULift.{u + 1} A) c := by
  let A := NativeFiniteExceptional.Ring P.coefficients.l P.extension r
  let c := P.finiteCounitCompactification f
  letI := c.hasCompactification
  exact FiniteRestriction.exceptionalComparison A c
    (Etale.rightDerivedUpperShriek (ULift.{u + 1} A) f.left)
    (Etale.rightDerivedUpperShriekAdjunctionOfCompactification (ULift.{u + 1} A) c)

/-- The smooth exceptional counit in the dependency's native coefficient coordinates.
It uses the same bounded-below published counit as smoothExceptionalCounit: the
canonical support comparison, the image of the published counit and the coefficient
equivalence counit. The initial map compares the chosen etale adjoint with the standard
one, and the compactification origin comparison has its published direction. Outside
D+ it is zero, exactly as in the original totalized smoothExceptionalCounit.
Source: blueprint def-pur-smooth-trace and finite-reduction proof, Step 4
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization). -/
def nativeSmoothExceptionalCounit
    (encoding : ∀ (n : ℕ) (T : Scheme.{u}),
      Encoding (NativeFiniteExceptional.Ring P.coefficients.l P.extension n) T)
    (K : _root_.DerivedCategory
      (Internal (NativeFiniteExceptional.Ring P.coefficients.l P.extension r) Y.left)) :
    let A := NativeFiniteExceptional.Ring P.coefficients.l P.extension r
    let c := P.finiteCounitCompactification f
    (FiniteRestriction.support A c).obj
        ((FiniteRestriction.conjugate A (encoding r)
          (sfFiniteExceptionalAt (ULift.{u + 1} A) c)).obj K) ⟶ K := by
  classical
  let A := NativeFiniteExceptional.Ring P.coefficients.l P.extension r
  let c := P.finiteCounitCompactification f
  letI := c.hasCompactification
  let L := (encoding r Y.left).fixedDerived.functor.obj K
  exact if hL : _root_.DerivedCategory.TStructure.t.plus L then
    (FiniteRestriction.support A c).map
        ((encoding r X.left).fixedDerived.inverse.map
          ((P.finiteCounitRightAdjointComparison r f).inv.app L)) ≫
      (FiniteRestriction.comparison A (encoding r) c).hom.app
        ((sfFiniteExceptionalFixed A c).obj L) ≫
      (encoding r Y.left).fixedDerived.inverse.map
        ((rightDerivedLowerShriekCompactificationIso (ULift.{u + 1} A) c).inv.app
            ⟨_, plus_etaleRightDerivedUpperShriek_obj f.left hL⟩ ≫
          rightDerivedUpperShriekCounit f.left L hL) ≫
      (encoding r Y.left).fixedDerived.unitIso.inv.app K
  else 0

/-- The included normalized finite counit is the specified native smooth exceptional
counit, and its input always selects the bounded-below branch. This is one coefficient
level; smoothness and coefficient-flatness are not assumed.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 4
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization).

Proof: (1) bounded constructible cohomology has finite support, hence a lower bound;
the exact termwise normalized encoding preserves that bound. This includes zero objects
and empty schemes. (2) Apply the specified exceptional Hom chain to its etale-origin
witness (the standard etale exceptional image, identity). Its inverse at identity is
the published counit, transported by the compactification origin comparison. The
ordinary right-adjoint uniqueness comparison is finiteCounitRightAdjointComparison.
(3) Apply the selected AdjunctionNormalized formula to this witness and counit.
(4) The identity evaluation cancels the right-adjoint comparison with the displayed
inverse factor. (5) Use Hom-equivalence naturality along the coefficient equivalence
unit inverse. (6) The coefficient equivalence triangle identity makes its transpose
identity, so Hom injectivity identifies the included adjunction counit. (7) Unfold
the bounded-below branch of nativeSmoothExceptionalCounit; its four displayed factors
are precisely this map. No ambient pro-etale right adjoint or scalar-change equation
is used. -/
theorem finiteReductionExceptionalFiniteModel_counit_normalization
    (encoding : ∀ (n : ℕ) (T : Scheme.{u}),
      Encoding (NativeFiniteExceptional.Ring P.coefficients.l P.extension n) T)
    (K : (NativeFiniteExceptional.domain P.coefficients.l P.extension Y.left r).FullSubcategory) :
    _root_.DerivedCategory.TStructure.t.plus
        ((encoding r Y.left).fixedDerived.functor.obj K.obj) ∧
      ((NativeFiniteExceptional.adjunction P.coefficients.l P.extension P.field
        P.coefficients.different f (P.finiteCounitCompactification f)
        encoding r).counit.app K).hom = P.nativeSmoothExceptionalCounit r f encoding K.obj := by
  sorry

end WeilConjectures.PurityFiniteSetting
