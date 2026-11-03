/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.DerivedLimitLowerBound
import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleFiniteTypeFrames
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # Native objects in the zero-section coefficient argument

Source: `lem-pur-zero-section-bottom-coefficients`, Steps 3--8 of the
native-coefficient refinement of the universal case in
`thm-pur-localized-top-chern.proof.md`, Step 3.
These objects are the existing signed coefficient line and actual derived
closed support. The finite tower is viewed by exact restriction of scalars
in the fixed integral module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.PurityFiniteSetting

/-- The shifted root-normalized line, without choosing any purity generator.
Source: the coefficient input in Steps 3--8
(blueprint: def-pur-zero-section-coefficient-objects). -/
def nativeZeroInput (P : PurityFiniteSetting.{u})
    (c : PurityTransport.Coefficient P.coefficients.l) (X : Scheme.{u}) (r : ℕ) :
    c.derived P.coefficients.l X :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (spInternalSignedTwist X (condensedRingObj (c.obj P.coefficients.l) X)
      (c.firstLine P.coefficients.l X) (r : ℤ))) ⟦2 * (r : ℤ)⟧

/-- The actual derived closed support of the shifted coefficient line.
Source: Steps 3--8, using the kernel-defined closed-support functor
(blueprint: def-pur-zero-section-coefficient-objects). -/
def nativeZeroSupport {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l) : c.derived P.coefficients.l B :=
  let := (V.zeroSection_spec).2.1
  (closedSupport (c.obj P.coefficients.l) V.zeroSection
    V.zeroSection.openComplement.ι).rightDerivedFunctor.obj (nativeZeroInput P c V.E r)

/-- The genuine finite quotients of the integral coefficient Z_l.
Source: Steps 4--6, the special case R = Z_l
(blueprint: def-pur-zero-section-coefficient-objects). -/
def zeroPrimePowerCoefficient (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    PurityTransport.Coefficient ell :=
  letI : NeZero (ell ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ell.Prime).ne_zero⟩
  .finite (CommRingCat.of (ZMod (ell ^ (n + 1)))) inferInstance n
    (by rw [← Nat.cast_pow]; exact ZMod.natCast_self _)

/-- The finite supported objects, restricted along their genuine integral quotient maps.
Source: Steps 2, 5 and 6, in the fixed integral module category
(blueprint: def-pur-zero-section-coefficient-objects). -/
def zeroIntegralSupportTerms {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) (n : ℕ) :
    (PurityTransport.Coefficient.integers).derived P.coefficients.l B :=
  let c := zeroPrimePowerCoefficient P.coefficients.l n
  (Mod.comap (coefficientMap (c.integralMap P.coefficients.l) B)).mapDerivedCategory.obj
    (nativeZeroSupport V c)

/-- Exact restriction of scalars transfers the common bound to every term.
Source: Step 6 of the native integral-coefficient argument.
Proof: restriction of scalars is additive and exact, so its termwise derived
functor commutes with cohomology and preserves the given lower bound.
(blueprint: def-pur-zero-section-coefficient-objects). -/
theorem zeroIntegralSupportTerms_isGE {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) (n : ℕ) (a : ℤ)
    (h : (nativeZeroSupport V (zeroPrimePowerCoefficient P.coefficients.l n)).IsGE a) :
    (zeroIntegralSupportTerms V n).IsGE a := by
  let c := zeroPrimePowerCoefficient P.coefficients.l n
  let := h
  exact (Mod.comap (coefficientMap (c.integralMap P.coefficients.l) B)).isGE_mapDerivedCategory_obj
    (nativeZeroSupport V c) a

/-- Combine finite local vanishing, the integral Roos triangle, and flat scalar
comparison. These are three different parts of the native-coefficient argument.
Source: Steps 3--8 of the node proof.
Proof: finite inputs use finite local vanishing. Exact scalar restriction gives
the same lower bound for every term of the integral tower. Apply the Roos
common-bound theorem to obtain the integral bound. For any of the four remaining
coefficients, its scalar comparison is an isomorphism from an exact derived
scalar image of that integral object. Exactness and invariance under isomorphism
transfer the integral bound.
(blueprint: def-pur-zero-section-coefficient-objects). -/
theorem nativeZeroSupport_isGE_of_comparisons
    {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r)
    (hfinite : ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
      (hA : (P.coefficients.l ^ (n + 1) : A) = 0),
      (nativeZeroSupport V (.finite A fin n hA)).IsGE 0)
    (hlimit : ∃ hprod : HasProduct (zeroIntegralSupportTerms V),
      letI := hprod
      ∃ f : ∀ n, zeroIntegralSupportTerms V (n + 1) ⟶ zeroIntegralSupportTerms V n,
        IsDerivedLimit f (nativeZeroSupport V .integers))
    (hscalar : ∀ c : PurityTransport.Coefficient P.coefficients.l,
      (match c with | .finite _ _ _ _ => False | _ => True) →
      ∃ hflat : PreservesFiniteLimits
          (Mod.extendScalars (coefficientMap (c.integralMap P.coefficients.l) B)),
        letI := hflat
        Nonempty
          ((Mod.extendScalars
            (coefficientMap (c.integralMap P.coefficients.l) B)).mapDerivedCategory.obj
            (nativeZeroSupport V .integers) ≅ nativeZeroSupport V c))
    (c : PurityTransport.Coefficient P.coefficients.l) :
    (nativeZeroSupport V c).IsGE 0 := by
  obtain ⟨hprod, f, hf⟩ := hlimit
  let := hprod
  have hint : (nativeZeroSupport V .integers).IsGE 0 := by
    refine isGE_of_isDerivedLimit (zeroIntegralSupportTerms V) f _ hf 0 ?_
    intro n
    apply zeroIntegralSupportTerms_isGE
    unfold zeroPrimePowerCoefficient
    exact hfinite _ _ n _
  have hchange (d : PurityTransport.Coefficient P.coefficients.l)
      (hd : match d with | .finite _ _ _ _ => False | _ => True) :
      (nativeZeroSupport V d).IsGE 0 := by
    obtain ⟨hflat, ⟨e⟩⟩ := hscalar d hd
    let := hflat
    let := hint
    have :=
      (Mod.extendScalars
        (coefficientMap (d.integralMap P.coefficients.l) B)).isGE_mapDerivedCategory_obj
        (nativeZeroSupport V .integers) 0
    exact DerivedCategory.TStructure.t.isGE_of_iso e 0
  cases c with
  | finite A fin n hA => exact hfinite A fin n hA
  | integers => exact hint
  | rationals => exact hchange .rationals trivial
  | integral E => exact hchange (.integral E) trivial
  | rational E => exact hchange (.rational E) trivial
  | closure => exact hchange .closure trivial

/-- The adjunction gives the initial lower bound -2r, including rank zero.
Source: the rank-zero boundary case of Step 11.
Proof: a degree-zero module shifted by 2r has lower bound -2r. A map
from an object in degrees at most -2r-1 into its closed support transposes
to a map into this shifted module. Exact closed direct image preserves the
upper bound, so the transpose is zero by orthogonality. Adjunction and
its preservation of zero imply the original map is zero.
(blueprint: def-pur-zero-section-coefficient-objects). -/
theorem nativeZeroSupport_isGE_neg {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r)
    (c : PurityTransport.Coefficient P.coefficients.l) :
    (nativeZeroSupport V c).IsGE (-(2 * (r : ℤ))) := by
  let := (V.zeroSection_spec).2.1
  let := V.locallyFree
  let := (VectorBundleZeroSection.finite_type_frames P.field.k B hB r V.𝓔).choose
  let := (VectorBundleZeroSection.finite_type_frames P.field.k B hB r V.𝓔).choose_spec.1
  let : IsNoetherian V.E := isNoetherian_of_locallyOfFiniteType V.phi.hom
  let : PreservesFiniteColimits (lowerStar (c.obj P.coefficients.l) V.zeroSection) :=
    closedSupport_lowerStarExact _ V.zeroSection V.zeroSection.openComplement.ι
      V.zeroSection.range_eq_compl_range_openComplement_ι
  let n : ℤ := -(2 * (r : ℤ))
  have hinput : (nativeZeroInput P c V.E r).IsGE n := by
    unfold nativeZeroInput
    exact DerivedCategory.TStructure.t.isGE_shift _ 0 (2 * (r : ℤ)) n (by dsimp [n]; omega)
  let adj := closedSupportDerivedAdjunction (c.obj P.coefficients.l)
    V.zeroSection V.zeroSection.openComplement.ι
    V.zeroSection.range_eq_compl_range_openComplement_ι
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega) _).2 ?_
  intro A f hA
  let : A.IsLE (n - 1) := hA
  have hpush := (lowerStar (c.obj P.coefficients.l) V.zeroSection).isLE_mapDerivedCategory_obj
    A (n - 1)
  have hz : (adj.homEquiv A (nativeZeroInput P c V.E r)).symm f = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n - 1) n (by omega) hpush hinput
  rw [← (adj.homEquiv A (nativeZeroInput P c V.E r)).apply_symm_apply f,
    hz, adj.homEquiv_unit, Functor.map_zero, comp_zero]

end WeilConjectures.PurityFiniteSetting
