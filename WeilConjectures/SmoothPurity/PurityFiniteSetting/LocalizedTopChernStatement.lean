/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChern
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupComparisonBasic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame
public import WeilConjectures.SmoothPurity.DivisorClass.DivisorClass
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCanonicalEtale
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChernKummerFamily
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChernKummerLaws
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.LocalizedTopChernStatementModels
/-!
# Localized top Chern classes, with the current divisor and frame interfaces

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.md`, L1--L4 and the final local-frame display;
`thm-pur-localized-top-chern.proof.md`, its six DAG proof paragraphs
(blueprint: thm-pur-localized-top-chern).

The finite-root Tate isomorphism and the supported-adjunction/site comparisons
are constructed explicitly. The line clause uses the current interface Cartier
map, with the sign `c = -cD`. The frame clause uses the current upstream
`Etale.frameClass`, whose definition is the ordered Kummer boundary product.
The family, base-change law, direct-sum law, and ordinary Chern construction are
the published declarations. This module replaces the superseded theorem as the
statement attachment without changing those public constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u c v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

/-- The fixed finite coefficient ring has positive characteristic.
Source: finite-coefficient purity conventions (blueprint: thm-pur-localized-top-chern). -/
instance localizedTopChernCoefficientChar (P : PurityFiniteSetting.{u}) :
    NeZero (ringChar P.Coefficient) :=
  ⟨CharP.ringChar_ne_zero_of_finite P.Coefficient⟩

/-- The annihilating exponent is invertible on every scheme over the fixed field.
Source: def-pur-conventions (blueprint: thm-pur-localized-top-chern). -/
abbrev localizedTopChernInvertibleExponent (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) : HasInvertibleExponent P.Coefficient T :=
  ⟨P.diagonalExponent, pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level,
    P.diagonalExponent_annihilates, P.diagonalExponent_isUnit a⟩

/-- The single-complex tensor comparison is invertible for the finite Tate lines.
Source: finite twists are locally free of rank one, hence flat; degree-zero flat
complexes compute the derived tensor (blueprint: thm-pur-localized-top-chern,
coefficient comparison for the local frame formula).
Proof: trivialize the root line on its primitive-root étale cover. Its positive
powers are free rank one there, so both degree-zero complexes are K-flat. The
localization tensor comparison is therefore the ordinary tensor comparison and
is an isomorphism. Reflect this along the covering inverse images. -/
theorem localizedTopChernSingleTensor_isIso (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    IsIso (ProEtale.cupSingleTensorMap
      (P.functorialCupTwist false T r) (P.functorialCupTwist false T 1)) := by
  let inverse : TensorInverse (P.functorialCupTwist false T r) :=
    { obj := P.functorialCupTwist false T (-(r : ℤ))
      rightIso := P.functorialCupTwistProduct false T a r (-(r : ℤ)) ≪≫
        eqToIso (congrArg (P.functorialCupTwist false T) (add_neg_cancel (r : ℤ)))
      leftIso := P.functorialCupTwistProduct false T a (-(r : ℤ)) r ≪≫
        eqToIso (congrArg (P.functorialCupTwist false T) (neg_add_cancel (r : ℤ))) }
  exact localizedTopChernSingleTensorMap_isIso _ _ inverse.flat

/-- Assemble ordered positive-power comparisons in an abstract monoidal category.
Source: the ordered tensor-power convention of def-coefficient-twists-detailed
(blueprint: thm-pur-localized-top-chern, coefficient comparison).
Keeping this recursion abstract avoids expanding the concrete site structures. -/
def localizedTopChernPowerIso {C : Type c} [Category.{v} C] [MonoidalCategory C]
    (S T : ℕ → C) (zero : S 0 ≅ T 0) (one : S 1 ≅ T 1)
    (stepS : ∀ r : ℕ, S (r + 2) ≅ S (r + 1) ⊗ S 1)
    (stepT : ∀ r : ℕ, T (r + 1) ⊗ T 1 ≅ T (r + 2)) :
    (r : ℕ) → S r ≅ T r
  | 0 => zero
  | 1 => one
  | r + 2 => stepS r ≪≫
      tensorIso (localizedTopChernPowerIso S T zero one stepS stepT (r + 1)) one ≪≫
      stepT r

/-- The unit comparison in degree zero.
Source: def-coefficient-twists-detailed (blueprint: thm-pur-localized-top-chern). -/
def localizedTopChernTateZeroIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) :
    (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T 0) ≅
      Etale.tateObject P.Coefficient T 0 := by
  letI := P.localizedTopChernInvertibleExponent a
  exact (Etale.constantComplexIsoSingleFunctor P.Coefficient T).symm ≪≫
    (Etale.HasTateTwist.twistObjectZeroIso (Λ := P.Coefficient) T).symm

/-- The rank-one root-insertion comparison, with the exact three factors of the
current divisor interface's canonicalFiniteTateLineIso. Source: its coefficient
extension construction (blueprint: thm-pur-localized-top-chern, L1). -/
def localizedTopChernTateOneIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) :
    (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T 1) ≅
      Etale.tateObject P.Coefficient T 1 := by
  letI := P.localizedTopChernInvertibleExponent a
  exact (DerivedCategory.singleFunctor _ 0).mapIso
      (localizedTopChernRootLineAbIso T
        P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates (P.diagonalExponent_isUnit a)) ≪≫
    (Etale.tateTwistObjectIsoSingleFunctor P.Coefficient T 1).symm

/-- Split off the last finite root line before taking its degree-zero complex.
Source: ordered finite twists and the K-flat tensor comparison
(blueprint: thm-pur-localized-top-chern, coefficient comparison). -/
def localizedTopChernFiniteStepIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T (r + 2 : ℕ)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T (r + 1 : ℕ)) ⊗
        (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T 1) := by
  letI := localizedTopChernSingleTensor_isIso P T a (r + 1)
  let mul := P.functorialCupEtaleTwistProduct T a (r + 1 : ℕ) 1 ≪≫
    eqToIso (congrArg (P.functorialCupTwist false T)
      (Int.natCast_succ (r + 1)).symm)
  exact (DerivedCategory.singleFunctor _ 0).mapIso mul.symm ≪≫
    (asIso (ProEtale.cupSingleTensorMap
      (P.functorialCupTwist false T (r + 1 : ℕ))
      (P.functorialCupTwist false T 1))).symm

/-- Multiply the normalized Tate powers, retaining their integer reindexing.
Source: def-coefficient-twists-detailed (blueprint: thm-pur-localized-top-chern). -/
def localizedTopChernTateStepIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    Etale.tateObject P.Coefficient T (r + 1 : ℕ) ⊗ Etale.tateObject P.Coefficient T 1 ≅
      Etale.tateObject P.Coefficient T (r + 2 : ℕ) := by
  letI := P.localizedTopChernInvertibleExponent a
  exact Etale.HasTateTwist.twistObjectAddIso T (r + 1 : ℕ) 1 ≪≫
    eqToIso (congrArg (Etale.tateObject P.Coefficient T)
      (Int.natCast_succ (r + 1)).symm)

/-- Canonical finite-root to normalized Tate comparison: the unit, the published
root-insertion map, and their ordered tensor powers. Source:
def-coefficient-twists-detailed (blueprint: thm-pur-localized-top-chern). -/
def localizedTopChernTateIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T r) ≅
      Etale.tateObject P.Coefficient T r :=
  localizedTopChernPowerIso
    (fun j : ℕ ↦ (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T j))
    (fun j : ℕ ↦ Etale.tateObject P.Coefficient T j)
    (P.localizedTopChernTateZeroIso T a) (P.localizedTopChernTateOneIso T a)
    (P.localizedTopChernFiniteStepIso T a) (P.localizedTopChernTateStepIso T a) r

/-- Canonical inverse to finite étale/pro-étale supported-Hom comparison.
Source: lem-pur-supported-cup-comparison-basic (blueprint: thm-pur-localized-top-chern). -/
def localizedTopChernEtaleLift (P : PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ T) [IsClosedImmersion i] (r : ℕ)
    (c : P.FunctorialCupH true i (2 * (r : ℤ)) r) :
    P.FunctorialCupH false i (2 * (r : ℤ)) r :=
  (Equiv.ofBijective (P.functorialCupCompare i (2 * (r : ℤ)) r)
    ((supportedCupComparisonBasic P).1 i a (2 * (r : ℤ)) r)).symm c

/-- Canonical supported-adjunction coordinates for the localized morphism.
The formula uses the canonical site-comparison inverse, the proper closed
`Ri_! = Ri_*` and single-functor comparisons, the `Ri_! ⊣ Ri^!` mate,
and the finite-root Tate comparison. Source: lem-pur-divisor-class and
lem-pur-supported-hom (blueprint: thm-pur-localized-top-chern). -/
def localizedTopChernSupported (P : PurityFiniteSetting.{u})
    {Z T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : Z ⟶ T) [IsClosedImmersion i] (r : ℕ)
    (c : P.FunctorialCupH true i (2 * (r : ℤ)) r) :
    Etale.constantComplex P.Coefficient T ⟶
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
        ((Etale.rightDerivedUpperShriek P.Coefficient i).obj
          ((Etale.tateObject P.Coefficient T r)⟦2 * (r : ℤ)⟧)) := by
  let L := (Etale.tateObject P.Coefficient T r)⟦2 * (r : ℤ)⟧
  let lower := Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i
  let eLower := (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} P.Coefficient) i).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (Etale.ordinaryFiniteConstant P.Coefficient Z)) ≫
    lower.singleFunctorCompRightDerivedFunctorIso.hom.app
      (Etale.ordinaryFiniteConstant P.Coefficient Z)
  let hκ := eLower ≫ P.localizedTopChernEtaleLift a i r c ≫
    (shiftFunctor _ (2 * (r : ℤ))).map (P.localizedTopChernTateIso T a r).hom
  let hD := (Etale.constantComplexIsoSingleFunctor P.Coefficient Z).hom ≫
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient i).homEquiv _ _ hκ
  exact (Equiv.ofBijective (Etale.supportedClassMap P.Coefficient i (L := L))
    (Etale.supportedClassMap_bijective P.Coefficient i L)).symm hD

/-- L1: the class is minus the canonical Cartier class cD, hence the positive
local Kummer boundary cl. Source: lem-pur-divisor-class(b)
(blueprint: thm-pur-localized-top-chern, L1). -/
def LocalizedTopChernStatementLine (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules)
    [F.IsFiniteLocallyFreeOfRank 1] (s : F.sections)
    (hs : IsRegularSection P T a F 1 s),
  ∃ hc : IsClosedImmersion (regularSectionZeroProjection P T a F 1 s),
    letI := hc
    ∃ hI : (regularSectionZeroProjection P T a F 1 s).ker.IsInvertible,
    ∃ cD : localizedTopChernDivisorHom P.Coefficient
        (regularSectionZeroProjection P T a F 1 s),
      cD = localizedTopChernCartierSupportedMap P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates
        (regularSectionZeroProjection P T a F 1 s) (P.localizedTopChernTateIso T a 1)
        (Etale.geoCartierEtaleClass P.Coefficient P.diagonalExponent
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
          P.diagonalExponent_annihilates (regularSectionZeroProjection P T a F 1 s)
          hI (P.diagonalExponent_isUnit a)) ∧
      P.localizedTopChernSupported a (regularSectionZeroProjection P T a F 1 s)
        1 (c a F 1 s hs) = -cD

/-- Forgetting support gives the signed ordinary top Chern class.  The signed
form is the coefficient-level expression of `(-1)^r c_r(F)=c_r(F^vee)`.
Source: L4 and the splitting principle in proof Step 6
(blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernStatementForgetSupport (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections)
    (hs : IsRegularSection P T a F r s),
  ∃ hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s),
    @functorialCupForget P true _ _ (regularSectionZeroProjection P T a F r s)
      hc (2 * (r : ℤ)) r (c a F r s hs) =
        ((-1 : ℤ) ^ r) • P.localizedChernOrdinary a F r

/-- On each trivializing étale frame the canonically transported class restricts
to the ordered positive Kummer boundary product. Source: def-pur-frame-class
(blueprint: thm-pur-localized-top-chern, local-frame clause). -/
def LocalizedTopChernStatementFrameFormula (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k)) [IsSeparated a]
    [LocallyOfFiniteType a] [QuasiCompact a] (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections)
    (hs : IsRegularSection P T a F r s),
    ∃ hc : IsClosedImmersion (regularSectionZeroProjection P T a F r s),
      letI := hc
      letI := P.localizedTopChernInvertibleExponent a
      ∀ Ff : (regularSectionZeroProjection P T a F r s).EtaleFrame r,
        Etale.frameRestriction P.Coefficient Ff
          (P.localizedTopChernSupported a (regularSectionZeroProjection P T a F r s)
            r (c a F r s hs)) = Etale.frameClass P.Coefficient Ff

/-- The four laws and the local frame formula for the same family of classes.
Source: L1--L4 and the final display (blueprint: thm-pur-localized-top-chern). -/
def LocalizedTopChernStatementLaws (P : PurityFiniteSetting.{u})
    (c : P.LocalizedTopChernClasses) : Prop :=
  P.LocalizedTopChernStatementForgetSupport c ∧
    P.LocalizedTopChernStatementLine c ∧
      P.LocalizedTopChernBaseChange c ∧
        P.LocalizedTopChernDirectSum c ∧
          P.LocalizedTopChernStatementFrameFormula c

/-- The canonical localized top Chern family of a regular section.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
thm-pur-localized-top-chern.md` and its `.proof.md`
(blueprint: thm-pur-localized-top-chern).

The six DAG proof steps, with their cited inputs, are as follows.

1. Use `def-pur-supported-class-operations` to read the group as supported Hom.
Pull back to `def-pur-complete-flag-bundle`. The degree-zero summand of the
iterated `thm-pur-projective-bundle-formula`, with the projection formula,
gives the retraction of `lem-pur-flag-pullback-injective`, both with support
Z(s) and with full support.
2. On the flag bundle, successively take the positive localized Kummer classes
of the induced line sections and cup them, using
`def-pur-supported-class-operations` and `def-coefficient-twists-detailed`.
By `lem-pur-divisor-class`, each factor forgets to minus the first Chern class
of its line quotient. `lem-pur-supported-cup-functoriality`,
`lem-pur-chern-flag-formula`, `def-pur-chern-classes`, and
`lem-pur-kummer-additivity` identify the product with the signed top Chern
class and the top Chern class of the dual filtration.
3. Use `def-pur-vector-bundle-zero-section` in the universal case. The
etale-origin localization triangle of `lem-pur-support-localization-triangle`
and `cor-pur-affine-space-zero-section-purity` give vanishing below degree 2r.
Then `lem-pur-supported-bottom-gluing` makes the bottom supported group a
sheaf on the base. Glue the coordinate Kummer products from
`def-pur-frame-class`; their restrictions agree by
`lem-pur-supported-cup-functoriality` and `lem-pur-frame-independence`.
4. Pull this universal class back by the section-as-total-space-map of
`def-pur-vector-bundle-zero-section`.
`lem-pur-supported-hom-pullback` identifies it with the displayed morphism.
Functoriality of Kummer classes, the individual support boundaries of
`def-pur-support-cohomology`, and the supported cup product gives the stated
local frame formula.
5. Compare on the pulled-back vector bundle over the complete flag bundle.
The universal filtration splits Zariski locally. Both classes are then frame
classes of adapted coordinates, so `lem-pur-frame-independence` and
`lem-pur-supported-bottom-gluing` identify them. Pulling back by the section
and using `lem-pur-flag-pullback-injective` identifies the general class with
the unique preimage of the class of Step 2.
6. Check the laws after this injective flag pullback. In rank one the positive
boundary is cl(Z(s)), whereas the canonical Cartier supported class is
cD = -cl(Z(s)), by `lem-pur-divisor-class`. Base change pulls back the flag
and the local Kummer construction, also for every base change of the
universal tautological section. For a transverse direct sum use the product
of the two complete flag bundles and the concatenated filtration; cup
associativity and `lem-pur-kunneth-supported` give L3. Finally Step 2 and
ordinary pullback injectivity give L4, with sign (-1)^r; the dual Chern roots
are the negatives of the original roots. The local formula is Step 4.
-/
theorem localized_top_chern_statement (P : PurityFiniteSetting.{u}) :
    ∃ c : P.LocalizedTopChernClasses, P.LocalizedTopChernStatementLaws c := by
  obtain ⟨c, hbase, hframe⟩ := localizedTopChernKummerFamily_exists P
  obtain ⟨hforget, hline, hsum⟩ := localizedTopChernKummerFamily_laws P c hbase hframe
  exact ⟨c, hforget, hline, hbase, hsum, hframe⟩

end WeilConjectures.PurityFiniteSetting
