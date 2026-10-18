/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.Paper.CompletedExtensionZeroComparison
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.Paper.IntrinsicCompletionCompleted
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.Paper.ExactFunctorDerivedLimit
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Algebra.Homology.RoosComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf
import Sheaf.Paper.ConstantCompletionEquivalence

/-! # Completed open exchange on the shared pullback presentation

Source: blueprint order 1587; Stacks Tags 03DI, 09BP and 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).

The old open exchange is retained. Its transport to `d.completedPull` is induced
by the actual coefficient maps and universal derived counits on strict towers.
The completion-unit equation retains its ordinary adjoint-mate normalization.

## Main definitions

- `cbcDatumCompletedTransport`: the normalized comparison of pullback presentations.
- `cbcDatumCompletedExchange`: completed open exchange on `d.completedPull`.

## Main statements

- `completedOpenExchangeComparison`: invertibility and all completeness assertions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {S T : Scheme.{t}} (h : S ⟶ T)

/-- Both finite coefficient maps are induced by the same constant-section map.
Source: Stacks 099N, finite reductions (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: expand finiteRingIso and completedFiniteCoefficientMap. Their outer maps
are the same constant/function comparisons, and their middle map is the same
constant inverse-image comparison. Thus their composites agree. -/
theorem cbcDatumFiniteCoefficient_eq (n : ℕ) :
    completedFiniteCoefficientMap h d n = (d.finiteRingIso h n).hom := by
  sorry

/-- The completed scalar structures coincide, with every quotient projection retained.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: both maps are limit lifts. After the n-th projection they are inverse
image of that projection followed by the finite map of cbcDatumFiniteCoefficient_eq.
Joint monicity of the limit projections gives equality. Naturality in every
quotient transition is the finite constant-comparison naturality square. -/
theorem cbcDatumCoefficient_eq :
    completedCoefficientMap h d = (d.integralRingIso h).hom := by
  sorry

/-- Both ordinary functors use identical inverse image and sheafified tensor data.
Source: Stacks 03EK, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: use cbcDatumCoefficient_eq. The recorded scalar-extension object formula
identifies every object with changeOfRings; its recorded map formula identifies
every map with changeOfRingsHom after the object equality transports. Functor
extensionality gives the equality. These formulas fix the tensor unit 1 tensor x. -/
theorem cbcDatumModulePull_eq :
    completedModulePullback h d =
      proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h) := by
  sorry

/-- Strict tower functors agree on levels AND transition maps.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: whisker cbcDatumModulePull_eq by the identity on the entire strict tower
category. Both constructions apply that module functor to every transition,
including the actual quotient maps of the reduction tower. -/
theorem cbcDatumTowerModulePull_eq :
    completedTowerModulePullback h d = d.towerModulePull h := by
  sorry

/-- The module comparison on actual complexes, with the additive structures installed.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: substitute cbcDatumModulePull_eq; preservation of zero morphisms is a
proposition, so its two instance witnesses coincide. The mapped complexes agree. -/
theorem cbcDatumModulePullComplex_eq
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj P =
      ((proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
        (d.integralRingIso h)).mapHomologicalComplex (.up ℤ)).obj P := by
  sorry

/-- The strict comparison on complexes keeps all levels and transitions.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: substitute cbcDatumTowerModulePull_eq. The zero-preservation witnesses
are proof irrelevant, so the mapped strict tower complexes agree. -/
theorem cbcDatumTowerPullComplex_eq
    (P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) :
    ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).obj P =
      ((d.towerModulePull h).mapHomologicalComplex (.up ℤ)).obj P := by
  sorry

/-- The ordinary derived comparison is uniquely fixed by its resolving counit.
Source: Stacks 099N, 06YS (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the ordinary functors coincide by cbcDatumModulePull_eq. The datum
presentation is exact, so its termwise factorization is a universal left-derived
counit. Uniqueness of the universal derived pair gives the isomorphism and the
displayed counit equation on complexes. Resolve by K-flat complexes to prove
uniqueness; exactness extends the equation to every representative. -/
theorem cbcDatumOrdinaryTransport_exists :
    ∃! e : completedOrdinaryPullback h d ≅ d.pull h,
      ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (proEtaleRingModulePullback h (d.completedRing T) (d.completedRing S)
              (d.integralRingIso h)).mapDerivedCategoryFactors.hom.app P =
          completedOrdinaryPullbackComplexCounit h d P ≫
            DerivedCategory.Q.map
              (eqToIso (cbcDatumModulePullComplex_eq d h P)).hom := by
  sorry

/-- Ordinary pullback transport with its universal-counit normalization.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumOrdinaryTransport : completedOrdinaryPullback h d ≅ d.pull h :=
  (cbcDatumOrdinaryTransport_exists d h).exists.choose

/-- The strict derived tower comparison retains the universal resolving counit.
Source: Stacks 099N, 06YS (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: cbcDatumTowerModulePull_eq identifies the whole ordinary tower functor.
Its exact termwise derived functor and the objectwise K-flat derived construction
are universal left-derived pairs. Their unique comparison satisfies the equation
below. In particular it compares one strict tower, including transitions, rather
than choosing independent isomorphisms of its finite evaluations. -/
theorem cbcDatumTowerTransport_exists :
    ∃! e : completedTowerPullback h d ≅ d.towerPull h,
      ∀ P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (d.towerModulePull h).mapDerivedCategoryFactors.hom.app P =
          completedTowerPullbackComplexCounit h d P ≫
            DerivedCategory.Q.map
              (eqToIso (cbcDatumTowerPullComplex_eq d h P)).hom := by
  sorry

/-- Canonical comparison of derived strict tower pullback presentations.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumTowerTransport : completedTowerPullback h d ≅ d.towerPull h :=
  (cbcDatumTowerTransport_exists d h).exists.choose

/-- Apply Rlim to the strict tower transport of the very same reduction functor.
The inverse-limit functors in the two interfaces are definitionally identical.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumCompletedTransport : cbcCompletedPullback d h ≅ d.completedPull h :=
  isoWhiskerLeft (completedReductionTower T d)
    (isoWhiskerRight (cbcDatumTowerTransport d h) (completedTowerRlim d S))

/-- The current recorded strict completed pullback has the same normalized transport.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
abbrev cbcDatumActualStrictTransport :
    pbcActualStrictCompletedPull d h ≅ d.completedPull h :=
  cbcDatumCompletedTransport d h

/-- The transport preserves the actual ordinary-to-completed quotient unit.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: expand both units into constant-tower/Rlim unit, constant-pullback
comparison and strict quotient augmentation. The constant-tower comparisons
are fixed by the same ordinary and tower counits. The quotient augmentation
sends x to 1 tensor x on both sides by cbcDatumModulePull_eq. The constant-limit
adjunction is fixed by compatible-family projections, so its unit agrees too.
Naturality and the derived counit equations then give the displayed identity.
This argument retains all quotient transitions and applies to ambient inputs. -/
theorem cbcDatumCompletedTransport_unit (K : d.derived T) :
    (cbcCompletedPullbackComparison d h).app K ≫
        (cbcDatumCompletedTransport d h).hom.app K =
      (cbcDatumOrdinaryTransport d h).hom.app K ≫ d.ordinaryToCompleted h K := by
  sorry

/-- The currently recorded strict-tower unit obeys the same normalization.
Source: Stacks 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: expand pbcActualStrictCompletedPullUnit and the old comparison. Both are
the same constant-tower unit followed by the same normalized constant-pullback
comparison and the same strict quotient augmentation. Functor associativity
identifies their components. Apply cbcDatumCompletedTransport_unit. -/
theorem cbcDatumActualStrictTransport_unit (K : d.derived T) :
    (pbcActualStrictCompletedPullUnit d h).app K ≫
        (cbcDatumActualStrictTransport d h).hom.app K =
      (cbcDatumOrdinaryTransport d h).hom.app K ≫ d.ordinaryToCompleted h K := by
  sorry

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

/-- Ordinary exchange transported with the universal counits; hence it is the
same generator-normalized adjoint mate as the retained ordinary exchange.
Source: Stacks 03DI, 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumOrdinaryExchange :
    cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ d.pull g ⟶
      d.pull gU ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  whiskerLeft (cbcDerivedOpenShriek d j sq.isOpenImmersion)
      (cbcDatumOrdinaryTransport d g).inv ≫
    cbcOrdinaryExchange d sq ≫
      whiskerRight (cbcDatumOrdinaryTransport d gU).hom
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion')

/-- Canonical completed open exchange on the same presentation as proper exchange.
It is Rlim of the finite exchange followed by the extension/Rlim comparison,
transported through the strict tower counits, with no new endpoint choice.
Source: Stacks 09BP, 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDatumCompletedExchange [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    (cbcCompleteProperty d U r a ha).ι ⋙
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ d.completedPull g ⟶
      (cbcCompleteProperty d U r a ha).ι ⋙ d.completedPull gU ⋙
        cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  whiskerLeft ((cbcCompleteProperty d U r a ha).ι ⋙
      cbcDerivedOpenShriek d j sq.isOpenImmersion)
      (cbcDatumCompletedTransport d g).inv ≫
    cbcCompletedExchange d sq r a ha ≫
      whiskerLeft (cbcCompleteProperty d U r a ha).ι
        (whiskerRight (cbcDatumCompletedTransport d gU).hom
          (cbcDerivedOpenShriek d j' sq.isOpenImmersion'))

/-- The shared-presentation exchange retains its ordinary adjoint-mate normalization.
Source: Stacks 03DI, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: substitute the three factors of cbcDatumCompletedExchange. Apply the unit
identity for each horizontal arrow and naturality for the open extension.
The old exchange unit equation cancels the intermediate transport and yields
exactly the displayed equation with the ordinary transported adjoint mate. -/
theorem cbcDatumCompletedExchange_unit [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory) :
    d.ordinaryToCompleted g
        ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ≫
        (cbcDatumCompletedExchange d sq r a ha).app K =
      (cbcDatumOrdinaryExchange d sq).app K.obj ≫
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          (d.ordinaryToCompleted gU K.obj) := by
  sorry

/-- Quasi-compact open extension preserves intrinsic completeness, and its canonical
completed exchange is invertible and natural, with both sides intrinsically complete.
Source: blueprint order 1587; Stacks 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
Proof:
1. Use lem-weil-proetale-weakly-etale-localization and sectionwise module limits
to identify completed rings on both slices by every finite projection.
lem-pc-quasi-compact-base-change makes the second open quasi-compact.
2. lem-pur-site-restriction-module-adjunction-exact gives exact sheafified
extension and restriction; lem-sf-exact-functor-derived-triangulated descends
them termwise. Scalar restriction leaves the direct-sum summands unchanged.
3. lem-pc-kflat-resolution and lem-weil-pbc-ringed-slice-extension-tensor show
that extension preserves K-flat complexes and identifies strict reductions,
including every quotient transition, by the same pure tensor formula.
4. lem-weil-pbc-proetale-ringed-open-closed expresses extension as a kernel of
product-preserving functors. Closed inverse image preserves products by
lem-weil-pbc-proetale-immersion-limit-preservation, including the empty product.
5. Exact countable products and lem-weil-derived-limit-products-core give the
functorial signed Roos fiber. prop-weil-pbc-rlim-functoriality and
lem-weil-derived-limit-roos-complex identify it with the specified Rlim.
Extension commutes with its two products and structure maps, as required by
lem-cbc-exact-functor-rlim and the ringed strict tower homotopy-limit lemma.
6. Apply that comparison to the finite-free Koszul tower and its unit from
def-weil-pbc-intrinsic-completion to preserve completeness. Use
lemma-weil-pbc-completed-pullback-reduction for completeness of pullback.
7. prop-weil-pbc-proetale-constant-exact and
lem-cbc-proetale-extension-zero-base-change give finite adjoint-mate exchanges.
The summand and scalar-restriction formulas and site-morphism composition show
they commute with quotient transitions. Constant/completed finite comparisons
from lem-weil-pbc-constant-completion-equivalence retain those transitions.
8. Apply functorial Rlim to that strict tower exchange and the inverse
extension/Rlim comparison. This is the old canonical completed exchange.
Transport it by cbcDatumCompletedTransport, which retains coefficients,
transitions, resolving counits and quotient units. Its mate normalization is
cbcDatumCompletedExchange_unit. Completeness is invariant under these
isomorphisms; the two applications of step 6 give the displayed complete
endpoints. All constituents are natural, so their composite is natural. -/
theorem completedOpenExchangeComparison [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    IsIso (cbcDatumCompletedExchange d sq r a ha) ∧
      (∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        cbcCompleteProperty d X r a ha
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
          cbcCompleteProperty d X' r a ha
            ((d.completedPull g).obj
              ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
              ((d.completedPull gU).obj K.obj))) := by
  sorry

end AlgebraicGeometry.Scheme
