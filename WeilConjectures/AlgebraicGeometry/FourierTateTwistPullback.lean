/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SecSmoothPurity.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.TateTwistLocallyFree
import WeilConjectures.Algebra.Homology.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback
import WeilConjectures.AlgebraicGeometry.AmbRootTowerPullbackCoherence
import WeilConjectures.AlgebraicGeometry.WfTateTwist
import WeilConjectures.AlgebraicGeometry.CondensedWeilModules


/-! # Tate-line pullback in the Fourier square

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion,
prop-base-linear.proof.md, paragraph (2) (blueprint: lem-fd-tate-twist-pullback).

All objects and Frobenius structures are the landed `StrictWeil` constructions.
Positive comparisons are the normalized `LinePullCoordinates.power`; negative
comparisons are their inverse transposes. Their invertibility is a conclusion.

## Main definitions and statements

* `coordinates`, `negativeComparison`, `comparison`: canonical ordinary signed maps.
* `derivedComparison`, `derivedSquare`: their exact derived images and the square.
* `WeilCompatible`: invertibility and the strict Weil morphism equation.
* `fiberMap`, `geometricPrimeInvertible`: the finite-field specialization.
* `fourier_tate_twist_pullback`: compatibility for both Fourier structure maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.WfCondensedTate

open CondensedRing PurityTransport

/-- The existing root-normalized coordinates, including their projection, scalar
and tensor normalization equations. No root frame is chosen.
Source: paragraph (2), root pullback (blueprint: lem-fd-tate-twist-pullback). -/
def coordinates (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] : LinePullCoordinates ell c f :=
  Classical.choice (linePullCoordinates_nonempty ell c f)

/-- Evaluation-transpose comparison followed by the coefficient-unit map and the
contravariant image of the inverse positive comparison. This is the same composite
as the negative branch of `StrictWeil.tatePull`, without presupposing invertibility
of the internal-Hom comparison for an arbitrary scheme morphism.
Source: paragraph (2), negative twists (blueprint: lem-fd-tate-twist-pullback). -/
def negativeComparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (e : (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y (n + 1)) ≅
      c.line ell X (n + 1)) :
    (CondensedRing.upperStar (c.obj ell) f).obj (StrictWeil.tateLine ell c Y (.negSucc n)) ⟶
      StrictWeil.tateLine ell c X (.negSucc n) := by
  let F := CondensedRing.upperStar (c.obj ell) f
  let L := c.line ell Y (n + 1)
  let M := c.line ell X (n + 1)
  let a : F.obj ((ihom L).obj (𝟙_ _)) ⟶ (ihom (F.obj L)).obj (F.obj (𝟙_ _)) :=
    (Functor.LaxMonoidal.ihomComparison F L).natTrans.app (𝟙_ _)
  let b : (ihom (F.obj L)).obj (F.obj (𝟙_ _)) ⟶ (ihom (F.obj L)).obj (𝟙_ _) :=
    (ihom (F.obj L)).map (Functor.Monoidal.εIso F).inv
  let d : (ihom (F.obj L)).obj (𝟙_ _) ⟶ (ihom M).obj (𝟙_ _) :=
    ((MonoidalClosed.internalHom.mapIso e.symm.op).app (𝟙_ _)).hom
  exact a ≫ b ≫ d

/-- Canonical signed comparison on the existing Tate lines. Nonnegative powers
are the normalized power coordinates, whose normalization includes the unit and
monoidal recursion; the negative branch is the evaluation inverse transpose.
Source: paragraph (2), all integer twists (blueprint: lem-fd-tate-twist-pullback). -/
def comparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    (m : ℤ) → (CondensedRing.upperStar (c.obj ell) f).obj (StrictWeil.tateLine ell c Y m) ⟶
      StrictWeil.tateLine ell c X m
  | .ofNat n => ((coordinates ell c f).power n).hom
  | .negSucc n => negativeComparison ell c f n ((coordinates ell c f).power (n + 1))

/-- Exact localization of the ordinary signed comparison, using the canonical
single-functor comparison. Both objects are literally `StrictWeil.derivedTateLine`.
Source: paragraph (2), derived Tate pullback (blueprint: lem-fd-tate-twist-pullback). -/
def derivedComparison (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (m : ℤ) :
    (CondensedRing.upperStar (c.obj ell) f).mapDerivedCategory.obj
      (StrictWeil.derivedTateLine ell c Y m) ⟶ StrictWeil.derivedTateLine ell c X m :=
  ((CondensedRing.upperStar (c.obj ell) f).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map (comparison ell c f m)

/-- The canonical ringed square already supplied by condensed coefficient pullback,
exactly localized; its compositors include the structural coefficient transport.
Source: paragraph (2), composite pullbacks (blueprint: lem-fd-tate-twist-pullback). -/
def derivedSquare (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ΦX : X ≅ X) (ΦY : Y ≅ Y)
    (h : ΦX.hom ≫ f = f ≫ ΦY.hom) :
    (CondensedRing.upperStar (c.obj ell) f).mapDerivedCategory ⋙ StrictWeil.action (c.obj ell) ΦX ≅
      StrictWeil.action (c.obj ell) ΦY ⋙
        (CondensedRing.upperStar (c.obj ell) f).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (CondensedRing.upperStarSquareComparison (c.obj ell) (⟨h.symm⟩ : CommSq f ΦX.hom ΦY.hom f))

/-- For every integer the canonical map is invertible and satisfies precisely the
morphism equation of the landed strict Weil pairs. The two tau maps are the actual
`StrictWeil.tateDatum`, with no newly chosen Weil structure.
Source: paragraph (2), Weil compatibility (blueprint: lem-fd-tate-twist-pullback). -/
def WeilCompatible (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ΦX : X ≅ X) (ΦY : Y ≅ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)]
    (h : ΦX.hom ≫ f = f ≫ ΦY.hom) : Prop :=
  ∀ m : ℤ, IsIso (derivedComparison ell c f m) ∧
    (StrictWeil.action (c.obj ell) ΦX).map (derivedComparison ell c f m) ≫
        (StrictWeil.tateDatum ell c ΦX m).hom =
      (derivedSquare ell c f ΦX ΦY h).hom.app (StrictWeil.derivedTateLine ell c Y m) ≫
        (CondensedRing.upperStar (c.obj ell) f).mapDerivedCategory.map
          (StrictWeil.tateDatum ell c ΦY m).hom ≫ derivedComparison ell c f m

/-- Base change of an actual morphism over the finite field to its fixed closure.
Source: Fourier square, structure morphisms p and p'
(blueprint: lem-fd-tate-twist-pullback). -/
def fiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Invertibility of the coefficient prime follows from its distinction from p;
it is not an additional hypothesis on the Fourier schemes.
Source: finite-field conventions in paragraph (2)
(blueprint: lem-fd-tate-twist-pullback). -/
instance geometricPrimeInvertible (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ D.p)]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    ∀ x : (D.geometricFiber X₀).left,
      Invertible (ℓ : (D.geometricFiber X₀).left.residueField x) :=
  fun x ↦ WeilConjectures.sfWeilPrimeInvertible D ℓ Fact.out X₀ x

/-- The two canonical signed Tate pullback maps are isomorphisms of the existing
strict Weil complexes. Their positive and negative normalizations are fixed by
`comparison`; the two Weil structures are exactly `StrictWeil.tateDatum`.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion,
prop-base-linear.proof.md, paragraph (2) (blueprint: lem-fd-tate-twist-pullback).

Proof:
1. Use the native coefficient E and the root lines of [sk-def-sp-tate-twist], with
   the strict Weil data of [sk-def-sf-weil-complexes]. The prime is invertible on
   each geometric fibre. Pullback is the exact module functor of
   [det-def-sfb-module-pushforward-pullback] and
   [det-prop-sfb-module-pullback-exact-main].
2. The root maps and their transition equations give the integral comparison;
   scalar extension gives the rational first comparison. These are exactly the
   coordinates of [def-pur-transport-line-pullback], retaining their finite
   projection and scalar normalization. Cartesian coefficients and twists are
   [sk-prop-sfb-cartesian-coefficients] and
   [det-prop-sfb-cartesian-coefficients-twists]. The internal encoding agrees by
   [lem-sfb-internal-module-operations-transport].
3. On the primitive-root cover of [det-def-sp-tate-twist-locally-free] the lines
   are free of rank one. [lem-pur-line-unbounded-derived-tensor] and
   [lem-sf-ringed-derived-tensor-hom-adjunction] identify the ordinary dual with
   the derived dual. They are constructible of Tor amplitude [0,0], as in
   [sk-def-sfb-constructible] and the landed StrictWeil.tate_mem.
4. The power_normalized field gives the unit and ordered tensor recursion via
   [lem-sfb-ringed-derived-monoidal-comparisons]. Thus the nonnegative branches
   are canonical isomorphisms with precisely the prescribed tensor normalization.
5. The evaluation transpose is an isomorphism on the locally free positive line
   by [lem-pur-ringed-site-finite-free-dual-pullback]. Its composite with the unit
   map and the inverse positive map is negativeComparison. This is the inverse
   transpose required by the source, and proves invertibility in every negative
   degree. Exact localization gives the displayed derived isomorphisms.
6. The model Frobenius maps commute with either base-changed structure morphism
   by the fibre-product projections. The coefficient mate-composition equation
   [lem-sfb-eta-comp] identifies the ringed composites. The existing upperStar
   square, followed by exact localization, is therefore the canonical square.
7. At finite root levels the square commutes by
   [lem-amb-root-tower-pullback-coherence]; limits and scalar extension preserve
   it. These are the very maps defining StrictWeil.tateDatum, rather than maps
   related only by an unspecified isomorphism. Degree zero is its unit equation.
8. Tensor bifunctoriality extends the equation to positive powers. Evaluation
   against the positive line reduces the negative equation to the same unit
   equation; a local rank-one frame detects equality. This is exactly the
   contragredient normalization in [sk-def-sf-weil-complexes].
9. Apply these constructions to both p and p'. Every constituent is canonical
   and natural. The equality in WeilCompatible is the strict-pair morphism
   equation, so the invertible comparisons and their inverses are Weil arrows.
   Restricting to the full constructible category gives the asserted strict Weil
   isomorphisms; their degree-zero interpretation is [def-weil-weil-sheaf-complex]. -/
theorem fourier_tate_twist_pullback
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (S₀ V₀ V'₀ : Over (Spec (.of D.k₀)))
    [IsSeparated S₀.hom] [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom]
    [IsSeparated V₀.hom] [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [IsSeparated V'₀.hom] [LocallyOfFiniteType V'₀.hom] [QuasiCompact V'₀.hom]
    (p₀ : V₀ ⟶ S₀) (p'₀ : V'₀ ⟶ S₀) :
    ∃ (hp : (StrictWeil.modelFrobenius D V₀).hom ≫ fiberMap D p₀ =
        fiberMap D p₀ ≫ (StrictWeil.modelFrobenius D S₀).hom)
      (hp' : (StrictWeil.modelFrobenius D V'₀).hom ≫ fiberMap D p'₀ =
        fiberMap D p'₀ ≫ (StrictWeil.modelFrobenius D S₀).hom),
      WeilCompatible ℓ (.rational E) (fiberMap D p₀)
        (StrictWeil.modelFrobenius D V₀) (StrictWeil.modelFrobenius D S₀) hp ∧
      WeilCompatible ℓ (.rational E) (fiberMap D p'₀)
        (StrictWeil.modelFrobenius D V'₀) (StrictWeil.modelFrobenius D S₀) hp' := by
  sorry

end AlgebraicGeometry.ProEtale.WfCondensedTate
