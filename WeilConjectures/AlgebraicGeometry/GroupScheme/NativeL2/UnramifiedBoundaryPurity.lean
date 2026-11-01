/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Complex.Basic
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.PointCount
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
public import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
public import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.GroupTheory.WeilGroup
public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.RingTheory.Etale.Field
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.CategoryTheory.Filtered.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.DescendFinite
public import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Purity at an unramified boundary point

Source: latest blueprint, sec-purity-real-sheaves/sk-cor-wrp-unramified-purity,
_section.md and sk-cor-wrp-unramified-purity.proof.md
(blueprint: sk-cor-wrp-unramified-purity).

The coefficient sheaf, Weil module, ordinary direct image, local operator and purity
predicate are the published condensed constructions. Inertia is the residue-action
kernel in the recorded henselian local data, evaluated by the normalized fibre paths.
All local data below are taken on the geometric curve, where they compute the same
inertia action as at the arithmetic boundary point. Scalar lifts only change universes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {U₀ C₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom]

/-- A lisse Weil sheaf on the whole smooth geometrically connected curve is pure
when its restriction to a dense open is pure. Restriction uses the canonical
pullback compositor for the Frobenius square, including the original Weil map.

Source: latest blueprint, sk-cor-wrp-unramified-purity, consequence
(blueprint: sk-cor-wrp-unramified-purity).

Proof: the geometric curve is integral. A dense open has finite closed complement;
remove all but one boundary point and apply the first assertion on that subcurve.
The ordinary image of the restriction of a lisse sheaf is the original sheaf.
The invariant-stalk formula and constant lisse rank show that its inertia-invariant
subspace has full dimension, hence inertia acts trivially. The first assertion
therefore proves purity at the chosen boundary point. On the open, purity is the
hypothesis. Treating each missing point proves purity everywhere, including an empty
boundary and the zero-rank case. -/
theorem pure_of_pure_dense_open
    [IsSeparated C₀.hom] [SmoothOfRelativeDimension 1 C₀.hom]
    [GeometricallyConnected C₀.hom]
    (_hl : l ≠ D.p) (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l C₀)
    (_hM : CondensedRing.LocallyFree
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber C₀).left) M.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (_hpure : Pure D l U₀
      ((Endofunctor.IsoAlgebra.mapOfNatIso
        (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
          (frobeniusSquare D j₀)).symm).obj M) iota w) :
    Pure D l C₀ M iota w := by
  sorry

end WeilConjectures.NativeL2
