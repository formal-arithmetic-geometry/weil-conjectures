/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ContinuousUniverseLocalFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousCompletedLocalizationSquare
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Module.Lattice
import Mathlib.GroupTheory.QuotientGroup.Finite
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionEquivalence
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedSystemData
import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedPointwiseComparison
import Mathlib.Tactic.Choose
import WeilConjectures.AlgebraicGeometry.SmoothLisseIntegralLattice
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedSpectralLattices
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ContinuousScalarEncodingUniverses
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# A lattice on the geometric fibre

This is the geometric-fibre part of the lattice-neighbourhood argument.  The statement records
only the lattice on the geometric fibre; extending it over the base is a separate theorem.
Source: latest blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity,
Step 1, paragraphs on the regular normal fibre and the lattice scheme.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood-fibre)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The data supplied by the lattice-scheme construction on a geometric fibre. -/
structure SmoothFibreLatticeWitness
    {R A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj A] [IsCommMonObj R] [IsCommMonObj A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (a : A ⟶ R) [IsMonHom a] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : Type _ where
  M : Mod (Sheaf (Scheme.ProEt.topology (pullback f barY)) Ab.{u + 1})
      (condensedRingObj A (pullback f barY))
  i : M ⟶ (Mod.comap (coefficientMap a (pullback f barY))).obj
      ((CondensedRing.upperStar R (pullback.fst f barY)).obj L)
  lisse : IsLisseCoefficientModule A M
  mono : Mono i
  iso : IsIso (((Mod.extendRestrictAdjunction
      (coefficientMap a (pullback f barY))).homEquiv M
      ((CondensedRing.upperStar R (pullback.fst f barY)).obj L)).symm i)

end AlgebraicGeometry.ProEtale
