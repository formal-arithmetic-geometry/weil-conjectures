/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerScalarOfSource

/-!
# Derived scalar extension of the supported Kummer boundary

Source: Stacks 03PL and 0A45.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Match the stored instances of the boundary and scalar interfaces.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The normalized supported boundary over A is the derived scalar extension of
its normalized Z/N boundary, with the sectionwise coefficient maps.
Source: Stacks 07A4, 03PL. -/
theorem supported_kummer_boundary_scalar (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    [NeZero N]
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ)
    (κ₀ : Ext
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod N))) i).obj
        (ordinaryFiniteConstant (ULift.{u + 1} (ZMod N)) D))
      (Scheme.finiteEtaleTateLine T N (ULift.{u + 1} (ZMod N))
        (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
          (ZMod.natCast_self N))) 2)
    (hκ₀ : SupportedKummerBoundary (ULift.{u + 1} (ZMod N)) N
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
        (ZMod.natCast_self N)) i hI hT κ₀) :
    SupportedKummerScalar
      ((Scheme.finiteEtaleTwistScalar N A hA).comp ULift.ringEquiv.toRingHom) N
      (congrArg (ULift.up : ZMod N → ULift.{u + 1} (ZMod N))
        (ZMod.natCast_self N)) hA i κ₀ κ := by
  let R := ULift.{u + 1} (ZMod N)
  have hR : (N : R) = 0 :=
    congrArg (ULift.up : ZMod N → R) (ZMod.natCast_self N)
  let φ := supportedScalarMap N A hA
  obtain ⟨η, ηT, hη, hηT, huD, huI, huT, hnat⟩ :=
    supported_kummer_scalar_source T N hN A hA i
  exact supported_kummer_scalar_of_source φ T N hN hR hA hT i hI κ κ₀ hκ hκ₀ η hη huI

end AlgebraicGeometry.Etale
