/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import Submission.WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import Submission.WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import Submission.WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import Submission.WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import Submission.WeilConjectures.CategoryTheory.FlatScalarUnit
import Submission.WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import Submission.WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import Submission.WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Submission.WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import Submission.WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.AlgebraicGeometry.Scheme
import Submission.WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerScalarOfSource

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Derived scalar extension of the supported Kummer boundary

Source: blueprint lem-amb-cartier-kummer-map; Stacks 03PL and 0A45
(blueprint: lem-asd-supported-kummer-boundary-scalar).
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
Source: Stacks 07A4, 03PL; blueprint lem-amb-cartier-kummer-map, final paragraph
(blueprint: lem-asd-supported-kummer-boundary-scalar).

Proof: the supported constant over Z/N has geometric stalk Z/N on D and zero off
D, so its degree-zero complex is K-flat. Its derived extension to A is i_* A_D,
with coefficient unit r mapped to its image in A. The etale roots line is locally
free of rank one over Z/N. Thus its derived extension is the ordinary root tensor
line over A, and the unit sends a pure tensor r tensor z to its coefficient image
tensor z. These give both unbounded scalar-unit universal properties, without
assuming A flat over Z/N. Applying the derived scalar-extension functor to the
relative torsor Kummer boundary produces the relative boundary over A: the torsor
extension and abelian Kummer boundary are unchanged and the root map is extended
on pure tensors. The relative boundary uniquely determines its Ext representative.
The resulting functoriality square is exactly SupportedKummerScalar. -/
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
