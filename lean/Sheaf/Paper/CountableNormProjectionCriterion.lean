/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.Paper.InternalScalarPullbackNormalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Analysis.NormedSpace.CountableUltrametricBasis
import Sheaf.LinearAlgebra.CountableEndomorphismModuleReconstruction
import Sheaf.Paper.ConstructibleNormedGeometricFibres

/-! # Countable-dimensional norm coefficient projection

Source: blueprint six-functors direct-images proof, paragraph (3), former
supported-lattice steps 5--7; agent-extracted endomorphism argument.
An exact published reference is wanted, not asserted by the blueprint.
(blueprint: lem-sfb-countable-norm-projection-criterion).

The coefficient sheaves use all continuous functions. The projection is the actual
geometric counit mate of the normalized ordinary unbounded scalar/pullback comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
open QuotientChange

/-- Postcomposition by the norm-compatible field inclusion, using all continuous maps.
Source: direct-images proof (3), A(P) to B(P)
(blueprint: lem-sfb-countable-norm-projection-criterion). -/
def countableNormCoefficientHom (E F : Type u) [NormedField E] [NormedField F]
    [NormedAlgebra E F] : (normContinuousRing E).X ⟶ (normContinuousRing F).X :=
  Profinite.continuousMapRingObjMapOfUniverse (algebraMap E F) (continuous_algebraMap E F)

/-- The inclusion uses the recorded pointwise ring-object structures.
Source: direct-images proof (3), coefficient inclusion
(blueprint: lem-sfb-countable-norm-projection-criterion). -/
instance countableNormCoefficientHom_isMonHom (E F : Type u)
    [NormedField E] [NormedField F] [NormedAlgebra E F] :
    IsMonHom (countableNormCoefficientHom E F) :=
  Profinite.isMonHom_continuousMapRingObjMapOfUniverse
    (algebraMap E F) (continuous_algebraMap E F)

/-- The balancing comparison specified by its universal computation-counit equation.
The existing normalization theorem determines its b component: on K-flat representatives
it is the ordinary balanced comparison, and resolutions determine it everywhere.
The other existential components of that theorem are not chosen as coefficient data.
Source: direct-images proof (3), canonical balanced tensor comparison
(blueprint: lem-sfb-countable-norm-projection-criterion). -/
def countableNormScalarPull (E F : Type u) [NormedField E] [NormedField F]
    [NormedAlgebra E F] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    D (countableNormCoefficientHom E F) Y ⋙ L (normContinuousRing F).X f ≅
      L (normContinuousRing E).X f ⋙ D (countableNormCoefficientHom E F) X :=
  letI : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (normContinuousRing E).X T) := fun T ↦
    have := IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (normContinuousRing E).X T)
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (normContinuousRing F).X T) := fun T ↦
    have := IsGrothendieckAbelian.of_equivalence
      (ModuleRingedComparison.equivalence (normContinuousRing F).X T)
    HasDerivedCategory.ofIsGrothendieckAbelian _
  ((internal_scalar_pullback_normalization
    (countableNormCoefficientHom E F) f).choose_spec).choose_spec.choose

/-- The specified beta: transpose the balancing map followed by scalar extension of
precisely the geometric counit. No arbitrary map or flatness assumption is introduced.
Source: direct-images proof (3), definition of beta
(blueprint: lem-sfb-countable-norm-projection-criterion). -/
def countableNormProjection (E F : Type u) [NormedField E] [NormedField F]
    [NormedAlgebra E F] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Modules (normContinuousRing E).X X)) :
    (D (countableNormCoefficientHom E F) Y).obj ((QuotientChange.F
      (normContinuousRing E).X f).obj K) ⟶
      (QuotientChange.F (normContinuousRing F).X f).obj
        ((D (countableNormCoefficientHom E F) X).obj K) :=
  (adj (normContinuousRing F).X f).homEquiv _ _
    ((countableNormScalarPull E F f).hom.app
        ((QuotientChange.F (normContinuousRing E).X f).obj K) ≫
      (D (countableNormCoefficientHom E F) X).map
        ((adj (normContinuousRing E).X f).counit.app K))

/-- Constant-model constructible images detect this specified coefficient projection,
and its target has no cohomology in a degree where the E-direct image vanishes.
Source: direct-images proof (3), former supported-lattice steps 5--7; agent-extracted
argument, with an exact published reference wanted
(blueprint: lem-sfb-countable-norm-projection-criterion).

Proof:
1. Apply lem-sfb-countable-normed-orthogonal-basis to F over E, prescribing b_0 = 1.
Its continuous first coordinate lambda has lambda(1) = 1. Put e(w) = lambda(w)1
in the algebra of continuous E-linear endomorphisms of F.
2. Lem-sfb-norm-coefficient-endomorphism-corner gives the canonical endomorphism
algebra action on the restricted N, and split maps M to N to M whose composite on
N is e. On fibres, M identifies with eH; the actual beta is v tensor h to theta_v h,
where theta_v(w) = lambda(w)v. Multiplication endomorphisms act by constant F-scalars.
3. Ultrametric balls are clopen, so both fields are totally disconnected. By
lem-sfb-constructible-normed-geometric-fibres, each degree-q target fibre H is
finite-dimensional over F. Countability of F over E makes H countably generated
over E. Apply lem-sfb-countable-endomorphism-module-reconstruction to identify
F tensor_E eH with H. This is exactly the cohomology-fibre map of beta by step 2.
4. If H^q(M) vanishes, eH vanishes, hence every fibre of H^q(N) vanishes by step 3.
Apply the bounded constructible conservativity of
lem-sfb-constructible-normed-geometric-fibres to H^q(N)[0] to conclude H^q(N) = 0.
This proves boundedness of N from that of M, before any conservativity on N is used.
5. Both endpoints are now bounded constant-model constructible. Step 3 makes every
derived fibre map invertible. Bounded constructible conservativity in
lem-sfb-constructible-normed-geometric-fibres makes the specified beta invertible.
No properness, finite-type, completeness of F, or coefficient-flatness is used. -/
theorem countableNormProjection_criterion
    (ℓ : ℕ) [Fact ℓ.Prime] (E F : Type u) [NormedField E] [NormedField F]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] [NormedAlgebra E F]
    (_hE : ∀ a : E, ‖a‖ = Padic.coefficientExtensionAbsoluteValue ℓ E a)
    (_hF : ∀ a b : F, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (_hcountable : ∃ s : ℕ → F, Submodule.span E (Set.range s) = ⊤)
    {X Y : Scheme.{u}} [CompactSpace Y] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (Modules (normContinuousRing E).X X))
    (_hM : constantModelBoundedConstructible (normContinuousRing E).X Y
      ((QuotientChange.F (normContinuousRing E).X f).obj K))
    (_hTM : constantModelBoundedConstructible (normContinuousRing F).X Y
      ((D (countableNormCoefficientHom E F) Y).obj
        ((QuotientChange.F (normContinuousRing E).X f).obj K)))
    (_hN : ∀ q : ℤ, IsConstantModelConstructible (normContinuousRing F).X Y
      ((DerivedCategory.homologyFunctor _ q).obj
        ((QuotientChange.F (normContinuousRing F).X f).obj
          ((D (countableNormCoefficientHom E F) X).obj K)))) :
    constantModelBoundedConstructible (normContinuousRing F).X Y
        ((QuotientChange.F (normContinuousRing F).X f).obj
          ((D (countableNormCoefficientHom E F) X).obj K)) ∧
      IsIso (countableNormProjection E F f K) ∧
      ∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((QuotientChange.F (normContinuousRing E).X f).obj K)) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((QuotientChange.F (normContinuousRing F).X f).obj
            ((D (countableNormCoefficientHom E F) X).obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale
