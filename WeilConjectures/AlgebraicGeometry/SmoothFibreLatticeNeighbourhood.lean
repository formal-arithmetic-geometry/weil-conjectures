/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.AlgebraicGeometry.StratifiedLatticeScheme
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.RegularNormalDecomposition

/-!
# An integral lattice over a smooth proper fibre neighbourhood

Source: latest Weil blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity/
prop-zl-smooth-proper-relative-purity.proof.md, Step 1, Lattices etale-locally on Y.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood)

The coefficient abbreviations specialize the existing continuous-map construction to the
canonical spectral topology. Integral coefficients are the recorded `sfbCondensedIntegers`.
The lattice is an actual monomorphism. Its scalar-extension map is its adjoint under the
existing extension/restriction adjunction, so it is induced by this very inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace SmoothFibreLattice

/-- Continuous rational coefficients with the canonical extending absolute value.
Source: latest blueprint, smooth-proper relative purity, Step 1, lattice paragraph.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood) -/
abbrev rational (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.continuousMapRingObjOfUniverse E

/-- The canonical ring-sheaf multiplication, specialized to the coefficient field.
Source: latest blueprint, smooth-proper relative purity, Step 1, lattice paragraph.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood) -/
instance rationalMonObj (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : MonObj (rational l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse E)

/-- Commutativity inherited from the existing continuous coefficient construction.
Source: latest blueprint, smooth-proper relative purity, Step 1, lattice paragraph.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood) -/
instance rationalComm (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : IsCommMonObj (rational l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse E

/-- Commutativity of the recorded integral coefficients, with their subspace topology.
Source: latest blueprint, smooth-proper relative purity, Step 1, lattice paragraph.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood) -/
instance integralComm (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    IsCommMonObj (sfbCondensedIntegers l E).X :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionIntegers l E)

/-- The continuous inclusion of the recorded integer ring into its coefficient field,
as the existing postcomposition morphism of condensed ring objects.
Source: latest blueprint, smooth-proper relative purity, Step 1, lattice paragraph.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood) -/
abbrev scalar (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (sfbCondensedIntegers l E).X ⟶ rational l E :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val

/-- The inclusion carries the canonical ring-object structures.
Source: latest blueprint, smooth-proper relative purity, Step 1, lattice paragraph.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood) -/
instance scalarMonHom (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] : IsMonHom (scalar l E) :=
  letI := spectralNorm.normedField ℚ_[l] E
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMapOfUniverse
      (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)

end SmoothFibreLattice

/-- Every geometric base point has a pointed etale neighbourhood on whose inverse image
there is an embedded lisse integral lattice. The scalar-extension isomorphism is the
adjoint of the specified inclusion, not an independently chosen rationalization.

Source: latest blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity/
prop-zl-smooth-proper-relative-purity.proof.md, Step 1, Lattices etale-locally on Y.
(blueprint: lem-zl-smooth-fibre-lattice-neighbourhood)

Proof plan, following the eight steps of the DAG node:
1. Finite type over k makes X Noetherian. The rank partition and the lattice-scheme
   theorem produce a separated etale scheme Q over X with universal lattice, representing
   the etale sheaf S of embedded lattices (det-lem-stratified-lattice-rank and
   det-lem-stratified-lattice-scheme).
2. At the given geometric point form the strict henselization T, its base change Z,
   and the canonical closed geometric fibre F over an algebraic closure of the residue
   field of T. The strict-local structure theorem makes T strictly henselian. Base
   change preserves smoothness and properness. Smooth affine charts over a field have
   regular local rings, so F is regular and Noetherian.
3. Regular-normal decomposition splits F into finitely many connected normal pieces.
   Pullback preserves the finite free local trivializations of L. On each nonempty piece
   thm-lisse-qlbar-representations (4) supplies a lattice. Glue on the disjoint pieces;
   use the unique zero module when F is empty.
4. In a pro-etale frame, the lattice scheme has the discrete lattice labels
   GL_r(E)/GL_r(A). The fibre lattice determines local sections with the same embedded
   images on overlaps. Subcanonicity glues them. Inverse image of representables identifies
   the result with a section of the etale inverse image of S on F.
5. Proper strict-henselian degree-zero comparison lifts this section from the canonical
   closed geometric fibre F to Z. The inverse-image composition isomorphism identifies
   the iterated restrictions compatibly with their adjunction units.
6. The proper map is quasi-compact and quasi-separated. The set-valued direct-image stalk
   theorem identifies this section on Z with a germ of f_* S at the original geometric
   point, without changing its algebraically closed field.
7. Represent the germ on a pointed etale neighbourhood V. The direct-image formula and
   the representing property of Q give the embedded lisse lattice on X times_Y V.
8. In each frame the inclusion is g A^r into E^r, so its scalar-extension map sends the
   integral basis g e_i to the same rational basis. It is locally, hence globally, an
   isomorphism. This includes rank zero, varying ranks and empty fibres. -/
theorem exists_smooth_fibre_lattice_neighbourhood
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l)
    {X Y : Scheme.{u}} (x : X ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k))
    [IsSeparated x] [LocallyOfFiniteType x] [QuasiCompact x]
    [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (f : X ⟶ Y) (_hf : f ≫ y = x) [Smooth f] [IsProper f]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (SmoothFibreLattice.rational l E) X))
    (_hL : IsLisseCoefficientModule (SmoothFibreLattice.rational l E) L)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Y) :
    ∃ (V : Y.Etale) (barV : Spec (.of Ω) ⟶ V.left), barV ≫ V.hom = barY ∧
      ∃ (L₀ : Mod (Sheaf (Scheme.ProEt.topology (pullback f V.hom)) Ab.{u + 1})
          (condensedRingObj (sfbCondensedIntegers l E).X (pullback f V.hom)))
        (i : L₀ ⟶ (Mod.comap (coefficientMap (SmoothFibreLattice.scalar l E)
          (pullback f V.hom))).obj
            ((CondensedRing.upperStar (SmoothFibreLattice.rational l E)
              (pullback.fst f V.hom)).obj L)),
        IsLisseCoefficientModule (sfbCondensedIntegers l E).X L₀ ∧ Mono i ∧
          IsIso (((Mod.extendRestrictAdjunction
            (coefficientMap (SmoothFibreLattice.scalar l E) (pullback f V.hom))).homEquiv
              L₀ ((CondensedRing.upperStar (SmoothFibreLattice.rational l E)
                (pullback.fst f V.hom)).obj L)).symm i) := by
  sorry

end AlgebraicGeometry.ProEtale
