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
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Category.MonCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.StratifiedLatticeScheme
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
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

end SmoothFibreLattice

end AlgebraicGeometry.ProEtale
