/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
import Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor
import Sheaf.Paper.SfHomTriangulated
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Paper.StratumAmbientHom
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.SmoothTensorDuality
import Sheaf.Paper.DirectImageTorAmplitude
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Verdier duality preserves finite-Tor constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.md`, order 2414
(blueprint: lem-weil-verdier-preservation-strata).

## Main declarations

* `finiteStageDualizingComplex`: the canonical ambient dualizing complex.
* `verdier_preservation_strata`: preservation with the specified uniform Tor bound.
* `verdier_preserves_boundedConstructible_finiteTor`: qualitative preservation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

/-- The canonical finite-stage ambient dualizing complex for the structure morphism of a
finite-type scheme over the fixed algebraically closed finite-field datum. The adjoint
instance is supplied by the ambient exceptional-adjoint theorem and Nagata compactification.
Source: blueprint `lem-weil-verdier-preservation-strata`
(blueprint: lem-weil-verdier-preservation-strata).
-/
noncomputable def finiteStageDualizingComplex
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X := by
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  letI : CompactSpace (HasCompactification.compactification
      (X ↘ Spec (.of D.k))).Z :=
    QuasiCompact.compactSpace_of_compactSpace
      (HasCompactification.compactification (X ↘ Spec (.of D.k))).g
  letI : IsLocallyNoetherian (HasCompactification.compactification
      (X ↘ Spec (.of D.k))).Z :=
    LocallyOfFiniteType.isLocallyNoetherian
      (HasCompactification.compactification (X ↘ Spec (.of D.k))).g
  letI : (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n)))
      (X ↘ Spec (.of D.k))).IsLeftAdjoint := by
    apply Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
  exact Etale.dualizingComplex
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E n)))
    (X ↘ Spec (.of D.k))

/-- Verdier duality preserves bounded constructible finite-Tor complexes over a finite
coefficient stage, with the uniform interval `[-b - 2*d, -a]`.

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.md`, order 2414
(blueprint: lem-weil-verdier-preservation-strata).

Proof (the five steps of the DAG node):
1. If a > b, the tensor-unit lemma lem-kun-tensor-unit makes K zero, so its dual is zero.
Otherwise lem-sf-etale-smooth-stratified-ctf supplies a finite smooth locally closed
stratification, dimensions e <= d, and finite-projective local models in [a,b].
2. The same stratification theorem supplies localization triangles building K from
G = Rs! P, with the terminal object zero. It suffices to bound the dual of each G.
3. Finite-type-over-Noetherian and open-subscheme facts, together with closed-immersion
finite type, verify the hypotheses of Nagata and thm-amb-etale-exceptional-adjoint on
all strata. The compact-support composition of lem-amb-unbounded-compact-support-comparisons,
the composite adjunction def-weil-pbc-composite-adjunction and det-sp-unique-right-adjoint
identify s! omega_X with omega_S. Then lem-weil-stratum-ambient-hom gives
D_X(Rs! P) = Rs* D_S P using ambient adjunctions only.
4. By thm-asd-smooth-tensor, omega_S is locally A[2e]. Restrict using
lem-weil-pbc-ringed-internal-hom-exact-restriction and compute the Hom complex of
E with A[2e] via def-pur-derived-internal-hom: its j-th term is Hom(E^(-j-2e),A).
These are finite projective and vanish outside [-b-2e,-a-2e]. Finite-locally-constant
Serre closure proves constructible cohomology. The bounded-flat Tor bound and derived
tensor restriction descend this interval. Apply lem-sf-etale-direct-image-vanishing
and thm-sf-direct-image-tor-amplitude to Rs* to obtain [-b-2e,-a].
5. By lem-sf-hom-triangulated dualize the localization triangles and induct backwards
from zero. Tensor each triangle with every module sheaf; lem-kun-derived-tensor-triangulated
and lem-sf-derived-homology-long-exact preserve the common interval [-b-2d,-a].
The untensored cohomology sequence and thm-constructible-serre preserve constructibility.
The interval contains no n, so the bound is uniform in the coefficient level.
-/
theorem verdier_preservation_strata
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X K)
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj
          (finiteStageDualizingComplex D l _hl E n hn X)) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (-b - 2 * (d : ℤ)) (-a)
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj
          (finiteStageDualizingComplex D l _hl E n hn X)) := by
  sorry

/-- The qualitative preservation clause: no dimension bound or Tor interval is fixed.
Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.md`, order 2414
(blueprint: lem-weil-verdier-preservation-strata).

Proof: choose a finite Tor interval of K. Use the finite smooth stratification of
lem-sf-etale-smooth-stratified-ctf and take the maximum d of zero and the finitely many
stratum dimensions. Apply the ambient-adjunction, smooth Hom-complex and direct-image
calculations in steps 1--4 of the node; every dual stratum has interval [-b-2d,-a].
The dual localization triangles, tensor exactness, the homology long exact sequence and
constructible Serre closure assemble these bounds in reverse order as in step 5.
For an empty stratification K is zero, so its dual has every Tor interval.
-/
theorem verdier_preserves_boundedConstructible_finiteTor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X K)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj
          (finiteStageDualizingComplex D l _hl E n hn X)) ∧
    ∃ a b : ℤ,
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      a b
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj
          (finiteStageDualizingComplex D l _hl E n hn X)) := by
  sorry

end WeilConjectures
