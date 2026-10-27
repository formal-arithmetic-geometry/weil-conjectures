/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Paper.CoefficientHeartFiltration
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness
import Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.CoefficientHeartLocallyClosedExtension
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.StratifiedLattice
import Sheaf.Paper.CoefficientHeartLisseExtensionConstructible
import Sheaf.Paper.CoefficientHeartClosure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-! # Integral lattice reduction in a support induction

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13 and
Proposition 6.8.14, pp.61--62; Stacks Project, proetale.tex, Tags 09AH and 09AB;
blueprint, coefficient-heart generation, Single sheaves and Complexes paragraphs.
(blueprint: lem-sfb-integral-support-lattice-reduction).

The helper constructions only specialize the recorded continuous coefficients and
canonical scalar/locally closed extensions. Support is zero restriction to the open
complement of a closed set, without imposing a scheme structure on that set.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

namespace IntegralSupportReduction

/-- Continuous functions into the recorded valuation ring, with its subspace norm topology
and the recorded pointwise multiplication. Source: Bhatt--Scholze, Section 6.8,
coefficient setup (blueprint: lem-sfb-integral-support-lattice-reduction). -/
def integralRing (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  X := Profinite.continuousMapRingObjOfUniverse (Padic.coefficientExtensionIntegers ℓ E)
  mon := Profinite.continuousMapRingObjOfUniverseMonObj _

/-- Commutativity of the recorded continuous integral coefficients.
Source: Bhatt--Scholze, Section 6.8, commutative coefficients
(blueprint: lem-sfb-integral-support-lattice-reduction). -/
instance integralRing_comm (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    IsCommMonObj (integralRing ℓ E).X :=
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse _

/-- Postcomposition with the actual inclusion of the valuation ring into E.
Source: Bhatt--Scholze, Lemma 6.8.13, scalar extension from integral coefficients
(blueprint: lem-sfb-integral-support-lattice-reduction). -/
def inclusion (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    integralRing ℓ E ⟶ normContinuousRing E :=
  letI := Profinite.continuousMapRingObjOfUniverseMonObj
    (Padic.coefficientExtensionIntegers ℓ E)
  letI := Profinite.continuousMapRingObjOfUniverseMonObj E
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val
  Mon.ofHom (Profinite.continuousMapRingObjMapOfUniverse
    (Padic.coefficientExtensionIntegers ℓ E).subtype continuous_subtype_val)

/-- The actual object a_!(A_E tensor_{A_O} M_0)[0]. Both coefficient rings are pulled
from the point and scalar extension uses the inclusion just specified. The extension
uses the canonical scheme-theoretic closure factorization. Finite type over a field
supplies Noetherianity, rather than requiring an extra hypothesis on U.
Source: Bhatt--Scholze, Lemma 6.8.13; blueprint coefficient-heart generation
(blueprint: lem-sfb-integral-support-lattice-reduction). -/
def latticeExtension (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {k : Type u} [Field k] (U : Over (Spec (.of k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    {S : Scheme.{u}} (a : S ⟶ U.left) (ha : IsImmersion a)
    (M₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (integralRing ℓ E).X S)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
      (condensedRingObj (normContinuousRing E).X U.left)) :=
  letI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  letI : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  letI : IsNoetherian U.left := ⟨⟩
  (DerivedCategory.singleFunctor _ 0).obj
    ((coefficientHeartLocallyClosedExtension (normContinuousRing E).X a ha).obj
      ((Mod.extendScalars (coefficientMap (inclusion ℓ E).hom S)).obj M₀))

end IntegralSupportReduction

/-- The conditional support-induction step and its unconditional empty-support case.
Only integral strata dense in the given closed set are tested by the lattice hypothesis;
for reducible support all component closures can instead use the smaller-support hypothesis.
Zero rank, arbitrary closed subsets, and nonreduced ambient schemes are included.

Source: agent support reduction from Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14,
pp.61--62; Stacks, Tags 09AH and 09AB; blueprint coefficient-heart generation proof
(blueprint: lem-sfb-integral-support-lattice-reduction).

Proof plan, following the nine steps of the node:
1. Exact open restriction commutes with cohomology. Reconstruct a bounded constructible
complex from its finitely many cohomology sheaves, shifts and cones using
lem-sfb-bounded-cohomology-cone-witness and lem-weil-pbc-condensed-open-closed-recollement.
Empty support means restriction along the identity is zero, so the object is zero.
2. Realize Z by its reduced induced closed subscheme i:T to U. Localization gives F = i_*N.
Finite type gives Noetherianity and quasi-compact open complements. Pull back actual
finite scalar-presentation models along the Cartesian coefficient identifications; N remains
constructible. Use lem-weil-pbc-reduced-induced-closed-subscheme,
lem-weil-pbc-finite-type-over-noetherian, lem-sfb-coefficient-heart-locally-closed-extension,
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal,
lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-module-constructible-pullback and
sk-prop-sfb-cartesian-coefficients.
3. The finitely many irreducible components of reduced T cover T. In each component remove
the others, obtaining disjoint nonempty integral opens O_h dense in the component; use
lem-sc-noetherian-finite-irreducible-components, lem-sc-irreducible-components-cover and
 def-pc-integral-scheme. No regularity is needed.
4. A finite locally closed partition of irreducible O_h has a dense stratum, which is open.
Its closed ideal on that open has zero radical and is zero because O_h is reduced.
The scalar models there are finite-dimensional E-vector spaces, so choosing bases makes N
lisse, including a zero model. Use sk-def-sfb-constructible,
lem-weil-pbc-module-constructible-pullback and sk-prop-sfb-cartesian-coefficients.
5. Apply sk-lem-stratified-lattice and shrink to a dense integral open S_h with a lisse
integral lattice M_0,h rationalizing to N restricted to S_h. No global lattice on T is claimed.
6. The finite disjoint union S of these opens has extension P = i_*j_!j^*N equal to the
finite sum of (a_h)_!(M_0,h[1/ell]). Exact extension and composition coherence are
lem-sfb-locally-closed-extension-coherence. Each summand is constructible by
lem-sfb-coefficient-heart-lisse-extension-constructible and their finite sum is constructible
by det-lem-coefficient-heart-closure applied to split short exact sequences.
7. For a component closure equal to Z apply the lattice hypothesis. For a proper component
closure apply the smaller-support hypothesis. The support assertion follows by closed
pushforward and zero restriction outside its image, using the same coherence and
lem-weil-pbc-proetale-ringed-open-closed. Thus P[0] belongs to H by finite sums.
8. Localization and exact i_* give 0 to P to F to Q to 0. The cokernel clause of
 det-lem-coefficient-heart-closure makes Q constructible. Its support is the proper closed
complement of S in T, so Q[0] belongs to H by the smaller-support hypothesis.
9. The short exact sequence yields a distinguished triangle by lem-sf-derived-ses-triangle.
Thickness puts F[0] in H, and step 1 puts the original complex in H. All constructions are
finite; neither an alteration nor a trace is asserted. -/
theorem integralSupportLatticeReduction
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (_hpℓ : p ≠ ℓ)
    (U : Over (Spec (.of k))) [IsSeparated U.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (Z : Closeds U.left)
    (H : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (normContinuousRing E).X U.left))))
    [H.IsTriangulated] [H.IsStableUnderRetracts] :
    (((∀ (F : Closeds U.left), F < Z →
        ∀ C : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
            (condensedRingObj (normContinuousRing E).X U.left)),
          constantModelBoundedConstructible (normContinuousRing E).X U.left C →
          IsZero ((CondensedRing.moduleObjectDerivedPullback
            (normContinuousRing E).X (Scheme.Opens.ι F.compl)).obj C) → H C) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ U.left) (ha : IsImmersion a),
        IsIntegral S → closure (Set.range a) = (Z : Set U.left) →
        ∀ M₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (IntegralSupportReduction.integralRing ℓ E).X S),
          IsLisseCoefficientModule (IntegralSupportReduction.integralRing ℓ E).X M₀ →
          H (IntegralSupportReduction.latticeExtension ℓ E U a ha M₀))) →
      ∀ C : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
          (condensedRingObj (normContinuousRing E).X U.left)),
        constantModelBoundedConstructible (normContinuousRing E).X U.left C →
        IsZero ((CondensedRing.moduleObjectDerivedPullback
          (normContinuousRing E).X (Scheme.Opens.ι Z.compl)).obj C) → H C) ∧
    (Z = ⊥ → ∀ C : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (normContinuousRing E).X U.left)),
      constantModelBoundedConstructible (normContinuousRing E).X U.left C →
      IsZero ((CondensedRing.moduleObjectDerivedPullback
        (normContinuousRing E).X (Scheme.Opens.ι Z.compl)).obj C) → H C) := by
  sorry

end AlgebraicGeometry.ProEtale
