/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.SfCommonStageDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

/-!
# The reverse adjunction for a finite etale pro-etale direct image

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
order 2062 (blueprint: prop-exc-finite-etale-adjoint).
Positive coefficient levels are indexed by `n : ℕ` with exponent `n+1`; this includes
exactly every exponent at least one. The ordinary clause is for arbitrary schemes.
Only the compact-support clause uses the ambient finite-type finite-field setting.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The published positive-level finiteness theorem supplies the coefficient instance;
this changes no coefficient ring or site universe. Source: blueprint order 2062,
coefficient convention (blueprint: prop-exc-finite-etale-adjoint). -/
noncomputable instance finiteEtaleAdjunction_coefficientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- The published exact inverse image, transported by the canonical constant-scalar
realization equivalences and applied termwise to all integer-indexed complexes.
The two `letI` declarations expose additivity of the already fixed realization;
no coefficient map, adjunction or equivalence is chosen independently.
Source: blueprint order 2062, inverse-image convention;
`def-weil-derived-pullback-tensor-hom`, finite-level clause
(blueprint: prop-exc-finite-etale-adjoint). -/
noncomputable def finiteEtaleAdjunction_inverseImage {V X : Scheme.{u}} (e : V ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory V A :=
  letI : (sfIntrinsicModuleEquivalence X A).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization X A).Additive
  letI : (sfIntrinsicModuleEquivalence V A).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization V A).Additive
  ((sfIntrinsicModuleEquivalence X A).inverse ⋙
    ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e ⋙
    (sfIntrinsicModuleEquivalence V A).functor).mapDerivedCategory

/-- Exactness, termwise computation, and the reverse derived adjunction for finite
etale direct image. No boundedness, nonempty-fibre, or constructibility condition occurs.
Source: blueprint order 2062, first displayed adjunction
(blueprint: prop-exc-finite-etale-adjoint).

Proof plan: (1) An etale map is weakly etale, so identify its small site with the slice
site by lem-weil-proetale-weakly-etale-localization. The exact slice extension `J_e`
is left adjoint to restriction by lem-pur-site-restriction-module-adjunction-exact.
Use lem-weil-pbc-finite-etale-etale-local-split to cover the base by etale neighbourhoods
on which the number of sheets is finite (and may vary). These are pro-etale covers.
(2) The sheaf condition identifies sheaves on a split cover with tuples; direct image
is their finite product, inverse image is the diagonal, and `J_e` is their finite sum.
(3) The diagonal matrix with identity entries gives the sum-to-product isomorphism,
with inverse the sum of inclusions composed with projections. Both commute with
permutations, so lem-pur-sheaf-hom-cover-gluing glues them naturally. Hence direct
image is exact and left adjoint to inverse image. The empty tuple gives zero.
(4) The unit is inclusion of each sheet and the counit is summation. On a summand,
both triangle identities reduce to the identity; uniqueness of gluing proves them
globally. (5) Apply both exact functors termwise to unbounded complexes. Naturality
makes units and counits chain maps, whose triangles hold degreewise. Localization
preserves them. Exactness sends every K-injective resolution quasi-isomorphism to a
quasi-isomorphism, so the termwise direct image computes the recorded total derived
image. Exact inverse image is the already specified termwise derived pullback.
This is the argument of lem-sf-exact-functor-derived-triangulated. -/
theorem finiteEtale_proEtale_exact_derived_adjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) {V X : Scheme.{u}} (e : V ⟶ X)
    [IsFinite e] [Etale e]
    (_hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    PreservesFiniteLimits
      (proEtaleConstantModuleDirectImage e (Padic.coefficientExtensionRing l E (n + 1))) ∧
    PreservesFiniteColimits
      (proEtaleConstantModuleDirectImage e (Padic.coefficientExtensionRing l E (n + 1))) ∧
    Nonempty
      (DerivedCategory.Q ⋙
          proEtaleConstantDerivedDirectImage e (Padic.coefficientExtensionRing l E (n + 1)) ≅
        (proEtaleConstantModuleDirectImage e
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    Nonempty
      (proEtaleConstantDerivedDirectImage e (Padic.coefficientExtensionRing l E (n + 1)) ⊣
        finiteEtaleAdjunction_inverseImage e (Padic.coefficientExtensionRing l E (n + 1))) := by
  sorry

/-- For the proper identity compactification the compact-support candidate is the
ordinary total direct image and has inverse image as right adjoint, on the entire
unbounded derived categories. Restricting this identification to the etale-origin
subcategory gives the usual compactification-independent notation `Re_! = Re_*`.
Source: blueprint order 2062, compact-support clause
(blueprint: prop-exc-finite-etale-adjoint).

Proof plan: (6) A finite map is proper (lem-weil-pbc-finite-proper), so
`Compactification.ofIsProper e.left` is exactly `(id_V,e)`. The formula of
def-weil-compact-support-candidate and def-compact-support-direct-image-detailed is
`Re_*` after extension by zero for the identity. In the defining presheaf every
test object has its unique factorization through the identity, giving the original
module sheaf and its restrictions; sheafification adds nothing. Thus that extension
is naturally the identity, and the candidate is naturally `Re_*`. The previous
clause supplies the adjunction and termwise interpretation. On the etale-origin
subcategory compactification independence permits suppression of the superscript.
No compactification independence on arbitrary unbounded objects is invoked. -/
theorem finiteEtale_proEtale_identityCompactification_adjunction
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (V X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (e : V ⟶ X) [IsFinite e.left] [Etale e.left] :
    Nonempty
      (sfIntrinsicCompactSupport (Compactification.ofIsProper e.left)
          (Padic.coefficientExtensionRing l E (n + 1)) ≅
        proEtaleConstantDerivedDirectImage e.left (Padic.coefficientExtensionRing l E (n + 1))) ∧
    Nonempty
      (sfIntrinsicCompactSupport (Compactification.ofIsProper e.left)
          (Padic.coefficientExtensionRing l E (n + 1)) ⊣
        finiteEtaleAdjunction_inverseImage e.left
          (Padic.coefficientExtensionRing l E (n + 1))) := by
  sorry

end AlgebraicGeometry.Scheme
