/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.AlgebraicGeometry.ConstructibleModuleObjectsEssentiallySmall
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.TAdmissibleDualizableTruncations
import Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels
import Sheaf.CategoryTheory.DerivedCategory.DegreeZeroAbelianCriterion
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.FiniteCoefficientModelComparison
import Sheaf.Paper.ProEtaleFixedModuleConstructible
import Sheaf.Paper.ProEtaleConstructibleExactClosure

/-!
# The Noetherian finite scalar-model constructible heart

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
Theorem 6.2(3), Lemma 6.10 and Corollary 6.11; Stacks Tags 09B5 and 03RZ.
(blueprint: lem-sfb-noetherian-scalar-constructible-heart).

The ambient category is the ordinary, uncompleted category of internal modules.
The coefficient alternatives are written out because the recorded localizing
coefficient predicate also permits a distinct finite-subextension-valued algebraic
closure. Here the algebraic-closure alternative uses all continuous functions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite scalar-model constructible modules on a Noetherian scheme form an
essentially small, replete abelian full subcategory, closed under every ambient
extension, with exact inclusion. Integral torsion modules are allowed.

Source: Hemo--Richarz--Scholbach, Theorem 6.2(3), Lemma 6.10 and Corollary 6.11;
Stacks Tags 09B5 and 03RZ.
(blueprint: lem-sfb-noetherian-scalar-constructible-heart).

Proof plan:
1. Identify internal modules with sectionwise module sheaves using
   def-weil-pbc-internal-abelian-sheaf-module-equivalence and
   def-weil-sheaf-of-modules-category. Finite scalar models are locally finitely
   presented by det-def-sfb-constructible-local-model. Restrict the small family of
   lem-sfb-constructible-module-objects-essentially-small to scalar-model objects;
   repleteness gives essential smallness in the universe of def-weil-size-convention.
2. Local Noetherianity gives quasi-separatedness by
   lem-weil-pbc-locally-noetherian-quasi-separated. Quasi-compactness makes the
   underlying space Noetherian by lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.
   Its locally closed subspaces are Noetherian, so
   lem-sc-noetherian-finite-irreducible-components applies to every stratum and open.
   Use lem-weil-pbc-constructible-stratification-intersection for a common finite
   stratification. Exact restriction (det-prop-sfb-module-pullback-exact-main) and
   composition (sk-def-sfb-module-pushforward-pullback) preserve scalar presentations
   and identify restrictions of kernels, cokernels and short exact sequences.
3. For the five topological coefficient cases, fields and the valuation PIDs
   (def-weil-l-adic-numbers, lem-weil-l-adic-extension-integers-dvr) are semihereditary.
   Their metric topologies are T1. Apply
   lem-sfb-semihereditary-topological-coefficients-admissible and
   lem-zl-t-admissible-dualizable-truncations. For the algebraic closure these use
   all continuous functions, without a finite-subextension or completeness condition.
4. On each common stratum the dualizable subcategory is strictly full and
   triangulated by lem-zl-condensed-dualizable-local-perfect-models. The preceding
   truncation theorem identifies its degree-zero objects with finite scalar models.
   The criterion lem-sfb-derived-degree-zero-abelian-criterion gives zero, ambient
   kernels, cokernels and extensions, including integral torsion. Descend these
   models along the finite stratification by sk-def-sfb-constructible.
5. For finite discrete coefficients use lem-sf-module-object-ordinary-coefficient-equivalence
   and lem-pe-finite-coefficient-model-comparison to identify scalar-model
   constructibility with finite-stalk ordinary constructibility
   (def-weil-proetale-constructible-sheaf). Transport kernels, cokernels and ambient
   short exact sequences through the exact equivalence, apply
   lem-weil-proetale-constructible-exact-closure, and transport back. This includes
   nonregular finite rings, such as Z/ell^2, and the zero ring.
6. The zero scalar model belongs on the one-stratum stratification, even for the
   empty scheme. Extension closure gives finite biproducts from split exact
   sequences. Apply lem-weil-pbc-abelian-full-subcategory-exact to obtain an abelian
   full subcategory with ambient kernels and cokernels and exact inclusion.
   No characteristic or dimension restriction was used. -/
theorem noetherian_scalar_constructible_heart
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    EssentiallySmall.{u + 1} (ConstantModelConstructible Λ X) ∧
      ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) ∧
      ObjectProperty.ContainsZero (IsConstantModelConstructible Λ X) ∧
      ObjectProperty.IsClosedUnderKernels (IsConstantModelConstructible Λ X) ∧
      ObjectProperty.IsClosedUnderCokernels (IsConstantModelConstructible Λ X) ∧
      ObjectProperty.IsClosedUnderExtensions (IsConstantModelConstructible Λ X) ∧
      Nonempty (Abelian (ConstantModelConstructible Λ X)) ∧
      PreservesFiniteLimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
      PreservesFiniteColimits (ObjectProperty.ι (IsConstantModelConstructible Λ X)) := by
  sorry

end AlgebraicGeometry.ProEtale
