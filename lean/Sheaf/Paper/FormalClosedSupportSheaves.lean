/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Sheaf.Paper.ModuleObjects

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Sections with closed support for condensed module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-formal-closed-support,
node det-lem-formal-closed-support-sheaves
(blueprint: det-lem-formal-closed-support-sheaves); Stacks Project, Tags 09AA and 09AH.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The kernel of the open restriction unit, formed in the functor category, so that
its maps are precisely the induced kernel maps.
Source: blueprint det-lem-formal-closed-support-sheaves, definition of the supported kernel
(blueprint: det-lem-formal-closed-support-sheaves). -/
noncomputable def moduleSectionsWithSupport {X V : Scheme.{u}} (j : V ⟶ X) :
    pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ X :=
  kernel (upperStarLowerStarAdjunction Λ j).unit

/-- The sheaf on the closed subscheme: `i^* ker(M ⟶ j_* j^* M)`.
Source: blueprint det-lem-formal-closed-support-sheaves, displayed definition
(blueprint: det-lem-formal-closed-support-sheaves). -/
noncomputable def closedModuleSectionsWithSupport {X Z V : Scheme.{u}}
    (i : Z ⟶ X) (j : V ⟶ X) :
    pulledBackModuleObjects Λ X ⥤ pulledBackModuleObjects Λ Z :=
  moduleSectionsWithSupport Λ j ⋙ upperStar Λ i

/-- Sections with closed support give the right adjoint to the exact closed direct image.
Source: blueprint main-20261015, det-lem-formal-closed-support-sheaves, clauses (1)--(3);
Stacks Project, Tags 09AA and 09AH (blueprint: det-lem-formal-closed-support-sheaves).

Proof plan:
1. The standing scheme is Noetherian by finite type over the field
   (lem-weil-pbc-finite-type-over-noetherian), so its open complement is quasi-compact.
   The coefficient comparison alpha is an isomorphism, identifying the recorded module
   operations with ringed inverse/direct image for the actual pulled-back coefficient ring.
2. Use lem-weil-pbc-proetale-ringed-open-closed for exact closed direct image, the closed
   counit, vanishing of open restriction of closed direct image, and localization. The
   immersion-limit-preservation node gives exact inverse image. The open-comparison node
   identifies the open counit with the restriction counit; base-change evaluation makes it
   invertible. The closed-counit node makes closed direct image fully faithful.
3. Apply open inverse image to the unit kernel. The triangle identity and the invertible
   open counit imply this restriction is zero. Localization identifies that kernel with
   its closed inverse image followed by closed direct image, by the closed unit. Both the
   kernel construction and this unit are natural in the module. This proves (1).
4. A map from a closed direct image to M has zero composite with the open unit, hence
   factors uniquely through its kernel. Full faithfulness of closed direct image then
   identifies it with a map to the specified closed inverse image of the kernel. The
   inverse sends this map through the inverse closed unit and the kernel inclusion.
   Kernel uniqueness proves the inverse identities and naturality, giving the adjunction.
5. Kernel-map uniqueness gives additivity. Right adjoints preserve small limits
   (lem-weil-pbc-right-adjoint-preserves-limits); in particular this gives left exactness.
6. Exact closed direct image preserves monomorphisms. Apply the generic
   lem-exc-rg-right-adjoint-preserves-injectives to obtain the injective-module assertion.
7. Lift the additive adjunction termwise and to homotopy categories using
   lem-weil-pbc-termwise-adjunction-homotopy. Exact closed direct image takes every
   acyclic complex to an acyclic complex (lem-sp-exact-functor-preserves-homology).
   Adjunction therefore identifies maps from an acyclic complex to the image of a
   K-injective complex with zero homotopy classes. This proves K-injectivity, including
   unbounded complexes, by def-pur-kinjective-complex.

The admissible coefficients are the recorded predicate of sk-def-localizing-closure.
The first conjunct is the canonical natural identification of clause (1).
The existential additive instance only makes the termwise functor on complexes available.
-/
theorem formal_closed_support_sheaves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    IsIso (Functor.whiskerLeft (moduleSectionsWithSupport Λ j)
      (upperStarLowerStarAdjunction Λ i).unit) ∧
    PreservesFiniteLimits (lowerStar Λ i) ∧
    PreservesFiniteColimits (lowerStar Λ i) ∧
    Nonempty (lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j) ∧
    PreservesFiniteLimits (closedModuleSectionsWithSupport Λ i j) ∧
    PreservesLimitsOfSize.{u + 1, u + 1} (closedModuleSectionsWithSupport Λ i j) ∧
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      (∀ I : CochainComplex (pulledBackModuleObjects Λ X) ℤ,
        I.IsKInjective →
          CochainComplex.IsKInjective
            (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) ∧
      (∀ I : pulledBackModuleObjects Λ X, Injective I →
        Injective ((closedModuleSectionsWithSupport Λ i j).obj I)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
