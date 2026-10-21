/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.Compactification.Refinement
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.CategoryTheory.RightDerivedFunctorUpperBound
import Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-!
# Bounded-below ordinary etale compact-support adjunctions

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
cor-weil-boundary-duality-discharge.md, first proof paragraph; Bhatt--Scholze,
The pro-etale topology for schemes, Corollary 5.1.6
(blueprint: lem-weil-boundary-etale-adjunction-restriction).

The proposition below packages exactly the geometric preparation, restriction of the
ordinary ambient adjunction, reflection of lower bounds, and image of the specified
comparison unit. All derived categories use the fixed constant-ring module presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a fixed compactification, the ambient ordinary etale right adjoint preserves
D+, and the full-subcategory adjunction is the restriction of this very adjunction.
The final map is the image of the canonical unbounded derived comparison unit.
Source: boundary-duality discharge, preparation of ordinary etale costalk adjunctions;
Bhatt--Scholze, Corollary 5.1.6
(blueprint: lem-weil-boundary-etale-adjunction-restriction). -/
def BoundaryEtaleCompactificationAdjunction (Λ : Type (u + 1)) [CommRing Λ]
    {V W : Scheme.{u}} {h : V ⟶ W} (c : Compactification h) : Prop :=
  ∃ (R : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⊣ R),
    (∀ K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.TStructure.t.plus K → DerivedCategory.TStructure.t.plus
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K)) ∧
    (∀ L : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      DerivedCategory.TStructure.t.plus L → DerivedCategory.TStructure.t.plus (R.obj L)) ∧
    (∃ (Rplus : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
        DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (eR : DerivedCategory.Plus.ι ⋙ R ≅ Rplus ⋙ DerivedCategory.Plus.ι)
      (adjPlus : rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} Λ) c ⊣ Rplus),
      adjPlus = adj.restrictFullyFaithful
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} Λ) c).symm eR) ∧
    (∀ L : DerivedCategory.Plus (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.map
        (R.map ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} Λ) W).unit.app L.obj))) ∧
      DerivedCategory.TStructure.t.plus
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.obj
          (R.obj L.obj)) ∧
      DerivedCategory.TStructure.t.plus
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.obj
          (R.obj (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) W).mapDerivedCategory ⋙
            (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} Λ) W).rightDerivedFunctor).obj
              L.obj))))

/-- The full conclusion: existence of a compactification, Noetherianity and
quasi-separatedness, finite type and finite dimension for every compactification,
its ordinary adjunction and restriction, and reflection of every lower bound on
arbitrary unbounded etale input. A natural number dimension bound includes zero
and does not exclude the empty scheme.
Source: boundary-duality discharge, first proof paragraph
(blueprint: lem-weil-boundary-etale-adjunction-restriction). -/
def BoundaryEtaleAdjunctionRestriction (Λ : Type (u + 1)) [CommRing Λ]
    {V W S : Scheme.{u}} (h : V ⟶ W) (aW : W ⟶ S) : Prop :=
  Nonempty (Compactification h) ∧ IsNoetherian V ∧ IsNoetherian W ∧
    QuasiSeparatedSpace V ∧ QuasiSeparatedSpace W ∧
    (∀ c : Compactification h,
      IsNoetherian c.Z ∧ QuasiSeparatedSpace c.Z ∧
      LocallyOfFiniteType (c.g ≫ aW) ∧ QuasiCompact (c.g ≫ aW) ∧
      (∃ d : ℕ, topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) ∧
      BoundaryEtaleCompactificationAdjunction Λ c) ∧
    (∀ (C : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ),
      DerivedCategory.TStructure.t.IsGE
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.obj C) b ↔
      DerivedCategory.TStructure.t.IsGE C b)

/-- Compact support and its ambient right adjoint restrict to D+, with the ambient
Hom bijections, unit and counit; comparison reflects arbitrary lower bounds and
carries the right-adjoint image of the specified comparison unit to an isomorphism
between bounded-below objects. No boundedness of the right-adjoint image is assumed.
Source: boundary-duality discharge, first proof paragraph; Bhatt--Scholze,
The pro-etale topology for schemes, Corollary 5.1.6
(blueprint: lem-weil-boundary-etale-adjunction-restriction).

Proof:
1. The finite coefficient ring is commutative and finite by
   def-weil-l-adic-coefficient-extension, hence additively torsion. The field spectrum
   is Noetherian. Apply lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated to V and W. Nagata's theorem
   thm-nagata-compactification gives a compactification of the separated finite-type h.
2. For every c, its proper map is finite type. Compose with aW using
   lem-sfb-finite-type-composition-base-change. The same Noetherian and quasi-separated
   lemmas apply to c.Z. Use lem-kun-dimension-finite-type to obtain a natural number
   dimension bound; zero works for the empty scheme. Density of the open is unnecessary.
3. Apply thm-amb-etale-exceptional-adjoint to obtain the ordinary ambient adjunction.
4. Exact extension by zero (lem-weil-pbc-extension-by-zero-exact and
   lem-weil-pbc-exact-functor-complex-cohomology) preserves lower bounds. Direct image
   is left exact by lem-weil-pbc-module-direct-image-left-exact. The sheaf categories
   are Grothendieck abelian by lem-pur-ringed-site-grothendieck-abelian. Apply
   lem-weil-pbc-derived-functor-negative-vanishing and
   src-right-derived-functor-plus-compatibility to show F_c preserves D+.
5. By lem-kun-relative-torsion-direct-image-dimension-bound, higher direct image under
   p vanishes above 2d. Use the Grothendieck property, enough injectives from
   lem-weil-pbc-module-sheaves-enough-injectives and K-injectives from
   prop-weil-pbc-kinjective-resolutions-exist in lem-etale-derived-functor-upper-amplitude.
   Exact j_! gives F_c(D^{≤m}) contained in D^{≤m+2d}, even on unbounded inputs.
   Orthogonality, as in lem-etale-upper-shriek-explicit-amplitude-interface, now gives
   preservation of D+ by R_c, before restricting the adjunction.
6. Restrict the ambient Hom bijections along the fully faithful D+ inclusions using
   Adjunction.restrictFullyFaithful. Its unit and counit formulas identify them with
   the ambient ones under the compatibility isomorphisms.
7. Exactness from lem-sf-comparison-pullback-exact identifies every cohomology sheaf
   of S_V C with S_V of that cohomology sheaf. The site-comparison theorem
   thm-weil-pbc-site-comparison implies faithfulness on sheaves placed in degree zero.
   Consequently S_V detects zero cohomology and reflects every lower bound, with
   no boundedness assumption on C.
8. The actual comparison unit at L in D+ is invertible by
   thm-weil-pbc-site-comparison. Its target is bounded below as well. Step 5 puts
   their R_c-images in D+, and step 7 puts their S_V-images in D+.
   Applying S_V R_c to that unit preserves its inverse and gives the specified map.
-/
theorem boundary_etale_adjunction_restriction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n) {V W : Scheme.{u}}
    (aV : V ⟶ Spec (.of D.k)) (aW : W ⟶ Spec (.of D.k))
    [IsSeparated aV] [LocallyOfFiniteType aV] [QuasiCompact aV]
    [IsSeparated aW] [LocallyOfFiniteType aW] [QuasiCompact aW]
    (h : V ⟶ W) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (_hover : h ≫ aW = aV) :
    BoundaryEtaleAdjunctionRestriction
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) h aW := by
  sorry

end AlgebraicGeometry.Etale
