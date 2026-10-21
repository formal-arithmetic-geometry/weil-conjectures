/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData

/-!
# Finite-field pro-etale direct-image finiteness

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.2 specialized
at a finite field, with Lemma 5.4.3 and Theorem 6.7.1
(blueprint: lem-sfb-finite-field-proetale-direct-image).

The categories are the ordinary uncompleted categories of intrinsic modules over the
constant ring sheaf. The total right derived functor is the recorded universal
K-injective construction, with its resolution hypothesis supplied by the existing
K-injective resolution instance. No separatedness or restriction on the base field
beyond its positive characteristic different from the coefficient characteristic is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Ordinary total direct image preserves bounded constructible complexes with finite
field coefficients of characteristic invertible in the base field.
Source: Bhatt--Scholze, Lemmas 6.7.2 and 5.4.3, Theorem 6.7.1, finite-field case
(blueprint: lem-sfb-finite-field-proetale-direct-image).

Proof plan, following the seven steps of the node:
1. Finite-type schemes over a field are Noetherian and quasi-compact
   (lem-weil-pbc-finite-type-over-noetherian), hence quasi-separated
   (lem-weil-pbc-locally-noetherian-quasi-separated). The morphism is qcqs by
   lem-weil-pbc-qcqs-morphism-permanence, without separatedness.
2. Finite modules over the finite field are precisely finite-dimensional vector spaces.
   On these qcqs schemes, the affine-local constructibility condition agrees with the
   global finite stratification condition: glue the local stratum maps using
   lem-weil-pbc-etale-stratification-local-gluing-core, and pull back the constant models.
3. By sk-thm-pe-constructible-comparison, descend K to a bounded constructible etale
   complex G. The exact inverse image of lem-pe-coefficient-comparison-derived-functor
   commutes with cohomology. Identify its intrinsic module presentation with the module
   inverse image of def-weil-pbc-site-comparison-morphism by uniqueness of left adjoints
   to the same sectionwise direct image (lem-pe-coefficient-comparison-data).
4. The coefficient field is killed by ell, which is invertible in k. Apply
   thm-dg-finite-type-constructibility to G. Its ordinary etale direct image is bounded
   constructible over the arbitrary field k, also for a non-separated morphism.
5. Module sheaves form Grothendieck abelian categories
   (lem-pur-ringed-site-grothendieck-abelian); lem-sfb-grothendieck-k-injective gives
   K-injective resolutions. Apply lem-weil-pbc-kinjective-total-derived to degreewise
   direct image followed by localization. It computes the full derived value on a
   K-injective resolution.
6. Enough injectives (lem-sp-grothendieck-enough-injectives) and
   lem-weil-pbc-dplus-injective-representative give a bounded-below injective, hence
   K-injective, representative. Thus the full functor of def-sfb-right-derived-functor
   agrees on this input with the bounded-below direct image.
7. Apply prop-weil-pbc-comparison-direct-image to G and the qcqs morphism. It identifies
   the pro-etale direct image of K with the inverse image of the etale direct image of G.
   Exact cohomology comparison preserves its finite interval of vanishing, and
   sk-thm-pe-constructible-comparison preserves constructibility. Step 2 converts this
   back to the intrinsic global stratification convention asserted here. -/
theorem finiteField_proEtale_directImage_bounded_constructible
    (ell p : ℕ) (hell : ell.Prime) (hp : 0 < p) (hne : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (A : Type u) [Field A] [Finite A] [CharP A ell]
    {T V : Scheme.{u}} (aT : T ⟶ Spec (.of k)) (aV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (f : T ⟶ V) (hf : f ≫ aV = aT) [LocallyOfFiniteType f] [QuasiCompact f]
    (K : proEtaleDerivedCategory T A)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K))
    (hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)) :
    (fun L : proEtaleDerivedCategory V A ↦
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules V (proEtaleConstantRing V A)) q).obj L)) ∧
      ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf V A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules V (proEtaleConstantRing V A)) q).obj L))
      (((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorOfQuasiIsoResolutions
        (fun C ↦ (Abelian.HasKInjectiveResolutions.exists_isKInjective C).elim
          (fun I hI ↦ hI.elim (fun hI hs ↦ hs.elim
            (fun s hs ↦ ⟨I, s, hI, hs.2⟩))))).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
