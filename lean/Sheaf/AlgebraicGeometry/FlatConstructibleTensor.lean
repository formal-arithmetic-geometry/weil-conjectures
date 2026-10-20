/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Tensor with a flat constructible etale sheaf

Source: Stacks Project, Etale Cohomology, Tags 095I and 0961, with the exact-functor
cohomology computation of Homology, Tag 010N
(blueprint: lem-fd-flat-constructible-tensor).

The two auxiliary bifunctors express naturality in both the bounded constructible complex
and the flat constructible sheaf. They use the existing small-etale module-sheaf tensor,
its unbounded derived tensor, and the recorded finite-value constructibility predicates.

## Main definitions

* `flatConstructibleEtaleSheafProperty`: the two hypotheses on the sheaf factor.
* `flatConstructibleTensorCohomologyLeft`: cohomology after derived tensor.
* `flatConstructibleTensorCohomologyRight`: ordinary tensor after cohomology.

## Main statements

* `flatConstructibleTensor_cohomology_and_bounds`: the natural comparison,
  constructibility, bounded constructibility, and preservation of every cohomology interval.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The full-subcategory property bundling exactly the assumptions on `L`: constructibility
and exactness of `- ⊗ L`. The tensor is the existing sheafification of sectionwise tensor,
with its monoidal structure supplied explicitly, so no file-local instance is needed.
Source: Stacks, Tags 03ER(3) and 095I
(blueprint: lem-fd-flat-constructible-tensor). -/
def flatConstructibleEtaleSheafProperty
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun L ↦ Scheme.IsConstructibleEtaleModuleSheaf L ∧
    exactFunctor _ _
      (@tensorRight _ _ (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) L)

/-- The bifunctor `(L,K) ↦ Hⁱ(K ⊗ᴸ L[0])` on flat constructible sheaves and bounded
constructible complexes. Every map is supplied by composition of the existing functors.
Source: Stacks, Tags 06YU, 010N and 0961
(blueprint: lem-fd-flat-constructible-tensor). -/
noncomputable def flatConstructibleTensorCohomologyLeft
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) (i : ℤ) :
    (flatConstructibleEtaleSheafProperty Λ X).FullSubcategory ⥤
      BoundedConstructibleDerivedCategory Λ X ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (flatConstructibleEtaleSheafProperty Λ X).ι ⋙
    _root_.DerivedCategory.singleFunctor _ 0 ⋙
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj (DerivedCategory.isBoundedConstructible Λ X).ι ⋙
    (Functor.whiskeringRight _ _ _).obj (_root_.DerivedCategory.homologyFunctor _ i)

/-- The bifunctor `(L,K) ↦ Hⁱ(K) ⊗ L`, with the ordinary tensor of module sheaves.
The full-subcategory inclusions retain all morphisms, so an isomorphism between these
bifunctors includes naturality in both variables, including arbitrary maps between flat
constructible sheaves.
Source: Stacks, Tags 095I and 010N
(blueprint: lem-fd-flat-constructible-tensor). -/
noncomputable def flatConstructibleTensorCohomologyRight
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) (i : ℤ) :
    (flatConstructibleEtaleSheafProperty Λ X).FullSubcategory ⥤
      BoundedConstructibleDerivedCategory Λ X ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (flatConstructibleEtaleSheafProperty Λ X).ι ⋙
    (@curriedTensor _ _
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).flip ⋙
    (Functor.whiskeringLeft _ _ _).obj
      ((DerivedCategory.isBoundedConstructible Λ X).ι ⋙
        _root_.DerivedCategory.homologyFunctor _ i)

/-- Tensoring a bounded constructible complex with a flat constructible sheaf in degree
zero commutes naturally with cohomology. The cohomology sheaves are constructible, the
result is bounded constructible, and every interval containing the input cohomology also
contains the output cohomology. No finite Tor-amplitude assumption is made on the input.

Source: Stacks, Tags 095I and 0961, specialized to a flat degree-zero factor; Homology,
Tag 010N, and Cohomology on Sites, Tags 06YS and 06YU
(blueprint: lem-fd-flat-constructible-tensor).

Proof:
1. Exactness of `- ⊗ L` gives its cohomology comparison by
   `lem-weil-pbc-exact-functor-complex-cohomology`. The total tensor with `L[0]` has
   exactly one summand in each degree and differential `d ⊗ 1`, so it is that exact
   functor applied degreewise. In particular `L[0]` is K-flat
   (`def-pc-flat-sheaf-modules`, `def-kun-derived-tensor`, `def-pc-kflat-complex`).
2. Resolve an arbitrary representative of `K` by a flat-term K-flat complex using
   `lem-pc-kflat-resolution`. Its tensor with `L[0]` represents the derived tensor.
   Step 1 identifies its cohomology with `Hⁱ(K) ⊗ L`. The localization and tensor
   comparison of `lem-weil-pbc-site-derived-tensor-descent` make this natural in `K`.
   Maps of flat sheaves commute with tensor differentials, cycles and boundaries,
   making the same comparison natural in `L`.
3. Refine the constructible stratifications of `Hⁱ(K)` and `L` by their fibre products
   (`lem-weil-pbc-constructible-stratification-intersection`). Pullback preserves finite
   locally constant sheaves (`lemma-constructible-pullback-locally-constant`,
   `lemma-constructible-pullback-finite`), with the constant coefficient comparison of
   `prop-weil-pbc-inverse-image-modules-exact` retaining their module structures.
4. Ordinary pullback commutes with tensor
   (`lem-weil-pbc-ringed-topoi-module-pullback-tensor`). On each refined stratum the
   tensor is locally constant by `lem-weil-pbc-flc-tensor-locally-constant-part` and
   finite by `lem-weil-pbc-flc-tensor-finite-part`. Thus `Hⁱ(K) ⊗ L`, and hence step 2's
   cohomology sheaf, is constructible (`def-weil-pbc-etale-constructible-sheaf`).
5. Where `Hⁱ(K)` vanishes, step 2 identifies the output with `0 ⊗ L = 0`.
   Every interval is therefore preserved. Combined with step 4 this is bounded
   constructibility (`def-weil-pbc-constructible-complexes`). Only `L` was flat. -/
theorem flatConstructibleTensor_cohomology_and_bounds
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :
    (∀ i : ℤ, Nonempty
      (flatConstructibleTensorCohomologyLeft Λ X i ≅
        flatConstructibleTensorCohomologyRight Λ X i)) ∧
    ∀ (L : (flatConstructibleEtaleSheafProperty Λ X).FullSubcategory)
      (K : BoundedConstructibleDerivedCategory Λ X),
      (∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
        (((flatConstructibleTensorCohomologyLeft Λ X i).obj L).obj K)) ∧
      DerivedCategory.isBoundedConstructible Λ X
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K.obj).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L.obj)) ∧
      ∀ a b : ℤ, a ≤ b →
        (∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K.obj)) →
        ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero (((flatConstructibleTensorCohomologyLeft Λ X i).obj L).obj K) := by
  sorry

end AlgebraicGeometry.Etale
