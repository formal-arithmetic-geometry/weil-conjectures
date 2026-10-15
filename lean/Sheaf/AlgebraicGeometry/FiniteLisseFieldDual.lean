/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import Mathlib.Data.ZMod.Basic

import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel

/-!
# Duals of bounded finite locally constant complexes over a prime field

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-lisse-field-dual.md
(blueprint: lem-fin-lisse-field-dual).

The existing etale `derivedHom` is the K-injective derived internal Hom in the
`ModuleCat` encoding. Its construction derives the homotopy-category Hom functor
using K-injectives in `DerivedCategory.tensorHomAdjunctionQhObj`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical map from the pullback of the coefficient dual to the dual of the
pullback: transpose the pulled-back evaluation using the strong monoidal pullback
and its unit comparison. Source: blueprint lem-fin-lisse-field-dual, proof step 5;
Stacks, Sites Cohomology, Section 08J7 (blueprint: lem-fin-lisse-field-dual). -/
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :
    (L(upperStar (ModuleCat.{u + 1} Λ) v)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj (constantComplex Λ T)) ⟶
      ((derivedHom (ModuleCat.{u + 1} Λ) T').obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C))).obj (constantComplex Λ T') :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
      ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C)).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) v C
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj
          (constantComplex Λ T))).inv ≫
      (L(upperStar (ModuleCat.{u + 1} Λ) v)).map
        ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) C).counit.app
          (constantComplex Λ T)) ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v).hom)

/-- Duality for an ordinary bounded etale complex over the prime field: finite local
constancy of cohomology is preserved, cohomology is the degree-reversed sheaf dual,
and the canonical comparison commutes with every scheme pullback.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-fin-lisse-field-dual.md
(blueprint: lem-fin-lisse-field-dual).

Proof plan:
1. Restrict the K-injective Hom construction to slice sites, using
   lem-pur-kinjective-restrict-localized and the sectionwise Hom-complex differential.
2. A finite locally constant sheaf is locally a finite free prime-field module.
   The bounded-free RHom model computes its dual in degree zero as sheaf Hom;
   its dual is finite locally constant, including rank zero.
3. Induct through the finite standard truncation triangles of C. Derived Hom
   reverses triangles and shifts. The cohomology long exact sequence gives the
   degree-reversing formula and the dual bounds [-b,-a].
4. Exact etale inverse image commutes with cohomology and truncation and preserves
   finite local constancy by pulling back a trivializing covering.
5. Pullback of evaluation defines the displayed comparison. On a finite free
   trivialization it is the identity on coordinate functionals, so geometric
   stalk conservativity makes it an isomorphism for a sheaf and its shifts.
6. Induct again through truncation triangles. Naturality of evaluation gives a
   morphism of dual triangles; the endpoint comparisons and the cohomology long
   exact sequences make the middle comparison an isomorphism. -/
theorem finiteLisseFieldDual
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (_hℓ : IsUnit (ℓ : Γ(T, ⊤)))
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj C))
    (_hlisse : ∀ i : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ i).obj C)) :
    (∀ q : ℤ, Scheme.IsFiniteLocallyConstantSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (((derivedHom
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)))) ∧
    (∀ q : ℤ, Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((derivedHom
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
              (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj
          (𝟙_ (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))))) ∧
    (∀ (T' : Scheme.{u}) (v : T' ⟶ T),
      IsIso (finiteLisseDualPullbackComparison v C)) := by
  sorry

end AlgebraicGeometry.Etale
