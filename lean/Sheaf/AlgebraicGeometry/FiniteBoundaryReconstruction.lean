/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import Sheaf.AlgebraicGeometry.FiniteReflectsBoundedConstructible
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Recovering bounded constructibility at a finite boundary

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-boundary-reconstruction.md`
(blueprint: lem-fin-finite-boundary-reconstruction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A bounded below étale complex is bounded constructible if its open restriction and
proper direct image are bounded constructible, and the closed boundary is finite over the
base. Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-fin-finite-boundary-reconstruction.md`
(blueprint: lem-fin-finite-boundary-reconstruction).

Proof plan:
1. The finite-type schemes over the field are Noetherian; so is the finite boundary over S
   (`lem-weil-pbc-finite-type-over-noetherian`, `def-weil-finite-integral-morphism`).
2. Open-closed recollement gives the triangle A → K → C → A[1], with A = a_!a^*K and
   C = i_*i^*K (`lem-cbc-open-closed-recollement`). Exact inverse image and closed direct
   image identify C with Ri_*i^*K (`prop-weil-pbc-inverse-image-modules-exact`,
   `lem-weil-pbc-exact-functor-derived-functor`).
3. Exact extension by zero preserves the cohomology and finite support interval of a^*K,
   making A bounded constructible (`lem-fin-extension-by-zero`,
   `lem-weil-pbc-extension-by-zero-exact`, `lem-weil-pbc-exact-functor-complex-cohomology`).
4. Apply Rb_* to the triangle. K-injective resolutions on a small-site skeleton and bounded
   below injective representatives identify the triangulated right derived functor with
   the bounded below pushforward (`lem-pc-right-derived-functor-triangulated`,
   `def-weil-size-convention`, `prop-pur-kinjective-resolutions-exist`,
   `lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-dplus-injective-representative`,
   `def-weil-pbc-direct-image`). Derived composition identifies the third term with
   R(bi)_*i^*K (`lem-weil-derived-direct-image-composition`, ordinary étale clause).
5. Proper pushforward makes Rb_*A bounded constructible
   (`lem-fin-proper-bounded-constructible`). Together with the hypothesis on Rb_*K, the
   long exact cohomology sequence bounds the third term: if both supports lie in [r,s],
   its support lies in [r-1,s] (`lem-sf-derived-homology-long-exact`). Now use the
   triangulated constructible subcategory (`prop-constructible-derived-subcategory`).
6. Exact inverse image preserves the lower bound of K. Finite reflection therefore makes
   i^*K bounded constructible (`lem-fin-finite-reflects-derived`).
7. Exact closed direct image makes C bounded constructible (`lem-fin-closed-immersion`).
   The original triangle first bounds K by the cohomology long exact sequence and then
   proves its constructibility by the triangulated constructible subcategory. -/
theorem isBoundedConstructible_of_finite_boundary
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Y S G Z : Scheme.{u}}
    [Y.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (b : Y ⟶ S) [b.IsOver (Spec (.of k))] [IsProper b]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ S)
    (a : G ⟶ Y) [IsOpenImmersion a] (i : Z ⟶ Y) [IsClosedImmersion i]
    (hcomplement : Set.range i.base = (Set.range a.base)ᶜ) [IsFinite (i ≫ b)]
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hopen : DerivedCategory.isBoundedConstructible Λ G
      ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory.obj K.obj))
    (hpush : DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) b).obj K).obj) :
    DerivedCategory.isBoundedConstructible Λ Y K.obj := by
  sorry

end AlgebraicGeometry.Etale
