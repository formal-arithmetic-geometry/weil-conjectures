/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.ProperIndConstructibleBoundedBelow
public import Sheaf.Paper.AmbientIndDerivedSums
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.CategoryTheory.Monoidal.Mod
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.LowerTruncationStepTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Proper direct image of arbitrary ind-constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-unbounded-window,
`sk-lem-proper-unbounded-window-arbitrary.md` and its proof
(blueprint: det-proper-unbounded-window-arbitrary).

The two statements retain the actual condensed coefficients, respectively a finite
subextension of ℚ_ℓ and the finite-subextension-valued condensed algebraic closure.
IndCons is the recorded replete small filtered-colimit closure of finite constant-model
constructible modules. Dic is expressed as this property of every cohomology object.
The stabilization arrow is the cohomology of the direct image of the canonical truncation
projection, without replacing it by an unspecified isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper direct image for a finite subextension of ℚ_ℓ: eventual truncation stabilization,
ind-constructible cohomology, and both cohomological amplitude bounds, for arbitrary K.
Source: blueprint sk-lem-proper-unbounded-window-arbitrary, all four proof paragraphs;
standing hypotheses inherited from det-proper-unbounded-window-bounded-below
(blueprint: det-proper-unbounded-window-arbitrary).

Proof (the six steps of the node):
1. Identify the internal module objects with sheaves of modules by
   sk-def-sfb-module-objects and sk-def-sfb-sheaf-tensor. Their categories are
   Grothendieck abelian by lem-weil-pbc-ring-sheaves-grothendieck and have K-injective
   resolutions by lem-sfb-grothendieck-k-injective. Put A_n = tau_ge(-n) K and
   L_n = Rp_* A_n. Products exist by det-pe-products-derived. The adjunction
   def-sfb-module-derived-pushpull-adjunction makes Rp_* product-preserving, including
   its projections. The additive module direct image is triangulated after deriving
   by lem-pc-right-derived-functor-triangulated.
2. det-pe-left-complete-iso identifies K with the derived limit of A_n. Apply
   lem-pc-homotopy-limit-map to the entire cone and Rp_*. This gives the Roos triangle
   Rp_*K --> product L_n --(1-T)--> product L_n --> (Rp_*K)[1] of
   def-weil-derived-limit, with projections exactly Rp_*(K --> A_n).
3. det-ambient-ind-derived-sums keeps A_n in Dic. The fibre of A_(n+1) --> A_n is
   H^(-n-1)(K)[n+1] by lem-pc-derived-lower-truncation-step-triangle. Its pushforward
   is supported in [-n-1, 2d-n] by det-proper-unbounded-window-bounded-below.
   lem-sf-derived-homology-long-exact makes the transitions of H^q(L_n) and
   H^(q-1)(L_n) invertible for n >= N_0 = max(0, 2d-q+2).
4. For either tower t_i : M_(i+1) --> M_i, fix x_(N_0) = 0. Given y, recursively
   set x_i = y_i + t_i x_(i+1) for i < N_0 descending, and
   x_(i+1) = t_i inverse (x_i-y_i) for i >= N_0 ascending. Each coordinate is a
   finite natural linear expression, giving a sheaf map splitting 1-T. Its cokernel
   vanishes. The compatible-tuples limit of def-pur-sheaf-inverse-limit projects
   isomorphically onto every M_n with n >= N_0, by the same tail inverses and the
   original maps below the tail; no earlier transition is assumed surjective.
5. Apply cohomology to the Roos triangle. det-pe-products-derived identifies the
   cohomology of the product with the product of cohomologies, with projections.
   lem-sf-derived-homology-long-exact gives the Milnor short exact sequence with
   left term coker(1-T) in degree q-1 and right term lim H^q(L_n). Step 4 kills
   the left term and identifies each sufficiently late right projection with an
   isomorphism. Step 2 identifies the composite with H^q(Rp_*(K --> A_n)).
6. For fixed q choose such n. The bounded-below theorem puts H^q(L_n) in IndCons;
   transport across step 5 gives H^q(Rp_*K) in IndCons. If K is at most b, A_n is
   too, so H^q(L_n) vanishes above b+2d+1 and the same transport gives the upper
   bound. If K is at least a, it is already bounded below and the lower bound
   follows directly from det-proper-unbounded-window-bounded-below.
-/
theorem proper_indConstructible_unbounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    :
    (∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) ∧
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E) p).obj
        K).IsLE
        (b + 2 * d + 1)) := by
  sorry

/-- Proper direct image for the condensed algebraic closure: eventual truncation stabilization,
ind-constructible cohomology, and both cohomological amplitude bounds, for arbitrary K.
Source: blueprint sk-lem-proper-unbounded-window-arbitrary, all four proof paragraphs;
standing hypotheses inherited from det-proper-unbounded-window-bounded-below
(blueprint: det-proper-unbounded-window-arbitrary).

Proof (the six steps of the node):
1. Identify the internal module objects with sheaves of modules by
   sk-def-sfb-module-objects and sk-def-sfb-sheaf-tensor. Their categories are
   Grothendieck abelian by lem-weil-pbc-ring-sheaves-grothendieck and have K-injective
   resolutions by lem-sfb-grothendieck-k-injective. Put A_n = tau_ge(-n) K and
   L_n = Rp_* A_n. Products exist by det-pe-products-derived. The adjunction
   def-sfb-module-derived-pushpull-adjunction makes Rp_* product-preserving, including
   its projections. The additive module direct image is triangulated after deriving
   by lem-pc-right-derived-functor-triangulated.
2. det-pe-left-complete-iso identifies K with the derived limit of A_n. Apply
   lem-pc-homotopy-limit-map to the entire cone and Rp_*. This gives the Roos triangle
   Rp_*K --> product L_n --(1-T)--> product L_n --> (Rp_*K)[1] of
   def-weil-derived-limit, with projections exactly Rp_*(K --> A_n).
3. det-ambient-ind-derived-sums keeps A_n in Dic. The fibre of A_(n+1) --> A_n is
   H^(-n-1)(K)[n+1] by lem-pc-derived-lower-truncation-step-triangle. Its pushforward
   is supported in [-n-1, 2d-n] by det-proper-unbounded-window-bounded-below.
   lem-sf-derived-homology-long-exact makes the transitions of H^q(L_n) and
   H^(q-1)(L_n) invertible for n >= N_0 = max(0, 2d-q+2).
4. For either tower t_i : M_(i+1) --> M_i, fix x_(N_0) = 0. Given y, recursively
   set x_i = y_i + t_i x_(i+1) for i < N_0 descending, and
   x_(i+1) = t_i inverse (x_i-y_i) for i >= N_0 ascending. Each coordinate is a
   finite natural linear expression, giving a sheaf map splitting 1-T. Its cokernel
   vanishes. The compatible-tuples limit of def-pur-sheaf-inverse-limit projects
   isomorphically onto every M_n with n >= N_0, by the same tail inverses and the
   original maps below the tail; no earlier transition is assumed surjective.
5. Apply cohomology to the Roos triangle. det-pe-products-derived identifies the
   cohomology of the product with the product of cohomologies, with projections.
   lem-sf-derived-homology-long-exact gives the Milnor short exact sequence with
   left term coker(1-T) in degree q-1 and right term lim H^q(L_n). Step 4 kills
   the left term and identifies each sufficiently late right projection with an
   isomorphism. Step 2 identifies the composite with H^q(Rp_*(K --> A_n)).
6. For fixed q choose such n. The bounded-below theorem puts H^q(L_n) in IndCons;
   transport across step 5 gives H^q(Rp_*K) in IndCons. If K is at most b, A_n is
   too, so H^q(L_n) vanishes above b+2d+1 and the same transport gives the upper
   bound. If K is at least a, it is already bounded below and the lower bound
   follows directly from det-proper-unbounded-window-bounded-below.
-/
theorem proper_indConstructible_unbounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    :
    (∀ q : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) ∧
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) p).obj
        K).IsLE
        (b + 2 * d + 1)) := by
  sorry

end AlgebraicGeometry.ProEtale
