/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts

/-!
# Conditional passage from heart coproducts to a localizing hull

Source: `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/
ProperLowerStarCoproducts.lean`, declaration
`AlgebraicGeometry.ProEtale.CondensedRing.
preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar`,
lines 98--124; `constructibleCoproductClosure` lines 72--76 (blueprint:
lem-dla1-proper-heart-localizing-coproduct-criterion).
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Conditional localizing-coproduct criterion for the derived module pushforward.

Let `Λ` be a commutative condensed ring and `p : Z ⟶ Y` any morphism of schemes. Suppose
`Rp_*` sends every object of `constructibleCoproductClosure Λ Z` (the weak-Serre,
`Type (u + 1)`-coproduct closure of the constructible module objects), placed in degree `0`,
into degrees `≤ d` for one `d`, and that the canonical comparison
`∐ Rp_*(N_j[0]) ⟶ Rp_*(∐ N_j[0])` is an isomorphism for every `Type (u + 1)`-family of such
objects. Then the canonical comparison `∐ Rp_* K_j ⟶ Rp_*(∐ K_j)` is an isomorphism for
every `Type (u + 1)`-family (possibly empty) in the localizing closure of the bounded
constructible complexes.

Source: `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/
ProperLowerStarCoproducts.lean`, lines 98--124: the direct `IsIso` formulation of
`AlgebraicGeometry.ProEtale.CondensedRing.
preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar`
(blueprint: lem-dla1-proper-heart-localizing-coproduct-criterion).

Proof:
1. By the sheaf-tensor theorem with coefficients `Ab` and the module-object Grothendieck
   theorem, `A_Z` and `A_Y` are Grothendieck abelian; small direct sums are filtered colimits
   of finite sums, hence exact. They have enough injectives and K-injective resolutions.
2. Both hearts have exact countable products: reconstruct the section-ring sheaf `B_T` of
   `Λ_T`, identify internal modules with `B_T`-module sheaves by the section-action
   equivalence (its hypotheses by the sheaf-tensor theorem), apply exact products for an
   arbitrary sheaf of rings, and transport kernels, cokernels and products back.
3. `G = Rp_*` is the total derived functor of the additive module pushforward: it is
   triangulated, commutes with shifts, and preserves countable products as right adjoint of
   `Lp^*`. It is left t-exact: `K ∈ D^{≥a}` has a K-injective bounded-below injective model
   `I` with `I^q = 0` for `q < a`, and `G K ≅ p_* I` vanishes below `a`.
4. Let `E` be the complexes with all cohomology in `P_Z`. By the weak-Serre cohomology
   theorem `E` is full, replete and triangulated; by exactness of sums (Step 1) cohomology
   commutes with sums, so `E` is closed under `Type (u + 1)`-sums; good truncations preserve
   `E`; bounded constructible complexes lie in `E`. Minimality of the localizing closure gives
   `Loc(B_Z) ⊆ E`.
5. The heart hypothesis is that of the finite-window heart coproduct lemma for
   `C = A_Z`, `D = A_Y`, `G`, `P = P_Z`; it gives the comparison for every family in `E`
   with cohomology in a common finite interval `[a, b]`.
6. For `X ∈ E` with `X ≤ b`, every `τ_{≥ -n} X` is bounded, in `E` and `≤ b`, so the bounded
   heart-amplitude devissage gives `G(τ_{≥ -n} X) ≤ b + d`; left completeness (Steps 1--3)
   gives `G X ≤ b + d + 1`. Put `e = d + 1`.
7. The finite-amplitude coproduct-window lemma for `E`, `G`, `e` (hypotheses from Steps 3--6)
   gives the canonical comparison for every `Type (u + 1)`-family in `E`, in particular in
   `Loc(B_Z)`; the empty family is included since both empty sums are zero. -/
theorem properHeartLocalizingCoproductCriterion
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (hbound : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d)
    (hsum : ∀ (J : Type (u + 1))
      (N : J → Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z)),
      (∀ j, constructibleCoproductClosure Λ Z (N j)) →
        IsIso (sigmaComparison R((p)_*⟦Λ⟧)
          (fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j))))
    (J : Type (u + 1))
    (K : J → DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK : ∀ j, (boundedConstructible (condensedRingObj Λ Z)).localizingClosure (K j)) :
    IsIso (sigmaComparison R((p)_*⟦Λ⟧) K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
