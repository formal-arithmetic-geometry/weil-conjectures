/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteEtaleIntegralGenericClopen
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssembly

/-! Clopen source decompositions over a finite reduced base stratification. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The geometric Noetherian induction and generic-fibre argument underlying the adapted
base-stratification theorem. It produces reduced base strata and clopen scheme pieces whose
ranges are the exact inverse images of the prescribed source strata.

Source: Stacks Project, Tag 095H and the geometric generic-interiors argument in the blueprint
(blueprint: lem-a1-finite-etale-base-clopen-stratification).

Proof: perform Noetherian induction on closed subsets of the base. On an integral affine open,
remove the finite image of the complement of the generic-fibre interiors; the resulting open
has clopen inverse images of all source strata. Apply the induction hypothesis to the closed
complement and glue the pieces. The scheme coproduct is the colimit of the finite disjoint open
cover, and reduction is retained on every base stratum. -/
theorem finite_etale_exists_base_clopen_stratification
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [IsLocallyNoetherian Y] [CompactSpace Y] (S : FiniteLocallyClosedStratification X) :
    ∃ T : FiniteLocallyClosedStratification Y,
      (∀ a : Fin T.n, IsReduced (T.domain a)) ∧
      ∀ a : Fin T.n,
        ∃ (C : Fin S.n → Scheme.{u})
          (j : ∀ i : Fin S.n, C i ⟶ pullback f (T.immersion a)),
          (∀ i : Fin S.n, IsOpenImmersion (j i) ∧ IsClosedImmersion (j i)) ∧
          Nonempty (IsColimit (Cofan.mk (pullback f (T.immersion a)) j)) ∧
          ∀ i : Fin S.n,
            Set.range (j i) =
              (pullback.fst f (T.immersion a)) ⁻¹' S.stratum i := by
  apply exists_reduced_stratification_of_integral_affine_generic Y
    (fun B t ↦ ∃ (C : Fin S.n → Scheme.{u})
      (j : ∀ i : Fin S.n, C i ⟶ pullback f t),
      (∀ i : Fin S.n, IsOpenImmersion (j i) ∧ IsClosedImmersion (j i)) ∧
      Nonempty (IsColimit (Cofan.mk (pullback f t) j)) ∧
      ∀ i : Fin S.n, Set.range (j i) = (pullback.fst f t) ⁻¹' S.stratum i)
  intro B _ _ _ t ht
  exact finite_etale_integral_generic_clopen f S B t ht

end AlgebraicGeometry.Scheme
