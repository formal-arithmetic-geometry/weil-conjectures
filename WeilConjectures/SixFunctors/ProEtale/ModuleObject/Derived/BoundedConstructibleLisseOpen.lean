/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!
# Bounded constructible complexes are lisse on a dense open

Let `Λ` be a commutative condensed ring and `D` a nonempty scheme with noetherian underlying
space. For a bounded constructible complex `K` on `D` there is a nonempty open `V` of `D` and a
surjective closed immersion `c : E ⟶ V` such that every cohomology sheaf of the pullback of `K`
to `E` is pro-étale locally finitely presented
(`ProEtale.CondensedRing.exists_isLocallyFinitelyPresented_homology_upperStar`). The scheme `E` is
`V` up to nilpotents: it is the intersection of `V` with strata of stratifications adapted to the
finitely many nonzero cohomology sheaves of `K`, which carry their reduced scheme structures.

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- **A bounded constructible complex is lisse on a dense open, up to nilpotents**: on a nonempty
scheme `D` with noetherian underlying space, a bounded constructible complex `K` has a nonempty
open `V` and a surjective closed immersion `c : E ⟶ V` such that all cohomology sheaves of the
pullback of `K` to `E` are pro-étale locally finitely presented. -/
theorem exists_isLocallyFinitelyPresented_homology_upperStar {D : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace D] [Nonempty D]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D))}
    (hK : boundedConstructible (condensedRingObj Λ D) K) :
    ∃ (V : D.Opens) (E : Scheme.{u}) (c : E ⟶ V), (V : Set D).Nonempty ∧
      IsClosedImmersion c ∧ Surjective c ∧ ∀ n : ℤ,
        IsLocallyFinitelyPresented (condensedRingObj Λ E)
          ((DerivedCategory.homologyFunctor _ n).obj ((L(((c ≫ V.ι))^*⟦Λ⟧)).obj K)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
