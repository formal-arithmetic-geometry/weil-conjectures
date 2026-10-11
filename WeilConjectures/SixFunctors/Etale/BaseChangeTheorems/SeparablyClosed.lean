/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Sections of étale sheaves after an extension of a separably closed base field

Let `k` be a separably closed field, `K/k` a field extension, `X` a scheme over `k` and
`F` an étale sheaf on `X`. Pullback along the projection `X_K = X ×_k K ⟶ X` is a bijection
`Γ(X, F) ≅ Γ(X_K, F|_{X_K})`.

## References

- Stacks Project, Lemma 59.39.4, <https://stacks.math.columbia.edu/tag/0A3I>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Sections are invariant under extension of a separably closed base field.** Let `k` be a
separably closed field, `K/k` a field extension and `p : X ⟶ Spec k` quasi-compact and
quasi-separated. For every étale sheaf `F` of `Λ`-modules on `X`, pullback along the projection
`X ×_k K ⟶ X` is an isomorphism `Γ(X, F) ≅ Γ(X ×_k K, F|)`. -/
@[stacks 0A3I]
theorem Etale.isIso_globalSectionsUpperStarMap_of_isSepClosed {k K : Type u} [Field k] [Field K]
    [Algebra k K] [IsSepClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [QuasiCompact p]
    [QuasiSeparated p] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ)
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K)))) F) :=
  sorry

end AlgebraicGeometry
