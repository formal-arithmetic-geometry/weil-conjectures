/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition

/-!
# Local triviality for bounded-image condensed algebraic-closure coefficients

The coefficient ring is the bounded-finite-subextension-image condensed ring, pulled
back from the profinite point. Presentations and restrictions are ordinary module
sheaf constructions; there is no completeness hypothesis.

## References

* Bhatt--Scholze, Definition 6.8.3
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Local finite presentation implies pro-etale local finite freeness for the
bounded-image condensed algebraic closure of the l-adic field
(Bhatt--Scholze, Definition 6.8.3). -/
theorem condensedQbar_lfp_locally_free (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) P) :
    ∃ 𝒲 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒲.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (𝒲.f i)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (𝒲.X i)) r) := by
  classical
  rcases hP with ⟨𝒰, h𝒰⟩
  have h0 (i : 𝒰.I₀) := exists_condensedQbar_finiteFree_refinement ℓ X (𝒰.X i)
    (𝒰.f i) (𝒰.forgetQc.map_prop i) P (h𝒰 i)
  exact exists_condensedQbar_refinement_of_local ℓ X P 𝒰 h0

end AlgebraicGeometry.ProEtale
