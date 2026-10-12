/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Mayer–Vietoris for the étale cohomology of a Zariski cover by two opens

Let `X` be a scheme covered by two open subschemes `U` and `V`. The étale cohomology of an
abelian sheaf `G` on `X` sits in the Mayer–Vietoris long exact sequence
`⋯ → Hⁿ(X, G) → Hⁿ(U, G) ⊕ Hⁿ(V, G) → Hⁿ(U ∩ V, G) → Hⁿ⁺¹(X, G) → ⋯`. We record the
vanishing statement it implies.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_succ_of_sup_eq_top`: if `Hⁿ⁺¹(U, G)`, `Hⁿ⁺¹(V, G)`
  and `Hⁿ(U ∩ V, G)` vanish, so does `Hⁿ⁺¹(X, G)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- **Mayer–Vietoris vanishing.** Let `X = U ∪ V` be a cover by two open subschemes and `G` an
abelian étale sheaf on `X`. If `Hⁿ⁺¹(U, G|_U)`, `Hⁿ⁺¹(V, G|_V)` and `Hⁿ(U ∩ V, G|_{U ∩ V})`
vanish, then so does `Hⁿ⁺¹(X, G)`. -/
theorem subsingleton_H_succ_of_sup_eq_top {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (hU : Subsingleton (Sheaf.H ((U.ι)^*[AddCommGrpCat.{u + 1}].obj G) (n + 1)))
    (hV : Subsingleton (Sheaf.H ((V.ι)^*[AddCommGrpCat.{u + 1}].obj G) (n + 1)))
    (hW : Subsingleton (Sheaf.H (((U ⊓ V).ι)^*[AddCommGrpCat.{u + 1}].obj G) n)) :
    Subsingleton (Sheaf.H G (n + 1)) :=
  sorry

end AlgebraicGeometry.Etale
