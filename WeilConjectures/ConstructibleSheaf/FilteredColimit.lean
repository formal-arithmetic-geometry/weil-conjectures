/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Sheaves of modules are filtered colimits of constructible sheaves

On a quasi-compact quasi-separated scheme `X`, every sheaf of modules over a Noetherian ring
`Λ` on `X_ét` is a filtered colimit of constructible sheaves
(`AlgebraicGeometry.Etale.exists_isColimit_isConstructibleSheaf`).

This is the classical input `lem-kun-03sa` of the blueprint (Stacks Project Tag 03SA), for which
the blueprint records no proof; it is stated here for quasi-compact quasi-separated schemes, the
generality of the Stacks project.

## References

- Stacks Project, Lemma 59.73.2, <https://stacks.math.columbia.edu/tag/03SA>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-03sa`: on a quasi-compact quasi-separated scheme, every sheaf of modules
over a Noetherian ring is a filtered colimit of constructible sheaves. -/
@[stacks 03SA]
theorem Etale.exists_isColimit_isConstructibleSheaf [IsNoetherianRing Λ] {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (_ : ∀ j, IsConstructibleSheaf (D.obj j)) (c : Cocone D), c.pt = F ∧ Nonempty (IsColimit c) :=
  sorry

end AlgebraicGeometry
