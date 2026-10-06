/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Spectral.Basic

/-!
# Restriction of sheaves to a closed subset of a spectral space

Let `T` be a spectral space and `T₀ ⊆ T` a closed subset such that every irreducible closed
subset `C ⊆ T` meets `T₀` in a nonempty connected set. Then for every sheaf of abelian
groups `F` on `T`, restriction `Γ(T, F) ⟶ Γ(T₀, F|_{T₀})` is bijective.

## Main statements

- `TopCat.Sheaf.bijective_unit_app_top`: the restriction is bijective.

## References

- Stacks Project, Lemma 59.82.1, <https://stacks.math.columbia.edu/tag/09ZG>
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

/-- **Zariski restriction on a spectral space.** Let `T` be a spectral space and `T₀ ⊆ T` a
closed subset such that every irreducible closed subset `C ⊆ T` meets `T₀` in a nonempty
connected set. Then for every sheaf of abelian groups `F` on `T`, the restriction map
`Γ(T, F) ⟶ Γ(T₀, F|_{T₀})`, the unit of the adjunction `i⁻¹ ⊣ i_*` for the inclusion
`i : T₀ ⟶ T` evaluated on `T`, is bijective.
(blueprint: `lemma-weil-pbc-spectral-restriction`) -/
@[stacks 09ZG]
theorem bijective_unit_app_top {T : TopCat.{u}} [SpectralSpace T]
    {T₀ : Set T} (hT₀ : IsClosed T₀)
    (hC : ∀ C : Set T, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    (F : T.Sheaf AddCommGrpCat.{u}) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of T₀ ⟶ T)).unit.app
          F).hom.app (op ⊤)).hom :=
  sorry

end TopCat.Sheaf
