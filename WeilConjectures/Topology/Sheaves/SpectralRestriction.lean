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
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Spectral.Basic

/-!
# Restriction of locally constant sheaves to a closed subset of a spectral space

Let `T` be a spectral space and `T₀ ⊆ T` a closed subset such that every irreducible closed
subset `C ⊆ T` meets `T₀` in a nonempty connected set. Then for every locally constant sheaf
of abelian groups `F` on `T`, restriction `Γ(T, F) ⟶ Γ(T₀, F|_{T₀})` is bijective.

The hypothesis that `F` be locally constant cannot be dropped: for `T = 𝔸¹_k`, `T₀ = {0}` and
`F` the skyscraper sheaf at a closed point `y ≠ 0`, one has `Γ(T, F) ≠ 0 = Γ(T₀, F|_{T₀})`.

## Main statements

- `TopCat.Sheaf.bijective_unit_app_top_of_isLocallyConstant`: the restriction is bijective.

## References

- Stacks Project, Lemma 59.82.1, <https://stacks.math.columbia.edu/tag/09ZG>
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

/-- **Zariski restriction on a spectral space.** Let `T` be a spectral space and `T₀ ⊆ T` a
closed subset such that every irreducible closed subset `C ⊆ T` meets `T₀` in a nonempty
connected set. Then for every locally constant sheaf of abelian groups `F` on `T` — every
point has an open neighbourhood `U` on which `F` is isomorphic to a constant sheaf — the
restriction map `Γ(T, F) ⟶ Γ(T₀, F|_{T₀})`, the unit of the adjunction `i⁻¹ ⊣ i_*` for the
inclusion `i : T₀ ⟶ T` evaluated on `T`, is bijective. The zero locus of a section is open
and closed, which gives injectivity; a section over `T₀` extends over a neighbourhood of each
point on which `F` is constant, and the extensions glue.
(blueprint: `lemma-weil-pbc-spectral-restriction`) -/
@[stacks 09ZG]
theorem bijective_unit_app_top_of_isLocallyConstant {T : TopCat.{u}} [SpectralSpace T]
    {T₀ : Set T} (hT₀ : IsClosed T₀)
    (hC : ∀ C : Set T, IsClosed C → IsIrreducible C → IsConnected (C ∩ T₀))
    (F : T.Sheaf AddCommGrpCat.{u})
    (hF : ∀ x : T, ∃ (U : Opens T) (_ : x ∈ U) (M : AddCommGrpCat.{u}),
      Nonempty ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj F ≅
        (constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}).obj M)) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of T₀ ⟶ T)).unit.app
          F).hom.app (op ⊤)).hom :=
  sorry

end TopCat.Sheaf
