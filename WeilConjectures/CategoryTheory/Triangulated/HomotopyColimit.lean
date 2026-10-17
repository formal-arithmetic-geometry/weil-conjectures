/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Homotopy colimits of sequences in a pretriangulated category

Let `F : ℕ ⥤ C` be a sequence `F₀ ⟶ F₁ ⟶ F₂ ⟶ ⋯` in a pretriangulated category. Its
*homotopy colimit* `hocolim F` is characterised, up to non-unique isomorphism, by the
distinguished triangle

```
  ∐ₙ Fₙ ──1 - t──▶ ∐ₙ Fₙ ⟶ hocolim F ⟶ (∐ₙ Fₙ)⟦1⟧
```

where `t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` maps the summand `Fₙ` to the summand `Fₙ₊₁` by the transition map.
This is dual to `CategoryTheory.Pretriangulated.IsHomotopyLimit`.

## Main definitions

- `CategoryTheory.Limits.sequenceShift`: the map `t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ`.
- `CategoryTheory.Pretriangulated.IsHomotopyColimit`: a cocone over a sequence is a homotopy
  colimit cocone if its legs fit into a distinguished triangle as above.

## Main statements

- `CategoryTheory.Pretriangulated.IsHomotopyColimit.of_iso`: being a homotopy colimit cocone is
  invariant under isomorphisms of sequences and of cocone points.
-/

@[expose] public section

namespace CategoryTheory

open Limits

namespace Limits

variable {C : Type*} [Category* C]

/-- The shift endomorphism `t : ∐ₙ Fₙ ⟶ ∐ₙ Fₙ` of a coproduct of the terms of a sequence
`F : ℕ ⥤ C`, mapping the summand `Fₙ` to the summand `Fₙ₊₁` by the transition map. -/
noncomputable def sequenceShift {F : ℕ ⥤ C} {P : Cofan fun n : ℕ ↦ F.obj n}
    (hP : IsColimit P) : P.pt ⟶ P.pt :=
  Cofan.IsColimit.desc hP fun n ↦ F.map (homOfLE n.le_succ) ≫ P.inj (n + 1)

@[reassoc (attr := simp)]
lemma inj_sequenceShift {F : ℕ ⥤ C} {P : Cofan fun n : ℕ ↦ F.obj n} (hP : IsColimit P)
    (n : ℕ) : P.inj n ≫ sequenceShift hP = F.map (homOfLE n.le_succ) ≫ P.inj (n + 1) :=
  Cofan.IsColimit.fac hP _ n

end Limits

namespace Pretriangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Blueprint `def-kun-truncations`: Truncations and homotopy colimits (the homotopy colimit
part; the stupid and canonical truncations are `HomologicalComplex.stupidTrunc`,
`CochainComplex.truncLE`, `CochainComplex.truncGE` and the truncation functors
`TStructure.truncLE`, `TStructure.truncGE` of the canonical t-structure
`DerivedCategory.TStructure.t`, with the truncation triangle
`TStructure.triangleLEGE_distinguished`).

A cocone `c` over a sequence `F : ℕ ⥤ C` in a pretriangulated category is a *homotopy colimit*
cocone if, for a coproduct `∐ₙ Fₙ`, the triangle

```
  ∐ₙ Fₙ ──1 - t──▶ ∐ₙ Fₙ ──(c.ι n)ₙ──▶ c.pt ──δ──▶ (∐ₙ Fₙ)⟦1⟧
```

is distinguished for some `δ`, where `t` is `CategoryTheory.Limits.sequenceShift`. The point of
a homotopy colimit cocone is then `hocolim F`, determined up to non-unique isomorphism. -/
def IsHomotopyColimit {F : ℕ ⥤ C} (c : Cocone F) : Prop :=
  ∃ (P : Cofan fun n : ℕ ↦ F.obj n) (hP : IsColimit P) (δ : c.pt ⟶ P.pt⟦(1 : ℤ)⟧),
    Triangle.mk (𝟙 P.pt - sequenceShift hP) (Cofan.IsColimit.desc hP fun n ↦ c.ι.app n) δ ∈
      distTriang C

namespace IsHomotopyColimit

/-- Being a homotopy colimit cocone is invariant under isomorphisms: if `c` is a homotopy
colimit cocone over `F`, `e : F ≅ G` and `eι : c.pt ≅ c'.pt` are compatible with the legs, then
`c'` is a homotopy colimit cocone over `G`. -/
lemma of_iso {F G : ℕ ⥤ C} (e : F ≅ G) {c : Cocone F} (hc : IsHomotopyColimit c)
    (c' : Cocone G) (eι : c.pt ≅ c'.pt)
    (h : ∀ n : ℕ, c.ι.app n ≫ eι.hom = e.hom.app n ≫ c'.ι.app n) :
    IsHomotopyColimit c' := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  let P' : Cofan fun n : ℕ ↦ G.obj n := Cofan.mk P.pt fun n ↦ e.inv.app n ≫ P.inj n
  have hP' : IsColimit P' := Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc hP fun n ↦ e.hom.app n ≫ s.inj n)
    (fun s n ↦ by simp [P'])
    (fun s m hm ↦ Cofan.IsColimit.hom_ext hP _ _ fun n ↦ by
      simp [← hm n, P'])
  have ht : sequenceShift hP' = sequenceShift hP := Cofan.IsColimit.hom_ext hP' _ _ fun n ↦ by
    rw [inj_sequenceShift]
    simp [P', NatTrans.naturality_assoc]
  refine ⟨P', hP', eι.inv ≫ δ,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eι.symm
      ?_ ?_ ?_)⟩
  · simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp, ht]
    rfl
  · refine Cofan.IsColimit.hom_ext hP' _ _ fun n ↦ ?_
    simp only [Triangle.mk_obj₂, Triangle.mk_obj₃, Triangle.mk_mor₂, Iso.refl_hom,
      Category.id_comp, Iso.symm_hom, Cofan.IsColimit.fac_assoc]
    simp only [P', cofan_mk_inj, Category.assoc, Cofan.IsColimit.fac]
    rw [← cancel_mono eι.hom]
    simp [h]
  · simp

end IsHomotopyColimit

end Pretriangulated

end CategoryTheory
