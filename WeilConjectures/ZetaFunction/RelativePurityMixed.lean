/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.RelativePurity

/-!
# Higher direct images under a smooth proper morphism are mixed of a single weight

Let `f : X₀ ⟶ Y₀` be a smooth proper morphism of pure relative dimension `d` and `F` a lisse Weil
sheaf on `X₀`, punctually `ι`-pure of weight `w`. By relative purity
(`AlgebraicGeometry.WeilSheaf.smooth_proper_relative_purity`) the sheaf `Rⁱf₀*F` is punctually
`ι`-pure of weight `w + i`; in particular it is mixed of the single weight `w + i`: it has a
finite filtration all of whose successive quotients are punctually `ι`-pure of weight `w + i`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.exists_filtration`: a punctually pure
  sheaf of weight `w` is mixed of the single weight `w`.
- `AlgebraicGeometry.WeilSheaf.exists_filtration_isPunctuallyPureOfWeight_higherLowerStar`:
  blueprint `theorem-purity-higher-direct-images-under--3`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- A Weil sheaf punctually `ι`-pure of weight `w` is mixed of the single weight `w`: it has a
finite filtration (namely `0 ⊆ F`) whose successive quotients are punctually `ι`-pure of
weight `w`. -/
theorem IsPunctuallyPureOfWeight.exists_filtration {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    ∃ (n : ℕ) (G : Fin (n + 1) → WeilSheaf k₀ l X)
      (φ : ∀ j : Fin n, G j.castSucc ⟶ G j.succ),
        IsZero (G 0) ∧ IsIsomorphic (G (Fin.last n)) F ∧ (∀ j, Mono (φ j)) ∧
          ∀ j, (cokernel (φ j)).IsPunctuallyPureOfWeight ι w := by
  let P : ObjectProperty (WeilSheaf k₀ l X) := fun G ↦ G.IsPunctuallyPureOfWeight ι w
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ IsPunctuallyPureOfWeight.of_epi e.hom h⟩
  exact (ObjectProperty.filtrationClosure_iff (P := P)).1 (P.le_filtrationClosure _ h)

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `theorem-purity-higher-direct-images-under--3`: for a smooth proper morphism
`f : X₀ ⟶ Y₀` of pure relative dimension `d` and a lisse Weil sheaf `F` punctually `ι`-pure of
weight `w`, the sheaf `Rⁱf₀!F = Rⁱf₀*F` is mixed of the single weight `w + i`: it has a finite
filtration whose successive quotients are all punctually `ι`-pure of weight `w + i`. This follows
from its punctual purity of weight `w + i`
(`AlgebraicGeometry.WeilSheaf.smooth_proper_relative_purity`). -/
theorem exists_filtration_isPunctuallyPureOfWeight_higherLowerStar {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    ∃ (n : ℕ) (G : Fin (n + 1) → WeilSheaf k₀ l Y)
      (φ : ∀ j : Fin n, G j.castSucc ⟶ G j.succ),
        IsZero (G 0) ∧ IsIsomorphic (G (Fin.last n)) ((higherLowerStar f i).obj F) ∧
          (∀ j, Mono (φ j)) ∧ ∀ j, (cokernel (φ j)).IsPunctuallyPureOfWeight ι (w + i) :=
  (isPunctuallyPureOfWeight_higherLowerStar f d hF hw i).exists_filtration

end WeilSheaf

end AlgebraicGeometry
