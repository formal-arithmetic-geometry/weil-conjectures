/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials

/-!
# Basic opens of the standard charts of the projective line

Let `ℙ¹_k = ProjectiveLine (Spec k)` with its standard charts `D₊(xᵢ) ≅ Spec k[t]`. For a
polynomial `g ≠ 0` we consider the basic open `Dᵢ(g) ⊆ D₊(xᵢ)` where `g(t)` does not vanish. These
opens form a basis of the topology of `ℙ¹_k`, their rings of sections are the localizations
`k[t]_g`, and over each of them `Ω¹_{ℙ¹/k}` is free on `dt`.

## Main definitions and results

- `AlgebraicGeometry.ProjectiveLine.chartBasicOpen`: the basic open `Dᵢ(g)`.
- `AlgebraicGeometry.ProjectiveLine.polyToChartBasicOpen`: the ring map `k[t] → Γ(Dᵢ(g))`.
- `AlgebraicGeometry.ProjectiveLine.isLocalization_chartBasicOpen`: `Γ(Dᵢ(g)) = k[t]_g`.
- `AlgebraicGeometry.ProjectiveLine.isBasis_chartBasicOpen`: the `Dᵢ(g)` form a basis.
- `AlgebraicGeometry.ProjectiveLine.isFreeGenerator_sectionsD_polyToChartBasicOpen_X`: `dt` is a
  free generator of `Ω¹_{ℙ¹/k}` over `Dᵢ(g)`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite Polynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules

variable (k : Type u) [Field k]

/-- The basic open `Dᵢ(g)` of the standard chart `D₊(xᵢ) = Spec k[t]` of `ℙ¹_k`, `t = x_{1-i}/xᵢ`,
where the polynomial `g(t)` does not vanish. -/
abbrev chartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    (ProjectiveLine (Spec (.of k))).Opens :=
  (ProjectiveLine (Spec (.of k))).basicOpen (polyEquivChart k (ne_other i) g)

lemma chartBasicOpen_le (i : ULift.{u} (Fin 2)) (g : k[X]) :
    chartBasicOpen k i g ≤ chart k {i} :=
  (ProjectiveLine (Spec (.of k))).basicOpen_le _

lemma isAffineOpen_chartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    IsAffineOpen (chartBasicOpen k i g) :=
  (isAffineOpen_chart k (Set.singleton_nonempty i)).basicOpen _

/-- The ring map `k[t] → Γ(ℙ¹_k, Dᵢ(g))`. -/
def polyToChartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    k[X] →+* Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g) :=
  ((ProjectiveLine (Spec (.of k))).presheaf.map (homOfLE (chartBasicOpen_le k i g)).op).hom.comp
    (polyEquivChart k (ne_other i)).toRingHom

/-- The constants of `k[t]` go to the structure map `k → Γ(ℙ¹_k, Dᵢ(g))`. -/
lemma polyToChartBasicOpen_C (i : ULift.{u} (Fin 2)) (g : k[X]) (c : k) :
    polyToChartBasicOpen k i g (C c) =
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).specStructureMap _ c :=
  sorry

/-- **The sections of `ℙ¹_k` over `Dᵢ(g)` are the localization `k[t]_g`.** -/
theorem isLocalization_chartBasicOpen (i : ULift.{u} (Fin 2)) (g : k[X]) :
    letI := (polyToChartBasicOpen k i g).toAlgebra
    IsLocalization.Away g Γ(ProjectiveLine (Spec (.of k)), chartBasicOpen k i g) :=
  sorry

/-- **The opens `Dᵢ(g)`, `g ≠ 0`, form a basis of the topology of `ℙ¹_k`.** -/
theorem isBasis_chartBasicOpen :
    Opens.IsBasis (Set.range fun a : (Σ _ : ULift.{u} (Fin 2), {g : k[X] // g ≠ 0}) ↦
      chartBasicOpen k a.1 a.2.1) :=
  sorry

/-- **`dt` is a free generator of `Ω¹_{ℙ¹/k}` over `Dᵢ(g)`.** -/
theorem isFreeGenerator_sectionsD_polyToChartBasicOpen_X (i : ULift.{u} (Fin 2)) (g : k[X]) :
    IsFreeGenerator ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).sectionsD _
      (polyToChartBasicOpen k i g X)) :=
  sorry

end AlgebraicGeometry.ProjectiveLine
