/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Mathlib.RingTheory.LaurentSeries
public import WeilConjectures.WeilSheaf.Fourier

/-!
# The punctured formal disc at infinity

Let `k̄` be an algebraic closure of the finite field `k₀`, `R = k̄⟦t⟧`, `K = k̄((t))` and `L` an
algebraic closure of `K`. The coordinate `t = 1 / x` at `∞ ∈ ℙ¹` gives

- the point `Spec R ⟶ ℙ¹_{k̄}`, `z = t` in the chart at infinity
  (`AlgebraicGeometry.powerSeriesInfinityPoint`), whose closed point maps to `∞`;
- the points `Spec K ⟶ 𝔸¹_{k̄}`, `x = b / t` (`AlgebraicGeometry.laurentPoint`), which are
  generic, so they factor through every nonempty open `Ū`;

and over `x = b / t`, `b ≠ 0`, a root `u ∈ L` of the Artin–Schreier equation `u^q - u = b / t`
gives a point `Spec L ⟶ 𝔸¹_{k̄}` over `Spec K` lifting `x = b / t` along `ĀS`, which every
translation `σ̄_c`, `c ∈ k₀`, carries to its image under some `K`-automorphism of `L`
(`LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single`).

This is the formal local geometry at `∞` behind the ramification of the linear Artin–Schreier
sheaves at infinity (blueprint `lem-a1-artin-schreier-ramified-infinity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀]

local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

/-- The point `x = b / t` of the geometric affine line `𝔸¹_{k̄}` with values in the Laurent series
field `k̄((t))`. -/
noncomputable def laurentPoint (b : AlgebraicClosure k₀) :
    Spec (.of (LaurentSeries (AlgebraicClosure k₀))) ⟶ Ā :=
  pullback.lift
    (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (LaurentSeries (AlgebraicClosure k₀)))))
      fun _ ↦ (Scheme.ΓSpecIso (.of (LaurentSeries (AlgebraicClosure k₀)))).inv.hom
        (HahnSeries.single (-1) b))
    (Spec.map (CommRingCat.ofHom
      (algebraMap (AlgebraicClosure k₀) (LaurentSeries (AlgebraicClosure k₀)))))
    (by sorry)

/-- The point `z = t` of the chart at infinity of the geometric projective line `ℙ¹_{k̄}` with
values in the power series ring `k̄⟦t⟧`; its closed point maps to `∞`. -/
noncomputable def powerSeriesInfinityPoint :
    Spec (.of (PowerSeries (AlgebraicClosure k₀))) ⟶
      (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)).geometricFiber :=
  pullback.lift
    (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (PowerSeries (AlgebraicClosure k₀)))))
      (fun _ ↦ (Scheme.ΓSpecIso (.of (PowerSeries (AlgebraicClosure k₀)))).inv.hom
        PowerSeries.X) ≫ ProjectiveLine.infinityChart _)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (AlgebraicClosure k₀) (PowerSeries (AlgebraicClosure k₀)))))
    (by sorry)

/-- On the punctured disc, the point `z = t` of the chart at infinity is the point `x = 1 / t` of
the affine chart. -/
theorem laurentPoint_one_comp_geometricFiberMap_affineChart :
    laurentPoint k₀ 1 ≫ Scheme.Hom.geometricFiberMap
        (ProjectiveLine.affineChart (Spec (.of k₀))) (comp_over _ _) =
      Spec.map (CommRingCat.ofHom
          (algebraMap (PowerSeries (AlgebraicClosure k₀)) (LaurentSeries (AlgebraicClosure k₀)))) ≫
        powerSeriesInfinityPoint k₀ := by
  sorry

/-- The point `z = t` of `ℙ¹_{k̄}` factors through the geometric fiber of every open `W ⊆ ℙ¹`
containing `∞`, that is, with `𝔸¹ ∪ W = ℙ¹`: its closed point maps to `∞`, and every open of
the local scheme `Spec k̄⟦t⟧` containing the closed point is everything. -/
theorem exists_comp_geometricFiberMap_eq_powerSeriesInfinityPoint
    (W : (ProjectiveLine (Spec (.of k₀))).Opens)
    (hW : (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange ⊔ W = ⊤) :
    ∃ z : Spec (.of (PowerSeries (AlgebraicClosure k₀))) ⟶
        (W.toScheme ↘ Spec (.of k₀)).geometricFiber,
      z ≫ Scheme.Hom.geometricFiberMap W.ι (comp_over _ _) = powerSeriesInfinityPoint k₀ := by
  sorry

/-- The point `x = 1 / t` is generic: it factors through the geometric fiber of every nonempty
open `j : U ↪ 𝔸¹`. -/
theorem exists_comp_geometricFiberMap_eq_laurentPoint {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [Nonempty U] (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    ∃ z : Spec (.of (LaurentSeries (AlgebraicClosure k₀))) ⟶
        (U ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      z ≫ Scheme.Hom.geometricFiberMap j (comp_over j _) = laurentPoint k₀ 1 := by
  sorry

/-- The geometric multiplication by `a` maps `x = b / t` to `x = a b / t`. -/
theorem laurentPoint_comp_geometricSMul (a b : AlgebraicClosure k₀) :
    laurentPoint k₀ b ≫ affineLine.geometricSMul k₀ a = laurentPoint k₀ (a * b) := by
  sorry

/-- The base change of the multiplication by `a ∈ k₀` maps `x = b / t` to `x = a b / t`. -/
theorem laurentPoint_comp_geometricFiberMap_smul (a : k₀) (b : AlgebraicClosure k₀) :
    laurentPoint k₀ b ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ a) (comp_over _ _) =
      laurentPoint k₀ (algebraMap k₀ (AlgebraicClosure k₀) a * b) := by
  sorry

variable [Finite k₀]

/-- **The Artin–Schreier cover over the punctured disc at infinity.** For `b ≠ 0`, a root `u` of
`u^q - u = b / t` in an algebraic closure `L` of `K = k̄((t))` gives a point `x = u` of `𝔸¹_{k̄}`
over `Spec L ⟶ Spec K` lifting `x = b / t` along `ĀS`, and for every `c ∈ k₀` some
`K`-automorphism of `L`, acting on `Spec L` over `Spec K`, moves it by the translation `σ̄_c`. -/
theorem exists_comp_geometricArtinSchreierMap_eq_laurentPoint {b : AlgebraicClosure k₀}
    (hb : b ≠ 0) :
    ∃ z' : Spec (.of (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀)))) ⟶ Ā,
      z' ≫ affineLine.geometricArtinSchreierMap k₀ =
          Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries (AlgebraicClosure k₀))
            (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))))) ≫ laurentPoint k₀ b ∧
        ∀ c : k₀, ∃ σ : Spec (.of (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀)))) ⟶
            Spec (.of (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀)))),
          σ ≫ Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries (AlgebraicClosure k₀))
              (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))))) =
            Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries (AlgebraicClosure k₀))
              (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))))) ∧
          σ ≫ z' = z' ≫ (affineLine.geometricTranslationIso k₀ c).hom := by
  sorry

end AlgebraicGeometry
