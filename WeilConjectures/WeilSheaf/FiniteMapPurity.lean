/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage
/-! # Purity under finite étale pushforward

Source: the blueprint of the Weil conjectures, chapter `sec-deligne-laumon-a1`,
unit `sk-thm-dl-a1-upper`, node `lem-a1-finite-map-purity`
(blueprint: lem-a1-finite-map-purity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- If `π` is finite étale and `F` is punctually `ι`-pure of weight `w`, then
`π₀ * F` is punctually `ι`-pure of weight `w`.

Proof: this is the special case of the library theorem
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.lowerStar_of_isFinite`
(`WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage`), which needs only `π` finite,
not étale. That theorem also asks for the structure morphism of `Y` to be quasi-separated.
`Y` is locally of finite type over the Noetherian scheme `Spec k₀`, so it is locally
Noetherian and therefore quasi-separated, and `quasiSeparated_iff_quasiSeparatedSpace`
turns this into quasi-separatedness of `Y ↘ Spec k₀`. The library theorem carries out the
blueprint's argument: at a closed point `y`, each eigenvalue `λ` of Frobenius on the
direct-image stalk has a power `λ^e` that is a local Frobenius eigenvalue at a closed point
`x` above `y`, with `e = [κ(x) : κ(y)]` and `q_x = q_y^e`; hence `|ι λ| = q_y^(w/2)`.
(blueprint: lem-a1-finite-map-purity).
-/
theorem isPunctuallyPureOfWeight_lowerStar_of_isFiniteEtale
    (ι : PadicAlgCl l ≃+* ℂ) {w : ℝ} {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of k₀))]
    [IsFinite π] [Etale π]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X}
    (h : F.IsPunctuallyPureOfWeight ι.toRingHom w) :
    ((lowerStar π).obj F).IsPunctuallyPureOfWeight ι.toRingHom w := by
  let _ : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  let _ : QuasiSeparatedSpace Y := inferInstance
  let _ : QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀)) :=
    (quasiSeparated_iff_quasiSeparatedSpace _).2 inferInstance
  exact IsPunctuallyPureOfWeight.lowerStar_of_isFinite (π := π) h

end AlgebraicGeometry.WeilSheaf
