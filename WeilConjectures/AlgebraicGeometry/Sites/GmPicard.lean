/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.UnitsTorsor

/-!
# The Picard group as first étale cohomology of `𝔾ₘ`

For a scheme `X` the isomorphism classes of invertible `𝒪_X`-modules, the Zariski cohomology
`H¹(X_Zar, 𝒪_Xˣ)` and the étale cohomology `H¹(X_ét, 𝔾ₘ)` are in bijection (Hilbert 90).
All three classify torsors: an invertible module `L` gives the `𝔾ₘ`-torsor `Isom(𝒪, L)`, and
`H¹` of an abelian sheaf classifies its torsors.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_equiv_quotient_torsor`: invertible modules up to
  isomorphism are in bijection with `𝔾ₘ`-torsors on `X_ét` and with `𝒪_Xˣ`-torsors on `X_Zar`.
  The Zariski part is `AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_unitsSheaf`;
  the proof of the étale part,
  `AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_gmSheaf`, is `sorry`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_H_one_unitsSheaf`: Hilbert 90,
  `Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`: there is a bijection
  `Pic(X) ≃ H¹(X_ét, 𝔾ₘ)`.

## TODO

`AlgebraicGeometry.Scheme.Pic` carries no group structure yet, and the torsor classification is
recorded as the existence of bijections, so the comparisons are bijections of sets. Replace
them by the canonical additive equivalences `L ↦ [Isom(𝒪, L)]`, of type `≃+`, once both are
available.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **Line bundles and `𝔾ₘ`-torsors, étale version.** For a scheme `X`, the isomorphism classes
of invertible `𝒪_X`-modules are in bijection with the isomorphism classes of `𝔾ₘ`-torsors on
the small étale site of `X`. The canonical bijection sends `L` to the torsor
`Isom(𝒪_{X_ét}, L_ét)`; that it is surjective is fpqc descent for invertible modules.

Only the existence of the bijection is recorded. The proof is `sorry`. For `X = Spec K` with
`K` a field, the descent step is proved in
`AlgebraicGeometry.Scheme.exists_app_eq_of_app_etaleSpec_eq`.
(blueprint: `lem-sc-line-bundle-torsor`, étale part) -/
theorem nonempty_pic_equiv_quotient_torsor_gmSheaf :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf))) :=
  sorry

/-- **Line bundles and `𝔾ₘ`-torsors.** For a scheme `X`, the isomorphism classes of invertible
`𝒪_X`-modules are in bijection with the isomorphism classes of `𝔾ₘ`-torsors on the small étale
site of `X`, and with the isomorphism classes of `𝒪_Xˣ`-torsors on the Zariski site. The
canonical bijections send `L` to the torsor `Isom(𝒪, L)`.

Only the existence of the bijections is recorded. The Zariski part is
`AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_unitsSheaf`, the étale part
`AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_gmSheaf`.
(blueprint: `lem-sc-line-bundle-torsor`) -/
theorem nonempty_equiv_quotient_torsor :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf))) ∧
      Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf))) :=
  ⟨X.nonempty_pic_equiv_quotient_torsor_gmSheaf, X.nonempty_pic_equiv_quotient_torsor_unitsSheaf⟩

/-- **Hilbert 90 for a scheme.** For a scheme `X` there are bijections

`{invertible 𝒪_X-modules}/≅ ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`.

Both cohomology groups classify torsors (`CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor`)
and both kinds of torsors are classified by invertible modules
(`AlgebraicGeometry.Scheme.nonempty_equiv_quotient_torsor`).

Only the existence of the bijections is recorded, not that they are the natural maps.
(blueprint: `thm-sc-hilbert-90`) -/
theorem nonempty_equiv_H_one_unitsSheaf :
    Nonempty (X.Pic ≃ Sheaf.H X.unitsSheaf 1) ∧
      Nonempty (Sheaf.H X.unitsSheaf 1 ≃ X.CohomologicalPicardGroup) := by
  obtain ⟨⟨eEt⟩, ⟨eZar⟩⟩ := X.nonempty_equiv_quotient_torsor
  obtain ⟨fEt⟩ := Sheaf.nonempty_equiv_H_one_torsor
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X) X.gmSheaf
  obtain ⟨fZar⟩ := Sheaf.nonempty_equiv_H_one_torsor (Limits.isTerminalTop (α := X.Opens))
    X.unitsSheaf
  exact ⟨⟨eZar.trans fZar.symm⟩, ⟨fZar.trans (eZar.symm.trans (eEt.trans fEt.symm))⟩⟩

/-- **The Picard group is `H¹(X, 𝔾ₘ)`.** For a scheme `X` the isomorphism classes of invertible
`𝒪_X`-modules are in bijection with the cohomological Picard group `H¹(X_ét, 𝔾ₘ)`: this is the
composite of the two bijections of `AlgebraicGeometry.Scheme.nonempty_equiv_H_one_unitsSheaf`.

This only asserts that some bijection exists; it does not specify the canonical map
`L ↦ [Isom(𝒪, L)]` of the blueprint statement.
(blueprint: `lem-sc-h1-gm-pic`) -/
theorem nonempty_equiv_cohomologicalPicardGroup :
    Nonempty (X.Pic ≃ X.CohomologicalPicardGroup) :=
  let h := X.nonempty_equiv_H_one_unitsSheaf
  ⟨h.1.some.trans h.2.some⟩

end AlgebraicGeometry.Scheme
