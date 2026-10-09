/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Group
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
- `AlgebraicGeometry.Scheme.Pic.toH1Units`: the canonical bijection
  `Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ)`, `L ↦ [Isom(𝒪_X, L)]`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_H_one_unitsSheaf`: Hilbert 90,
  `Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`: there is a bijection
  `Pic(X) ≃ H¹(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.nonempty_addEquiv_cohomologicalPicardGroup`: there is an isomorphism
  of groups `Pic(X) ≃+ H¹(X_ét, 𝔾ₘ)`; its proof is `sorry`.

## TODO

The Zariski comparison `Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ)` is the canonical map
`AlgebraicGeometry.Scheme.Pic.toH1Units`; it remains to show that it is additive, which needs
that the class map `CategoryTheory.Sheaf.Torsor.classH1` carries contracted products of torsors
to sums. The étale side is only recorded through the existence of bijections: the canonical map
`L ↦ [Isom(𝒪_{X_ét}, L_ét)]`, equivalently the comparison map along the morphism of sites
`X_ét → X_Zar`, needs either the étale sheaf `L_ét` of an `𝒪_X`-module or the exact pullback
functor from Zariski to étale sheaves, and neither is available yet.
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

Only the existence of the bijections is recorded here. The Zariski part is
`AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_unitsSheaf`, which comes from the
canonical bijection `AlgebraicGeometry.Scheme.picEquivQuotientTorsorUnitsSheaf`; the étale part
`AlgebraicGeometry.Scheme.nonempty_pic_equiv_quotient_torsor_gmSheaf`.
(blueprint: `lem-sc-line-bundle-torsor`) -/
theorem nonempty_equiv_quotient_torsor :
    Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.gmSheaf))) ∧
      Nonempty (X.Pic ≃ _root_.Quotient (Sheaf.Torsor.setoid (G := X.unitsSheaf))) :=
  ⟨X.nonempty_pic_equiv_quotient_torsor_gmSheaf, X.nonempty_pic_equiv_quotient_torsor_unitsSheaf⟩

/-- **The Picard group as Zariski cohomology of units.** The canonical bijection
`Pic(X) ≃ H¹(X_Zar, 𝒪_Xˣ)`, sending the class of an invertible module `L` to the class
(`CategoryTheory.Sheaf.Torsor.classH1`) of the `𝒪_Xˣ`-torsor `Isom(𝒪_X, L)` of local
generators of `L` (`AlgebraicGeometry.Scheme.Pic.toH1Units_mk`). It is the composite of the
bijection `AlgebraicGeometry.Scheme.picEquivQuotientTorsorUnitsSheaf` between invertible modules
and `𝒪_Xˣ`-torsors and the classification of torsors by `H¹`.
(blueprint: `thm-sc-hilbert-90`, the first map; `lem-sc-h1-gm-pic`) -/
noncomputable def Pic.toH1Units : X.Pic ≃ Sheaf.H X.unitsSheaf 1 :=
  X.picEquivQuotientTorsorUnitsSheaf.trans
    (Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens)))

variable {X} in
/-- The class of an invertible module `M` in `H¹(X_Zar, 𝒪_Xˣ)` is the class of the torsor
`Isom(𝒪_X, M)` of its local generators. -/
lemma Pic.toH1Units_mk (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    Pic.toH1Units X (Pic.mk M) =
      Sheaf.Torsor.classH1 X.unitsSheaf (Limits.isTerminalTop (α := X.Opens))
        ⟦M.generatorsTorsor⟧ := by
  rw [Pic.toH1Units, Equiv.trans_apply, picEquivQuotientTorsorUnitsSheaf_apply,
    Pic.torsorClass_mk]

/-- **Hilbert 90 for a scheme.** For a scheme `X` there are bijections

`{invertible 𝒪_X-modules}/≅ ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`.

The first one is the canonical bijection `AlgebraicGeometry.Scheme.Pic.toH1Units`,
`L ↦ [Isom(𝒪_X, L)]`. For the second, only the existence of a bijection is recorded: both
groups classify torsors (`CategoryTheory.Sheaf.Torsor.classH1`), and both kinds of torsors are
classified by invertible modules (`AlgebraicGeometry.Scheme.nonempty_equiv_quotient_torsor`,
whose étale part is `sorry`).
(blueprint: `thm-sc-hilbert-90`) -/
theorem nonempty_equiv_H_one_unitsSheaf :
    Nonempty (X.Pic ≃ Sheaf.H X.unitsSheaf 1) ∧
      Nonempty (Sheaf.H X.unitsSheaf 1 ≃ X.CohomologicalPicardGroup) := by
  obtain ⟨eEt⟩ := X.nonempty_pic_equiv_quotient_torsor_gmSheaf
  let fEt := Sheaf.Torsor.classH1 X.gmSheaf
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  exact ⟨⟨Pic.toH1Units X⟩, ⟨(Pic.toH1Units X).symm.trans (eEt.trans fEt)⟩⟩

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

/-- **The Picard group is `H¹(X, 𝔾ₘ)` as a group.** For a scheme `X` the group `Pic(X)` of
invertible `𝒪_X`-modules up to isomorphism, under tensor product, is isomorphic to the
cohomological Picard group `H¹(X_ét, 𝔾ₘ)`. The canonical isomorphism sends `ℒ` to the class of
the `𝔾ₘ`-torsor `Isom(𝒪_X, ℒ)`, and the tensor product of invertible modules corresponds to the
contracted product of torsors, i.e. to the sum in `H¹`; this upgrades the bijection
`AlgebraicGeometry.Scheme.nonempty_equiv_cohomologicalPicardGroup`.
(blueprint: `lem-sc-h1-gm-pic`) -/
theorem nonempty_addEquiv_cohomologicalPicardGroup :
    Nonempty (Additive X.Pic ≃+ X.CohomologicalPicardGroup) :=
  sorry

end AlgebraicGeometry.Scheme
