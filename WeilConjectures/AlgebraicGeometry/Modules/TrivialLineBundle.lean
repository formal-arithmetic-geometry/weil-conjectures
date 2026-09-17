/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Over

/-!
# Global sections of a trivial line bundle, read on the fibres

Let `X` be a scheme and `L` a sheaf of `𝒪ₓ`-modules isomorphic to the structure sheaf. This file
proves the two statements about such a *trivial* line bundle that the seesaw theorem consumes:
over a base ring `R` which the structure morphism identifies with `Γ(X, 𝒪ₓ)` — for instance a
field over which `X` is proper and geometrically integral — the space of global sections of `L`
is one-dimensional, and, as soon as `Γ(X, 𝒪ₓ)` is a field, a non-zero global section of `L` has
non-zero image in every fibre.

The image of a global section in a fibre is `AlgebraicGeometry.Scheme.Modules.fiberMk`, and the
computation behind the second statement is the identification of the fibre of the structure sheaf
with the residue field, `AlgebraicGeometry.Scheme.Modules.fiberMk_unit_eq_zero_iff`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.sectionsEquivOfIsoUnit`: an isomorphism `L ≅ 𝒪ₓ` identifies
  `Γ(X, L)` with `Γ(X, 𝒪ₓ)`, so the global sections of a trivial line bundle are a free
  `Γ(X, 𝒪ₓ)`-module of rank one.

## Main results

- `AlgebraicGeometry.Scheme.Modules.finrank_sections_unit_eq_one`: `h⁰(X, 𝒪ₓ) = 1` for a scheme
  whose structure morphism identifies the base ring `R` with `Γ(X, 𝒪ₓ)`.
- `AlgebraicGeometry.Scheme.Modules.finrank_sections_eq_one_of_iso_unit`: for such an `X` and
  `L ≅ 𝒪ₓ`, the `R`-module `Γ(X, L)` is free of rank one.
- `AlgebraicGeometry.Scheme.Modules.nontrivial_sections_of_iso_unit`: a trivial line bundle on a
  scheme with a non-trivial ring of global functions has a non-zero global section.
- `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_isUnit` and
  `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_isField`: a global section of a trivial
  line bundle whose image in `Γ(X, 𝒪ₓ)` is a unit — for instance any non-zero section, when
  `Γ(X, 𝒪ₓ)` is a field — has non-zero image in the fibre at every point.

A line bundle is usually trivialised by an isomorphism `L ≅ 𝟙_ X.Modules` with the tensor unit;
`AlgebraicGeometry.Scheme.Modules.tensorUnitIsoUnit` turns that into the isomorphism `L ≅ 𝒪ₓ`
these statements take.

## Blueprint

The main results together are `lem:cube-nowhere-vanishing` of the theorem-of-the-cube chapter,
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`. The other three
statements of that group — `lem:cube-degeneracy-closed`, `lem:cube-invertible-fibrewise` and
`lem:cube-triviality-criterion` — need a local trivialisation of an invertible sheaf and are left
to later work.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L : X.Modules}

section Trivial

/-- **The global sections of a trivial line bundle.** If `L ≅ 𝒪ₓ`, then `Γ(X, L)` is a free
`Γ(X, 𝒪ₓ)`-module of rank one: an isomorphism `L ≅ 𝒪ₓ` identifies `Γ(X, L)` with `Γ(X, 𝒪ₓ)`. -/
noncomputable def sectionsEquivOfIsoUnit (e : L ≅ unit X.ringCatSheaf) :
    Γ(L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  sectionsEquivOfIso e ⊤

@[simp]
lemma sectionsEquivOfIsoUnit_apply (e : L ≅ unit X.ringCatSheaf) (s : Γ(L, ⊤)) :
    sectionsEquivOfIsoUnit e s = Hom.app e.hom ⊤ s := rfl

/-- **A trivial line bundle has a non-zero global section**, as soon as the ring of global
functions of `X` is non-trivial. -/
theorem nontrivial_sections_of_iso_unit [Nontrivial Γ(X, ⊤)] (e : L ≅ unit X.ringCatSheaf) :
    Nontrivial Γ(L, ⊤) :=
  (sectionsEquivOfIsoUnit e).toEquiv.nontrivial

/-- **A global section of a trivial line bundle which is a unit vanishes nowhere.** If `L ≅ 𝒪ₓ`
and the corresponding global function is a unit of `Γ(X, 𝒪ₓ)`, then the section has non-zero
image in the fibre `L(x)` at every point `x`. -/
theorem fiberMk_ne_zero_of_isUnit (e : L ≅ unit X.ringCatSheaf) {s : Γ(L, ⊤)}
    (hs : IsUnit (sectionsEquivOfIsoUnit e s)) (x : X) : fiberMk L x s ≠ 0 := by
  intro h
  refine fiberMk_unit_ne_zero_of_isUnit hs x ((fiberMap_fiberMk e.hom x s).symm.trans ?_)
  rw [h]
  exact map_zero _

/-- **A non-zero global section of a trivial line bundle vanishes nowhere.** If the ring of
global functions of `X` is a field — for instance if `X` is an integral scheme, proper over a
field — and `L ≅ 𝒪ₓ`, then a non-zero global section of `L` has non-zero image in the fibre
`L(x)` at every point `x`.

This is the second half of `lem:cube-nowhere-vanishing` of the blueprint. -/
theorem fiberMk_ne_zero_of_isField (hX : IsField Γ(X, ⊤)) (e : L ≅ unit X.ringCatSheaf)
    {s : Γ(L, ⊤)} (hs : s ≠ 0) (x : X) : fiberMk L x s ≠ 0 :=
  fiberMk_ne_zero_of_isUnit e (isUnit_iff_exists_inv.mpr (hX.mul_inv_cancel
    fun hz ↦ hs ((sectionsEquivOfIsoUnit e).map_eq_zero_iff.mp hz))) x

/-- **A non-zero global section of a trivial line bundle on a proper integral scheme vanishes
nowhere.** This is `lem:cube-nowhere-vanishing` of the blueprint under its own hypotheses; the
field `K` need not be algebraically closed, and universal closedness suffices for properness. -/
theorem fiberMk_ne_zero_of_universallyClosed {K : Type u} [Field K] (π : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed π] (e : L ≅ unit X.ringCatSheaf) {s : Γ(L, ⊤)} (hs : s ≠ 0)
    (x : X) : fiberMk L x s ≠ 0 :=
  fiberMk_ne_zero_of_isField (isField_of_universallyClosed K π) e hs x

end Trivial

section OverBase

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- An isomorphism of sheaves of modules on a scheme over `Spec R` identifies their global
sections as `R`-modules. -/
noncomputable def sectionsBaseEquivOfIso {F G : X.Modules} (e : F ≅ G) : Γ(F, ⊤) ≃ₗ[R] Γ(G, ⊤) :=
  { (sectionsEquivOfIso e ⊤).toAddEquiv with
    map_smul' := fun r s ↦ (sectionsEquivOfIso e ⊤).map_smul (Scheme.overRingHom R X r) s }

variable {R}

/-- **The global functions of `X` are free of rank one over the base ring.** If the structure
morphism of `X` over `Spec R` identifies `R` with `Γ(X, 𝒪ₓ)`, then `Γ(X, 𝒪ₓ)` is a free
`R`-module of rank one, a generator being the unit. -/
noncomputable def sectionsUnitEquiv
    (hπ : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop)) :
    R ≃ₗ[R] Γ(unit X.ringCatSheaf, ⊤) :=
  letI := hπ
  letI φ := (asIso ((Scheme.ΓSpecIso (.of R)).inv ≫
    (X ↘ Spec (.of R)).appTop)).commRingCatIsoToRingEquiv
  { φ.toAddEquiv with map_smul' := fun c d ↦ map_mul φ c d }

/-- **`h⁰(X, 𝒪ₓ) = 1`.** If the structure morphism of `X` over `Spec R` identifies `R` with
`Γ(X, 𝒪ₓ)`, the global functions of `X` are a one-dimensional `R`-module. -/
theorem finrank_sections_unit_eq_one [Nontrivial R]
    (hπ : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop)) :
    Module.finrank R Γ(unit X.ringCatSheaf, ⊤) = 1 := by
  rw [← (sectionsUnitEquiv hπ).finrank_eq, Module.finrank_self]

/-- **The space of global sections of a trivial line bundle is one-dimensional.** If the
structure morphism of `X` over `Spec R` identifies `R` with `Γ(X, 𝒪ₓ)` and `L ≅ 𝒪ₓ`, the
`R`-module `Γ(X, L)` is free of rank one. This is the first half of
`lem:cube-nowhere-vanishing`. -/
theorem finrank_sections_eq_one_of_iso_unit [Nontrivial R]
    (hπ : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop))
    (e : L ≅ unit X.ringCatSheaf) : Module.finrank R Γ(L, ⊤) = 1 := by
  rw [(sectionsBaseEquivOfIso R e).finrank_eq, finrank_sections_unit_eq_one hπ]

/-- **The space of global sections of a trivial line bundle on a proper variety is
one-dimensional.** For `X` proper and integral over an algebraically closed field `K` and
`L ≅ 𝒪ₓ`, the `K`-vector space `Γ(X, L)` has dimension one. -/
theorem finrank_sections_eq_one_of_iso_unit_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    [X.Over (Spec (.of K))] [IsIntegral X] [IsProper (X ↘ Spec (.of K))]
    (e : L ≅ unit X.ringCatSheaf) : Module.finrank K Γ(L, ⊤) = 1 :=
  finrank_sections_eq_one_of_iso_unit (isIso_ΓSpecIso_inv_comp_appTop _) e

/-- **The space of global sections of a trivial line bundle on a proper geometrically integral
scheme is one-dimensional.** For `X` proper and geometrically integral over a field `K` — which
need not be algebraically closed — and `L ≅ 𝒪ₓ`, the `K`-vector space `Γ(X, L)` has dimension
one. -/
theorem finrank_sections_eq_one_of_iso_unit_of_geometricallyIntegral {K : Type u} [Field K]
    [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    [GeometricallyIntegral (X ↘ Spec (.of K))] (e : L ≅ unit X.ringCatSheaf) :
    Module.finrank K Γ(L, ⊤) = 1 :=
  finrank_sections_eq_one_of_iso_unit (isIso_ΓSpecIso_inv_comp_appTop_of_geometricallyIntegral _) e

end OverBase

end AlgebraicGeometry.Scheme.Modules
