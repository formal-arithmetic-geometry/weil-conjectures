/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationPointEvaluation

/-! # Changing the chosen geometric point of a strict localization

Source: ILO, Travaux de Gabber, Expose XVII, proof of Lemma 3.5.8, p. 277;
Stacks Project, Tag 04HX, the pointed-neighbourhood construction
(blueprint: def-per-strict-localization-point-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A geometric-point isomorphism induces the unique pointed map of strict localizations.
Source: ILO XVII 3.5.8, p. 277; Stacks 04HX
(blueprint: def-per-strict-localization-point-change).

Proof: precompose the lift in each affine pointed etale neighbourhood of `y` by
`e.hom`. The equation `he` makes it a pointed neighbourhood of `x`. The limit
projections for `x` now form a compatible cone over the neighbourhoods of `y`.
The inverse-limit property of strict localization gives `h`, over `S`, and the
compatible geometric-point cocones give the displayed pointed equation.
Conversely, this equation makes `h` carry the closed point to the closed point.
For any pointed etale neighbourhood, its projection composed with `h` is the unique
lift with that closed geometric point: henselian etale lifting, or equivalently
Stacks 08HR applied to its etale coordinate ring, gives uniqueness. Thus every
projection of `h` is prescribed, and limit uniqueness gives uniqueness of `h`.
The same construction for `e.symm` gives the inverse, so this is the canonical
change-of-point isomorphism on strict localizations. -/
theorem strictLocalizationPointChange_existsUnique
    {S : Scheme.{u}} {Ω₁ Ω₂ : Type u}
    [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ S) (y : Spec (.of Ω₂) ⟶ S)
    (e : Spec (.of Ω₁) ≅ Spec (.of Ω₂)) (he : e.hom ≫ y = x) :
    ∃! h : strictHenselizationScheme x ⟶ strictHenselizationScheme y,
      h ≫ strictHenselizationStructuralMap y = strictHenselizationStructuralMap x ∧
      Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation x)) ≫ h =
        e.hom ≫ Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation y)) := by
  sorry

/-- The canonical map induced by a geometric-point isomorphism, chosen from its unique
pointed universal property, rather than from mere existence.
Source: ILO XVII 3.5.8, p. 277; Stacks 04HX
(blueprint: def-per-strict-localization-point-change). -/
noncomputable def strictLocalizationPointChange
    {S : Scheme.{u}} {Ω₁ Ω₂ : Type u}
    [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ S) (y : Spec (.of Ω₂) ⟶ S)
    (e : Spec (.of Ω₁) ≅ Spec (.of Ω₂)) (he : e.hom ≫ y = x) :
    strictHenselizationScheme x ⟶ strictHenselizationScheme y :=
  Classical.choose (strictLocalizationPointChange_existsUnique x y e he)

end AlgebraicGeometry.Scheme
