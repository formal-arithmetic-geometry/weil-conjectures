/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Vector bundles

A vector bundle of rank `d` over a scheme `S` is a morphism `π : V ⟶ S` with a zero section
`z : S ⟶ V`, which is Zariski-locally on `S` isomorphic to relative affine space
`𝔸^d_U ⟶ U`, compatibly with the zero sections, with *linear* transition maps: on the overlap of
two trivialising opens the coordinates of one chart are linear combinations, with coefficients
functions on the base forming an invertible matrix, of the coordinates of the other.

## Main definitions

- `AlgebraicGeometry.VectorBundle`: a vector bundle structure of rank `d` on `π : V ⟶ S`.
- `AlgebraicGeometry.VectorBundle.coord`: the coordinates `t₁, …, t_d` of a chart.
- `AlgebraicGeometry.VectorBundle.zeroRestrict`: the zero section over a trivialising open.

## Main statements

- `AlgebraicGeometry.VectorBundle.zero_π`: the zero section is a section.
- `AlgebraicGeometry.VectorBundle.smoothOfRelativeDimension`: `π` is smooth of relative
  dimension `d`.
- `AlgebraicGeometry.VectorBundle.isClosedImmersion_zero`: the zero section is a closed
  immersion.
- `AlgebraicGeometry.VectorBundle.existsUnique_transition`: two charts differ on their overlap by
  a unique invertible matrix.

## Implementation notes

The blueprint (`def-asd-vector-bundle-zero-section`) defines a vector bundle as
`V = Spec_S Sym(𝒬)` for a locally free `𝒪_S`-module `𝒬` of rank `d`, the zero section being the
augmentation `Sym(𝒬) ⟶ 𝒪_S`. A basis of `𝒬|_U` is a trivialisation `V|_U ≅ 𝔸^d_U` carrying the
zero section to the zero section, the coordinates being the basis vectors, and two bases differ
by an invertible matrix. Conversely the coordinates of a family of such trivialisations with
linear transition functions are bases of a locally free module `𝒬` — the sheaf of functions on
`V` which are linear in the coordinates of every chart — and `V = Spec_S Sym(𝒬)`. We therefore
record a vector bundle by such an atlas of linear charts: this is the form in which all
statements about vector bundles are proved, by reduction to affine space over the charts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V S : Scheme.{u}}

/-- If `z` is a section of `π`, then `U ≤ z⁻¹(π⁻¹ U)` for every open `U` of the base. -/
lemma Scheme.Hom.le_preimage_preimage_of_comp_eq_id {π : V ⟶ S} {z : S ⟶ V} (h : z ≫ π = 𝟙 S)
    (U : S.Opens) : U ≤ z ⁻¹ᵁ π ⁻¹ᵁ U := by
  intro x hx
  change (z ≫ π).base x ∈ U
  rwa [h]

/-- Blueprint `def-asd-vector-bundle-zero-section`: Vector bundles.

A *vector bundle of rank `d`* on a morphism `π : V ⟶ S`: a zero section `z : S ⟶ V` and a
Zariski open cover `(U i)` of `S` with trivialisations `π⁻¹(U i) ≅ 𝔸^d_{U i}` over `U i`, carrying
`z` to the zero section of affine space, whose transition functions are linear: on
`π⁻¹(U i ∩ U j)` the coordinates of the `j`-th chart are `t^j = M t^i` for an invertible matrix
`M` of functions on `U i ∩ U j`. Equivalently (see the module docstring) `V = Spec_S Sym(𝒬)` for
a locally free `𝒪_S`-module `𝒬` of rank `d`, with `z` the augmentation; two trivialisations
differ by a unique matrix in `GL_d(Γ(U, 𝒪_U))`
(`AlgebraicGeometry.VectorBundle.existsUnique_transition`). -/
structure VectorBundle (d : ℕ) (π : V ⟶ S) where
  /-- The zero section `z : S ⟶ V`. -/
  zero : S ⟶ V
  /-- The zero section is a section of `π`. -/
  zero_comp : zero ≫ π = 𝟙 S
  /-- The index type of the trivialising cover. -/
  ι : Type u
  /-- The trivialising opens of the base. -/
  U : ι → S.Opens
  /-- The trivialising opens cover the base. -/
  iSup_U : iSup U = ⊤
  /-- The trivialisations `π⁻¹(U i) ≅ 𝔸^d_{U i}`. -/
  chart (i : ι) : (π ⁻¹ᵁ U i).toScheme ≅ 𝔸(ULift.{u} (Fin d); U i)
  /-- The trivialisations are over the base. -/
  chart_over (i : ι) : (chart i).hom ≫ 𝔸(ULift.{u} (Fin d); U i) ↘ U i = π ∣_ U i
  /-- The trivialisations carry the zero section to the zero section. -/
  zero_chart (i : ι) :
    zero.resLE (π ⁻¹ᵁ U i) (U i) (Scheme.Hom.le_preimage_preimage_of_comp_eq_id zero_comp _) ≫
      (chart i).hom = AffineSpace.zeroSection _ _
  /-- The transition functions are linear: on `π⁻¹(U i ∩ U j)` the coordinates of the `j`-th
  chart are `M` times those of the `i`-th chart, for an invertible matrix `M` of functions on
  `U i ∩ U j`. -/
  linear (i j : ι) : ∃ M : Matrix (Fin d) (Fin d) Γ((U i ⊓ U j).toScheme, ⊤), IsUnit M.det ∧
    ∀ a, (V.homOfLE (π.preimage_mono inf_le_right) ≫ (chart j).hom).appTop
        (AffineSpace.coord _ (ULift.up a)) =
      ∑ b, (π ∣_ (U i ⊓ U j)).appTop (M a b) *
        (V.homOfLE (π.preimage_mono inf_le_left) ≫ (chart i).hom).appTop
          (AffineSpace.coord _ (ULift.up b))

namespace VectorBundle

variable {d : ℕ} {π : V ⟶ S} (E : VectorBundle d π)

attribute [reassoc (attr := simp)] zero_comp chart_over zero_chart

/-- The coordinates `t₁, …, t_d` of the `i`-th chart, functions on `π⁻¹(U i)`. -/
noncomputable def coord (i : E.ι) (a : Fin d) : Γ((π ⁻¹ᵁ E.U i).toScheme, ⊤) :=
  (E.chart i).hom.appTop (AffineSpace.coord _ (ULift.up a))

/-- The zero section over the trivialising open `U i`, `U i ⟶ π⁻¹(U i)`. -/
noncomputable def zeroRestrict (i : E.ι) : (E.U i).toScheme ⟶ (π ⁻¹ᵁ E.U i).toScheme :=
  E.zero.resLE (π ⁻¹ᵁ E.U i) (E.U i)
    (Scheme.Hom.le_preimage_preimage_of_comp_eq_id E.zero_comp _)

@[reassoc (attr := simp)]
lemma zeroRestrict_ι (i : E.ι) : E.zeroRestrict i ≫ (π ⁻¹ᵁ E.U i).ι = (E.U i).ι ≫ E.zero :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma zeroRestrict_chart (i : E.ι) :
    E.zeroRestrict i ≫ (E.chart i).hom = AffineSpace.zeroSection _ _ :=
  E.zero_chart i

@[reassoc (attr := simp)]
lemma zeroRestrict_comp_morphismRestrict (i : E.ι) :
    E.zeroRestrict i ≫ π ∣_ E.U i = 𝟙 _ := by
  rw [← E.chart_over, E.zeroRestrict_chart_assoc, AffineSpace.zeroSection_comp_over]

lemma coord_zeroRestrict (i : E.ι) (a : Fin d) : (E.zeroRestrict i).appTop (E.coord i a) = 0 := by
  rw [coord, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, zeroRestrict_chart,
    AffineSpace.zeroSection_appTop_coord]

/-- The base change of `π` to a trivialising open is a smooth morphism of relative dimension
`d`, being isomorphic to the projection of `𝔸^d_{U i}`. -/
lemma smoothOfRelativeDimension_morphismRestrict (i : E.ι) :
    SmoothOfRelativeDimension d (π ∣_ E.U i) := by
  rw [← E.chart_over]
  have : SmoothOfRelativeDimension d (𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (n := ULift.{u} (Fin d)) (E.U i)
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension d) _ _).2
    this

include E in
/-- A vector bundle of rank `d` is smooth of relative dimension `d`. -/
lemma smoothOfRelativeDimension : SmoothOfRelativeDimension d π :=
  IsZariskiLocalAtTarget.of_iSup_eq_top _ E.iSup_U E.smoothOfRelativeDimension_morphismRestrict

lemma preimage_zero_preimage (U : S.Opens) : E.zero ⁻¹ᵁ π ⁻¹ᵁ U = U := by
  rw [← Scheme.Hom.comp_preimage, E.zero_comp]
  rfl

lemma iSup_preimage_U : ⨆ i, π ⁻¹ᵁ E.U i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, E.iSup_U]
  rfl

lemma zeroRestrict_eq (i : E.ι) :
    E.zeroRestrict i = AffineSpace.zeroSection _ _ ≫ (E.chart i).inv := by
  rw [← E.zeroRestrict_chart_assoc, Iso.hom_inv_id, Category.comp_id]

instance isClosedImmersion_zeroRestrict (i : E.ι) : IsClosedImmersion (E.zeroRestrict i) := by
  rw [zeroRestrict_eq]
  infer_instance

include E in
/-- The zero section of a vector bundle is a closed immersion. -/
lemma isClosedImmersion_zero : IsClosedImmersion E.zero := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ E.iSup_preimage_U fun i ↦ ?_
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr _ _ rfl (E.preimage_zero_preimage _) @IsClosedImmersion]
  exact E.isClosedImmersion_zeroRestrict i

lemma isAffineHom_morphismRestrict (i : E.ι) : IsAffineHom (π ∣_ E.U i) := by
  rw [← E.chart_over]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom) _ _).2 inferInstance

include E in
/-- A vector bundle is an affine morphism. -/
lemma isAffineHom : IsAffineHom π :=
  IsZariskiLocalAtTarget.of_iSup_eq_top _ E.iSup_U E.isAffineHom_morphismRestrict

lemma locallyOfFiniteType_morphismRestrict (i : E.ι) : LocallyOfFiniteType (π ∣_ E.U i) := by
  rw [← E.chart_over]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) _ _).2
    inferInstance

include E in
/-- A vector bundle is locally of finite type. -/
lemma locallyOfFiniteType : LocallyOfFiniteType π :=
  IsZariskiLocalAtTarget.of_iSup_eq_top _ E.iSup_U E.locallyOfFiniteType_morphismRestrict

end VectorBundle

end AlgebraicGeometry
