/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Morphisms into the integral model of affine space

`AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv` identifies morphisms `Y ⟶ Spec ℤ[m]`
with families of global sections of `Y`. We record how it evaluates on a morphism that
factors through the spectrum of a ring:

- `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp_SpecMap`.

We record that the affine coordinates are the sections classifying the morphism to the integral
model, in `AlgebraicGeometry.AffineSpace.coord_eq_toSpecMvPolyIntEquiv`.

We also record how `AlgebraicGeometry.AffineSpace.homOfVector` interacts with the functoriality
of affine space in the base, in `AlgebraicGeometry.AffineSpace.homOfVector_comp_map`, and that
`AlgebraicGeometry.AffineSpace.map` is an open immersion whenever the map of bases is.

`AlgebraicGeometry.AffineSpace.isClosedImmersion_homOfVector` is the criterion for a morphism
into an affine space over an affine base to be a closed immersion, and
`AlgebraicGeometry.AffineSpace.isImmersion_homOfVector_divBasicOpen` its consequence for the
morphism classified by a family of quotients `s j / s i` on a basic open.
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.AffineSpace

/-- The family of sections classifying a morphism `Y ⟶ Spec R ⟶ Spec ℤ[m]` is obtained by
evaluating the ring map `ℤ[m] ⟶ R` at the variables. -/
lemma toSpecMvPolyIntEquiv_comp_SpecMap {m : Type u} {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (h : Y ⟶ Spec R) (ψ : CommRingCat.of (MvPolynomial m (ULift.{u} ℤ)) ⟶ R) (j : m) :
    toSpecMvPolyIntEquiv m (h ≫ Spec.map ψ) j =
      h.appTop ((Scheme.ΓSpecIso R).inv (ψ (MvPolynomial.X j))) := by
  rw [toSpecMvPolyIntEquiv_comp]
  congr 1
  rw [toSpecMvPolyIntEquiv_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]

/-- The `j`-th affine coordinate of `𝔸(m; S)` is the `j`-th component of the family of global
sections classifying the morphism `AffineSpace.toSpecMvPoly m S` to the integral model. -/
lemma coord_eq_toSpecMvPolyIntEquiv {m : Type u} (S : Scheme.{u}) (j : m) :
    coord S j = toSpecMvPolyIntEquiv m (toSpecMvPoly m S) j :=
  rfl

section Map

variable {m : Type u} {S T : Scheme.{u}}

/-- Changing the base of `AlgebraicGeometry.AffineSpace.homOfVector` along `f : S ⟶ T` amounts
to composing the structure morphism with `f`. -/
@[reassoc]
lemma homOfVector_comp_map {X : Scheme.{u}} (h : X ⟶ S) (f : S ⟶ T) (v : m → Γ(X, ⊤)) :
    homOfVector h v ≫ map m f = homOfVector (h ≫ f) v := by
  refine hom_ext ?_ fun j ↦ ?_
  · rw [Category.assoc, map_over, homOfVector_over_assoc, homOfVector_over]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_appTop_coord,
      homOfVector_appTop_coord, homOfVector_appTop_coord]

instance isOpenImmersion_map (f : S ⟶ T) [IsOpenImmersion f] : IsOpenImmersion (map m f) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_map (n := m) f).flip ‹_›

end Map

/-- If the global sections of an affine scheme `X` are generated as a ring by the image of
`Γ(T, ⊤)` together with a family `v`, the morphism `X ⟶ 𝔸(m; T)` classifying `v` over
`h : X ⟶ T` is a closed immersion. -/
lemma isClosedImmersion_homOfVector {m : Type u} {X T : Scheme.{u}} [IsAffine X]
    [IsAffine T] (h : X ⟶ T) (v : m → Γ(X, ⊤))
    (hgen : Subring.closure (Set.range h.appTop ∪ Set.range v) = ⊤) :
    IsClosedImmersion (homOfVector h v) := by
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  have hle : Subring.closure (Set.range ⇑h.appTop ∪ Set.range v) ≤
      RingHom.range (homOfVector h v).appTop.hom := by
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨(𝔸(m; T) ↘ T).appTop a, ?_⟩
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over]
    · exact ⟨coord T i, homOfVector_appTop_coord _ _ _⟩
  exact fun x ↦ hle ((Subring.eq_top_iff' _).mp hgen x)

/-- The morphism into affine space over `S` classified by the quotients `s j / s i` on the basic
open `V_{s i}` is an immersion, provided the sections over `V_{s i}` are generated as a ring by
the image of the sections of an affine open `W` of `S` receiving `V_{s i}` together with those
quotients. -/
lemma isImmersion_homOfVector_divBasicOpen {V S : Scheme.{u}} (g : V ⟶ S) [IsAffine V]
    {n : Type u} (s : n → Γ(V, ⊤)) (i : n) (W : S.Opens) (hW : IsAffineOpen W)
    (hle : V.basicOpen (s i) ≤ g ⁻¹ᵁ W)
    (hgen : Subring.closure (Set.range (g.resLE W (V.basicOpen (s i)) hle).appTop ∪
      Set.range fun j : {j : n // j ≠ i} ↦ V.divBasicOpen (s j.1) (s i)) = ⊤) :
    IsImmersion (homOfVector ((V.basicOpen (s i)).ι ≫ g)
      fun j : {j : n // j ≠ i} ↦ V.divBasicOpen (s j.1) (s i)) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (V.basicOpen (s i) : Scheme.{u}) := (isAffineOpen_top V).basicOpen (s i)
  have := isClosedImmersion_homOfVector (m := {j : n // j ≠ i})
    (g.resLE W (V.basicOpen (s i)) hle) _ hgen
  have hcomp : (V.basicOpen (s i)).ι ≫ g = g.resLE W (V.basicOpen (s i)) hle ≫ W.ι :=
    (Scheme.Hom.resLE_comp_ι g hle).symm
  rw [hcomp, ← homOfVector_comp_map]
  infer_instance

end AlgebraicGeometry.AffineSpace
