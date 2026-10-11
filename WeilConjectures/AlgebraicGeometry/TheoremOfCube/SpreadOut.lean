/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.CechGluing
public import WeilConjectures.AlgebraicGeometry.Cohomology.FibreVanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatOver
public import WeilConjectures.AlgebraicGeometry.Cohomology.Kunneth
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratesFibre
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Seesaw
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.Slices
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Triviality on a fibre spreads out (Stacks, Tag 0BF3)

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `L` be an invertible module on `X ×_K Y ×_K Z` which is trivial on the slices
`{x} × Y × Z` and `X × {y} × Z` and on the fibre over a point `t` of `Z`. Then `L` is trivial
over a neighbourhood of `t`.

Let `J` be the ideal sheaf of `{x} × Y ∪ X × {y}` in `X ×_K Y`; it is `I_x ⊠ I_y`, so
`H¹(X × Y, J) = 0` by the Künneth formula. The module `𝒢 = pr^* J ⊗ L` on `X × Y × Z` is flat
over `Z` with `H¹(𝒢_t) = H¹(X × Y, J) = 0`, so `H¹` of `𝒢` vanishes over affine opens near `t`.
Hence the trivialisations of `L` on the two slices, made compatible on `{x} × {y} × Z`, lift to a
section of `L` near the fibre over `t` which generates `L` at a point of that fibre, and so
generates `L` over a neighbourhood of `t`.

## Main statements

- `AlgebraicGeometry.TheoremOfCube.subsingleton_H_one_crossIdeal`: the Künneth input.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace TheoremOfCube

variable {K : Type u} [Field K]

/-- On a `K`-scheme with `Γ(X, 𝒪_X) = K`, a function vanishing at a `K`-point is zero. -/
lemma eq_zero_of_mem_idealOfOpens_ker {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [Scheme.GlobalSectionsBijective K X] (x : Spec (.of K) ⟶ X) (hx : x ≫ X ↘ Spec (.of K) = 𝟙 _)
    {s : Γ(X, ⊤)} (hs : s ∈ x.ker.idealOfOpens ⊤) : s = 0 := by
  rw [Scheme.IdealSheafData.mem_idealOfOpens_iff] at hs
  have h0 : x.appTop s = 0 := by
    rw [← x.toImage_imageι]
    change x.toImage.app _ (x.imageι.app ⊤ s) = 0
    rw [hs, map_zero]
  obtain ⟨c, rfl⟩ := (Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom
    (k := K) (X := X)).2 s
  have h1 : x.appTop (Scheme.globalSectionsRingHom K c) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c := by
    change ((X ↘ Spec (.of K)).appTop ≫ x.appTop) _ = _
    rw [← Scheme.Hom.comp_appTop, hx, Scheme.Hom.id_appTop]
    rfl
  rw [h1] at h0
  have hc : c = 0 := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
    (h0.trans (map_zero _).symm)
  rw [hc, map_zero]


variable (X Y : Over (Spec (.of K)))

/-- The ideal sheaf `pr_X⁻¹ I_x ⊓ pr_Y⁻¹ I_y` of `{x} × Y ∪ X × {y}` in `X ×_K Y`. -/
noncomputable def crossIdeal (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) : (X ⊗ Y).left.IdealSheafData :=
  letI : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of K)) := ⟨Y.hom⟩
  Scheme.IdealSheafData.Kunneth.prodIdeal (K := K) x.left.ker y.left.ker

/-- **The Künneth input** (Stacks, Tag 0BF2). For `X`, `Y` proper and geometrically integral
over `K` with `K`-points `x`, `y`, the first cohomology of the ideal sheaf of
`{x} × Y ∪ X × {y}` in `X ×_K Y` vanishes. -/
lemma subsingleton_H_one_crossIdeal [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y) :
    Subsingleton ((crossIdeal X Y x y).toModules.H 1) := by
  letI : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of K)) := ⟨Y.hom⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsSeparated (X.left ↘ Spec (.of K)) := inferInstanceAs (IsSeparated X.hom)
  have : IsSeparated (Y.left ↘ Spec (.of K)) := inferInstanceAs (IsSeparated Y.hom)
  have : Scheme.GlobalSectionsBijective K X.left :=
    have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
    have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral X.hom)
    .of_geometricallyIntegral (k := K) (X := X.left)
  have : Scheme.GlobalSectionsBijective K Y.left :=
    have : IsProper (Y.left ↘ Spec (.of K)) := inferInstanceAs (IsProper Y.hom)
    have : GeometricallyIntegral (Y.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral Y.hom)
    .of_geometricallyIntegral (k := K) (X := Y.left)
  exact Scheme.IdealSheafData.Kunneth.subsingleton_H_one_toModules_prodIdeal (K := K) _ _
    (fun s hs ↦ eq_zero_of_mem_idealOfOpens_ker x.left (Over.w x) hs)
    (fun s hs ↦ eq_zero_of_mem_idealOfOpens_ker y.left (Over.w y) hs)

end TheoremOfCube

end AlgebraicGeometry
