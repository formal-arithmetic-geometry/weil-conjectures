/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Finite admissible smooth coordinate covers

Source: Stacks Project, Tag 054L, and the Local charts paragraph (7.14) of
`sk-prop-cohsm` in the smooth-purity blueprint
(blueprint: lem-sp-smooth-admissible-coordinate-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth morphism of pure relative dimension `d` between separated finite-type
`k`-schemes admits a finite affine coordinate cover over the original base.
Source: Stacks Project, Tag 054L, with the admissibility elaboration of the
Local charts paragraph (7.14) of `sk-prop-cohsm`
(blueprint: lem-sp-smooth-admissible-coordinate-cover).

Proof plan (the eight steps of the source proof):
1. A field is Noetherian. Finite type and quasi-compactness make `X` and `Y`
   Noetherian, using local Noetherianity and compactness.
2. Affine space over `Y` is affine, separated, quasi-compact, locally of finite
   type, and Noetherian; its structure map to the field is separated and finite type.
3. At every point, the fixed-dimension smooth chart theorem supplies affine `U`
   and `V` and an etale map `e₀ : U ⟶ A^d_V` over `V`.
4. Quasi-compactness gives a finite subcover, reindexed by `Fin n`; the empty
   scheme yields `n = 0`.
5. The selected affine opens and their inclusions are Noetherian, separated,
   quasi-compact and of finite type over the field.
6. Affine-space projections over each `V` have the same geometric properties,
   and composing with `V ⟶ Y` gives the asserted properties of `A^d_V`.
7. The base-change map `A^d_V ⟶ A^d_Y` is an open immersion and hence etale;
   composing with `e₀` gives `e`, with `j ≫ f = e ≫ p_d`.
8. Since `e` is etale, separated, quasi-compact and locally of finite presentation,
   it is of finite presentation. The construction includes `d = 0` and the empty cover.
-/
theorem SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover
    {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ (n : ℕ) (U : Fin n → X.Opens) (V : Fin n → Y.Opens)
      (hUV : ∀ a, U a ≤ f ⁻¹ᵁ V a)
      (e₀ : ∀ a, (U a).toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) (V a).toScheme)
      (e : ∀ a, (U a).toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y),
      (∀ x : X, ∃ a, x ∈ U a) ∧
      IsNoetherian (AffineSpace (ULift.{u} (Fin d)) Y) ∧
      IsSeparated ((AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
      LocallyOfFiniteType
        ((AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
      QuasiCompact ((AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) ≫ (Y ↘ Spec (.of k))) ∧
      ∀ a, IsAffineOpen (U a) ∧ IsAffineOpen (V a) ∧
        Etale (e₀ a) ∧
        e₀ a ≫ (AffineSpace (ULift.{u} (Fin d)) (V a).toScheme ↘ (V a).toScheme) =
          f.resLE (V a) (U a) (hUV a) ∧
        e a = e₀ a ≫ AffineSpace.map (ULift.{u} (Fin d)) (V a).ι ∧
        IsSeparated (e a) ∧ Etale (e a) ∧ LocallyOfFinitePresentation (e a) ∧
        QuasiCompact (e a) ∧ QuasiSeparated (e a) ∧
        (U a).ι ≫ f = e a ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) ∧
        IsOpenImmersion (U a).ι ∧ QuasiCompact (U a).ι ∧ LocallyOfFiniteType (U a).ι ∧
        IsNoetherian (U a).toScheme ∧ IsNoetherian (V a).toScheme ∧
        IsNoetherian (AffineSpace (ULift.{u} (Fin d)) (V a).toScheme) ∧
        IsSeparated ((U a).ι ≫ (X ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((U a).ι ≫ (X ↘ Spec (.of k))) ∧
        QuasiCompact ((U a).ι ≫ (X ↘ Spec (.of k))) ∧
        IsSeparated ((V a).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType ((V a).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact ((V a).ι ≫ (Y ↘ Spec (.of k))) ∧
        IsSeparated
          ((AffineSpace (ULift.{u} (Fin d)) (V a).toScheme ↘ (V a).toScheme) ≫
            (V a).ι ≫ (Y ↘ Spec (.of k))) ∧
        LocallyOfFiniteType
          ((AffineSpace (ULift.{u} (Fin d)) (V a).toScheme ↘ (V a).toScheme) ≫
            (V a).ι ≫ (Y ↘ Spec (.of k))) ∧
        QuasiCompact
          ((AffineSpace (ULift.{u} (Fin d)) (V a).toScheme ↘ (V a).toScheme) ≫
            (V a).ι ≫ (Y ↘ Spec (.of k))) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin d)) Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
  have : CompactSpace (AffineSpace (ULift.{u} (Fin d)) Y) :=
    QuasiCompact.compactSpace_of_compactSpace (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y)
  have : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) Y) := ⟨⟩
  choose V U hV hU _ hx hUV e₀ he₀ hfactor using
    fun x : X ↦ Smooth.exists_etale_to_affineSpace f d x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let t : Fin s.card → X := fun a ↦ (s.equivFin.symm a).val
  refine ⟨s.card, (fun a ↦ U (t a)), (fun a ↦ V (t a)), (fun a ↦ hUV (t a)),
    (fun a ↦ e₀ (t a)),
    (fun a ↦ e₀ (t a) ≫ AffineSpace.map (ULift.{u} (Fin d)) (V (t a)).ι),
    ?_, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  · intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨s.equivFin ⟨i, hi⟩, by simpa [t] using hxi⟩
  · intro a
    have : IsAffine (U (t a)).toScheme := hU (t a)
    have : IsAffine (V (t a)).toScheme := hV (t a)
    have : Etale (e₀ (t a)) := he₀ (t a)
    have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) (V (t a)).ι) :=
      MorphismProperty.of_isPullback
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (V (t a)).ι).flip
        (inferInstance : IsOpenImmersion (V (t a)).ι)
    have hcomm : (U (t a)).ι ≫ f =
        (e₀ (t a) ≫ AffineSpace.map (ULift.{u} (Fin d)) (V (t a)).ι) ≫
          (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) := by
      rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hfactor,
        Scheme.Hom.resLE_comp_ι]
    refine ⟨hU (t a), hV (t a), he₀ (t a), hfactor (t a), rfl,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hcomm,
      inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance⟩
    · exact ⟨⟩
    · exact ⟨⟩
    · have : IsLocallyNoetherian
          (AffineSpace (ULift.{u} (Fin d)) (V (t a)).toScheme) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (AffineSpace (ULift.{u} (Fin d)) (V (t a)).toScheme ↘ (V (t a)).toScheme)
      exact ⟨⟩

end AlgebraicGeometry
