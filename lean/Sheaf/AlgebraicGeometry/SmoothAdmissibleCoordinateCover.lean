/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.Topology.Defs.Filter

/-!
# Finite admissible smooth coordinate covers

Source: Stacks Project, Tag 054L, and the Charts paragraph of
`det-sp-reduction-exceptional` in the smooth-purity blueprint
(blueprint: lem-sp-smooth-admissible-coordinate-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth morphism of pure relative dimension `d` between separated finite-type
`k`-schemes admits a finite affine coordinate cover over the original base.
Source: Stacks Project, Tag 054L, with the admissibility elaboration of Step 13 of
`det-sp-reduction-exceptional`
(blueprint: lem-sp-smooth-admissible-coordinate-cover).

Proof plan:
1. The field is Noetherian. By `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-qcqs-over-affine`, `X` and `Y` are Noetherian, compact and quasi-separated.
2. At every point choose affine standard-smooth charts of exactly dimension `d` using
   `lem-sc-standard-smooth-local-relative-dimension`. The etale polynomial map of
   `lem-sc-standard-smooth-etale-polynomial-chart` gives `e₀` under `def-sbc-affine-space`.
   The identity over the affine base is
   `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`.
3. Compactness (`def-weil-pbc-quasi-compact-scheme`) gives finitely many source opens
   covering `X`; choose no opens when `X` is empty.
4. Open subschemes are Noetherian by `lem-weil-pbc-noetherian-open-subscheme-noetherian`.
   Their inclusions are quasi-compact by `lem-weil-pbc-qcqs-morphism-permanence` and of
   finite type by `lem-weil-pbc-qc-open-immersion-finite-type`. Separation follows from
   `lem-weil-pbc-separated-cancellation`; composition uses
   `lem-sfb-finite-type-composition-base-change` and `lem-weil-pbc-proper-fp-permanence`.
5. Affine-space projections are affine (`pqf-def-affine-morphism`) and hence separated
   and quasi-compact (`lem-weil-pbc-affine-morphism-permanence`). Polynomial variables
   generate their rings, giving finite type. Composition and finite type over the
   Noetherian field give all claimed properties of both affine spaces.
6. `AffineSpace.map` of each target open inclusion is its base change, an open immersion.
   By `lem-weil-pbc-etale-composition-cancellation`, its composite with `e₀` is etale.
   Functoriality of the projection gives the factorization over the original `Y`.
7. The source is affine and the target quasi-separated. The finite-presentation clause
   of `lem-weil-pbc-qcqs-morphism-permanence` applies to each etale composite. Separation
   follows by `lem-weil-pbc-separated-cancellation` from the separated source over `k`.
   The argument includes dimension zero, since the empty-variable affine space is its base.
-/
theorem SmoothOfRelativeDimension.exists_finite_admissible_coordinate_cover
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
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
            (V a).ι ≫ (Y ↘ Spec (.of k))) :=
  sorry

end AlgebraicGeometry
