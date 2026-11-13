/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteFieldTowerDegreeBound

/-!
# Fibre degree bounds under composition

Source: Stacks Project, Morphisms, Lemma Tag 03J6.

## Main statements

* `AlgebraicGeometry.Scheme.Hom.boundsFiberDegrees_comp`: fibre degree bounds multiply.
* `AlgebraicGeometry.Scheme.Hom.hasUniversallyBoundedFibers_comp`: uniform bounds compose.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

private theorem finite_of_finite_fibers_over_field {X Y : Scheme.{u}}
    {K : Type u} [Field K] (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [IsFinite g]
    (hf : ∀ y, IsFinite (f.fiberToSpecResidueField y)) : IsFinite f := by
  have : LocallyQuasiFinite f := .of_fiberToSpecResidueField f fun y ↦ by
    let := hf y
    infer_instance
  have : IsLocallyArtinian Y := .of_locallyQuasiFinite g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : IsArtinianScheme Y := ⟨⟩
  have hX : (Set.univ : Set X).Finite := by
    apply Set.Finite.of_finite_fibers f (Set.toFinite _)
    intro y _
    let := hf y
    have : IsLocallyArtinian (f.fiber y) :=
      .of_locallyQuasiFinite (f.fiberToSpecResidueField y)
    have : CompactSpace (f.fiber y) :=
      QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField y)
    have : IsArtinianScheme (f.fiber y) := ⟨⟩
    have : Finite (f ⁻¹' {y}) := Finite.of_equiv _ (f.fiberHomeo y).toEquiv
    simpa only [Set.univ_inter] using (Set.toFinite (f ⁻¹' {y}))
  have : Finite X := Set.finite_univ_iff.mp hX
  exact IsFinite.of_locallyQuasiFinite f

/-- Fibre degree bounds multiply under composition (Stacks Project, Morphisms, Tag 03J6).

Proof, following the seven steps of the node:
1. Fix `z : Z` and write `k = κ(z)`. The fibre `Y_z` is finite over `k`, hence affine
   with finite-dimensional global sections `B` of dimension at most `m`
. Its spectrum is finite discrete
. Decompose `B` into its
   localizations `B_i` at maximal ideals.
   Each factor is Artinian, with nilpotent
   maximal ideal, and residue field `K_i`.
2. Cartesian-square pasting identifies
   `X_z` with `X ×_Y Y_z`, and its fibres over the points of `Y_z` with
   `X ×_Y Spec K_i`. These are finite over `K_i`, with degree at most `n`
, hence have finite discrete spectra.
3. The underlying space of `X_z` is a finite union of these finite fibres; every point
   is closed, since the corresponding point of `Y_z` is closed. Thus `X_z` is finite
   discrete, hence affine. Put
   `A = Γ(X_z, O)`; the morphisms yield `k → B → A`
.
4. Affine fibre products identify the
   fibre over the maximal ideal `n_i` with `Spec (A/n_i A)`, so its dimension over
   `K_i` is at most `n`.
5. Tensor the finite product decomposition of `B` with `A` to obtain the decomposition
   into `A_i = A ⊗_B B_i`; dimensions over `k` add across this finite product.
6. Lift a `K_i`-basis of `A_i/n_i A_i`, of size `d_i ≤ n`, to `A_i`. Nilpotent Nakayama
 makes the resulting map `B_i^{d_i} → A_i`
   surjective. Consequently `dim_k A_i ≤ n * dim_k B_i`.
7. Sum these inequalities to get `dim_k A ≤ n * dim_k B ≤ n * m`. Thus `A` is finite
   over `k`, and `X_z → Spec k` is finite.
   This proves both clauses of `BoundsFiberDegrees (f ≫ g) (n * m)` for every `z`. -/
theorem boundsFiberDegrees_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n m : ℕ) (hf : BoundsFiberDegrees f n) (hg : BoundsFiberDegrees g m) :
    BoundsFiberDegrees (f ≫ g) (n * m) := by
  intro z
  let fz := Limits.pullback.snd f (g.fiberι z)
  let gz := g.fiberToSpecResidueField z
  have hgz : IsFinite gz := (hg z).1
  let := hgz
  have hfz : BoundsFiberDegrees fz n :=
    boundsFiberDegrees_pullback_snd f (g.fiberι z) n hf
  have hfzfin : IsFinite fz :=
    finite_of_finite_fibers_over_field fz gz fun y ↦ (hfz y).1
  let := hfzfin
  have H := (IsPullback.of_hasPullback f (g.fiberι z)).paste_vert
    (IsPullback.of_hasPullback g (Z.fromSpecResidueField z))
  have he : H.isoPullback.inv ≫ (fz ≫ gz) =
      (f ≫ g).fiberToSpecResidueField z := H.isoPullback_inv_snd
  have hfinite : IsFinite ((f ≫ g).fiberToSpecResidueField z) := by
    rw [← he]
    infer_instance
  refine ⟨hfinite, ?_⟩
  have hdeg := finrankΓ_comp_le_mul_of_finite fz gz n fun y ↦ (hfz y).2
  have hrank : (fz ≫ gz).finrankΓ =
      ((f ≫ g).fiberToSpecResidueField z).finrankΓ :=
    finrankΓ_eq_of_iso _ _ H.isoPullback (Iso.refl _) (by
      rw [Iso.refl_hom, Spec.map_id, Category.comp_id]
      change H.isoPullback.hom ≫ Limits.pullback.snd (f ≫ g) (Z.fromSpecResidueField z) =
        Limits.pullback.snd f (g.fiberι z) ≫ Limits.pullback.snd g (Z.fromSpecResidueField z)
      exact H.isoPullback_hom_snd)
  rw [← hrank]
  exact hdeg.trans (Nat.mul_le_mul_left n (hg z).2)

/-- A composition of morphisms with universally bounded fibres has universally bounded
fibres (Stacks Project, Morphisms, Tag 03J6). -/
theorem hasUniversallyBoundedFibers_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasUniversallyBoundedFibers f) (hg : HasUniversallyBoundedFibers g) :
    HasUniversallyBoundedFibers (f ≫ g) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hg
  exact ⟨n * m, boundsFiberDegrees_comp f g n m hn hm⟩

end AlgebraicGeometry.Scheme.Hom
