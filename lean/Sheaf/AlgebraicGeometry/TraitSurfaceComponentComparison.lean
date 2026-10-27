/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Blowup.Gluing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.NodalTraitRegularization
import Sheaf.AlgebraicGeometry.CommonRegularSurfaceResolution
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Complement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Componentwise comparison of regular nodal trait models

Source: Stacks Project, resolve.tex, Tag 0C5S, with models.tex, Tag 0CDE,
Algebra Tag 00HS and the properness argument for special centres
(blueprint: lem-sfb-trait-surface-component-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Regular projective flat nodal trait models have matched integral surface components
and a common componentwise point-blowup comparison preserving the prescribed generic map.
The two input models are indexed by `Fin 2`. No fibre connectedness or geometric
integrality is assumed. Both the empty blowup tower and disconnected models are included.
The component inclusions exhibit actual scheme coproducts, and the last comparison is
explicitly the coproduct of the common integral models, with its induced maps.

Source: Stacks Project, resolve.tex, Tag 0C5S, `lemma-birational-regular-surfaces`,
with models.tex, Tag 0CDE, and Algebra Tag 00HS.
(blueprint: lem-sfb-trait-surface-component-comparison).

Proof plan (the eight steps of the node):
1. Choose a uniformizer. The DVR unit-times-uniformizer-power lemma identifies
   `K = R[1/π]`, so Spec K is the generic open of Spec R. Base change gives the
   corresponding open in each model. The DVR and its spectrum are Noetherian;
   projectivity implies properness (lem-kun-projective-implies-proper).
2. The finite-singular-charts lemma gives Noetherianity. Apply nodal trait
   regularization. Its centres are nonregular, so regularity forces length zero.
   The terminal decomposition gives finite clopen integral regular surfaces of dimension two.
3. Flat going down at a special-fibre point produces a generalization over the generic
   point, using affine-open stalk localization. Every component therefore dominates the
   trait and has nonempty integral dense generic open.
4. The generic opens partition the generic fibre into clopen integral subschemes, hence
   are exactly its irreducible components. The prescribed generic isomorphism determines
   a unique matching and restricts to an isomorphism on every matched pair.
5. Closed immersions into proper models make the components proper. Apply
   lem-sfb-common-regular-surface-resolution componentwise with these dense generic opens.
   This gives regular integral common models and the two reduced-closed-point towers.
6. At every stage of any such tower the structural map stays proper and the scheme stays
   Noetherian (finite-type-over-Noetherian, blowup-proper and proper-composition).
   Properness sends a closed point to a closed point of the trait, necessarily its special point.
7. Blowup-complement makes every stage a generic isomorphism. The maps from each common
   generic fibre agree with the prescribed identification on a dense open; schematic density
   of a nonempty open in an integral scheme and separated uniqueness extend this agreement
   to its whole generic fibre (lemma-nagata-ext-scheme-theoretically-dominant-separated).
8. Take the finite coproduct of the common integral models. The coproduct universal
   property supplies its two maps; generic isomorphisms and their compatibility glue.
   Only ordinary integrality of component generic fibres was used.
-/
theorem exists_trait_surface_component_comparison
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (T : Fin 2 → Over (Spec (.of R)))
    [∀ i, IsHProjective (T i).hom] [∀ i, Flat (T i).hom]
    [∀ i, LocallyOfFinitePresentation (T i).hom]
    [∀ i, Smooth (pullback.snd (T i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (hregular : ∀ i, IsRegularScheme (T i).left)
    (hfib : ∀ (i : Fin 2) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)),
      Nonempty ↥(pullback (T i).hom g) ∧ IsReduced (pullback (T i).hom g) ∧
        (pullback (T i).hom g).IsPureDimension 1)
    (hnodal : ∀ (i : Fin 2) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of R)) (x : ↥(pullback (T i).hom g)),
      IsClosed ({x} : Set ↥(pullback (T i).hom g)) →
      x ∉ (pullback.snd (T i).hom g).smoothLocus →
      Nonempty
        (AdicCompletion
          (IsLocalRing.maximalIdeal ((pullback (T i).hom g).presheaf.stalk x))
          ((pullback (T i).hom g).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    (α : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (T 0) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (T 1)) :
    ∃ (n : Fin 2 → ℕ) (C : ∀ i, Fin (n i) → Over (Spec (.of R)))
      (j : ∀ i a, C i a ⟶ T i),
      (∀ i, IsIso (Sigma.desc (fun a ↦ (j i a).left))) ∧
      (∀ i a, IsOpenImmersion (j i a).left ∧ IsClosedImmersion (j i a).left ∧
        IsIntegral (C i a).left ∧ IsRegularScheme (C i a).left ∧
        topologicalKrullDim (C i a).left = 2 ∧ DenseRange (C i a).hom ∧
        IsIntegral (pullback (C i a).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        IsOpenImmersion (pullback.fst (C i a).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        DenseRange (pullback.fst (C i a).hom
          (Spec.map (CommRingCat.ofHom (algebraMap R K))))) ∧
      (∃ E : ∀ i, Fin (n i) ≃ ↥(irreducibleComponents
          ↥(((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
            (T i)).left)),
        ∀ i a, (E i a).val = Set.range
          (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
            (j i a)).left)) ∧
      (∃ σ : Fin (n 0) ≃ Fin (n 1),
        (∀ a, α.hom.left '' Set.range
            (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
              (j 0 a)).left) =
          Set.range
            (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
              (j 1 (σ a))).left)) ∧
        (∀ τ : Fin (n 0) ≃ Fin (n 1),
          (∀ a, α.hom.left '' Set.range
              (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
                (j 0 a)).left) =
            Set.range
              (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
                (j 1 (τ a))).left)) → τ = σ) ∧
        ∃ (V : Fin (n 0) → Over (Spec (.of R)))
          (q₀ : ∀ a, V a ⟶ C 0 a) (q₁ : ∀ a, V a ⟶ C 1 (σ a))
          (β : ∀ a,
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (C 0 a) ≅
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
              (C 1 (σ a))),
          (∀ a, IsRegularScheme (V a).left ∧ IsIntegral (V a).left ∧
            (β a).hom ≫
                (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
                  (j 1 (σ a)) =
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
                  (j 0 a) ≫ α.hom ∧
            IsIso ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (q₀ a)) ∧
            IsIso ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (q₁ a)) ∧
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (q₁ a) =
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (q₀ a) ≫
                (β a).hom ∧
            (∃ (A : OrdinaryBlowupTower (C 0 a).left)
              (e : (V a).left ≅ A.level (Fin.last A.length)),
              e.hom ≫ A.toBase (Fin.last A.length) = (q₀ a).left ∧
              ∀ b : Fin A.length,
                ∃ (p : A.level b.castSucc) (hp : IsClosed ({p} : Set _)),
                  A.center b = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ∧
                  (A.toBase b.castSucc ≫ (C 0 a).hom) p = IsLocalRing.closedPoint R) ∧
            (∃ (A : OrdinaryBlowupTower (C 1 (σ a)).left)
              (e : (V a).left ≅ A.level (Fin.last A.length)),
              e.hom ≫ A.toBase (Fin.last A.length) = (q₁ a).left ∧
              ∀ b : Fin A.length,
                ∃ (p : A.level b.castSucc) (hp : IsClosed ({p} : Set _)),
                  A.center b = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ∧
                  (A.toBase b.castSucc ≫ (C 1 (σ a)).hom) p = IsLocalRing.closedPoint R)) ∧
          ∃ (W : Over (Spec (.of R)))
            (e : W.left ≅ ∐ (fun a ↦ (V a).left)) (p₀ : W ⟶ T 0) (p₁ : W ⟶ T 1),
            e.hom ≫ Sigma.desc (fun a ↦ (q₀ a).left ≫ (j 0 a).left) = p₀.left ∧
            e.hom ≫ Sigma.desc (fun a ↦ (q₁ a).left ≫ (j 1 (σ a)).left) = p₁.left ∧
            IsIso ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₀) ∧
            IsIso ((Over.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₁) ∧
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₁ =
              (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₀ ≫
                α.hom) ∧
      (∀ (i : Fin 2) (A : OrdinaryBlowupTower (T i).left),
        (∀ b : Fin A.length, ∃ (p : A.level b.castSucc) (hp : IsClosed ({p} : Set _)),
          A.center b = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) →
        (∀ (b : Fin (A.length + 1)) (p : A.level b),
          IsClosed ({p} : Set (A.level b)) →
          (A.toBase b ≫ (T i).hom) p = IsLocalRing.closedPoint R) ∧
        ∀ b : Fin (A.length + 1), IsIso (pullback.snd (A.toBase b)
          (pullback.fst (T i).hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))))) := by
  sorry

end AlgebraicGeometry
