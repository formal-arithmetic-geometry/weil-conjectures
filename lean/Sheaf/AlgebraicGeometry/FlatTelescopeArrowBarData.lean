/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement
import Sheaf.Algebra.Homology.FlatTruncationTower

/-! # Strict augmentation data from finite-piece bar diagrams

Source: Stacks Project Tags 03EW, 077J and 06XX for flat-generator resolutions;
the finite-piece and bar-enlargement argument below is an agent-written expansion
of the parent arrow-diagram construction, not a literal assertion of those tags.
(blueprint: lem-sc-flat-telescope-arrow-bar-data).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace AlgebraicGeometry

private theorem telescope_square_of_level_square {Y : Scheme.{u}}
    (E F : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)) (u : ∀ n : ℕ, F n ⟶ F (n + 1))
    (a : ∀ n : ℕ, E n ⟶ F n)
    (ha : ∀ n : ℕ, t n ≫ a (n + 1) = a n ≫ u n) :
    flatTelescopeDifferential E t ≫ Limits.Sigma.map a =
      Limits.Sigma.map a ≫ flatTelescopeDifferential F u := by
  apply Sigma.hom_ext
  intro n
  simp only [flatTelescopeDifferential, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.id_comp, Category.comp_id,
    Sigma.ι_map_assoc, Sigma.ι_desc_assoc, Sigma.ι_map, Category.assoc]
  rw [← Category.assoc, ha n, Category.assoc]
  simp only [Sigma.ι_desc]

/-- Tower and target-augmentation data, before constructing a source-cone map.
The target augmentations have zero shifted component and agree strictly with the
source augmentation on the two sum maps.

Source: Stacks Project 03EW, 077J and 06XX, and the finite-piece bar enlargement
isolated in `exists_flat_telescope_target_refinement`.

Proof. Choose a bounded flat truncation tower E,t,q for P. Augment it into P by
p_n = q_n followed by the truncation inclusion. Refine this tower against the first
target P. This gives a source R with level quasi-isomorphisms c_n:R_n -> E_n,
a target tower F and maps a_n:R_n -> F_n, and the required augmentation r1.
The maps c_n;p_n;f form a strictly compatible augmentation of R into Pprime.
Refine R against this second target, giving S with level quasi-isomorphisms
d_n:S_n -> R_n, a target tower G and maps b_n:S_n -> G_n, and augmentation r2.
Use S,F,G as the final three towers, d_n;a_n as the first level map, and b_n as
the second. Naturality of d implies that its sum map commutes with 1-shift;
compose that square with the first refinement's square. Put q'_n=d_n;c_n;q_n.
Quasi-isomorphisms compose, and the two naturality identities and the original
truncation compatibility give strict compatibility of q'. The two augmentation
identities follow by testing on coproduct inclusions and associating compositions.
The target augmentations and their zero shifted restrictions are unchanged.
(blueprint: lem-sc-flat-telescope-arrow-bar-data). -/
theorem exists_flat_telescope_arrow_bar_data (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) ∧
      ∃ (_c₁ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map a =
          Limits.Sigma.map a ≫ flatTelescopeDifferential E₁ t₁)
        (_c₂ : flatTelescopeDifferential E₀ t₀ ≫ Limits.Sigma.map b =
          Limits.Sigma.map b ≫ flatTelescopeDifferential E₂ t₂)
        (r₁ : CochainComplex.mappingCone (flatTelescopeDifferential E₁ t₁) ⟶ P)
        (r₂ : CochainComplex.mappingCone (flatTelescopeDifferential E₂ t₂) ⟶ P')
        (q : ∀ n : ℕ, E₀ n ⟶ P.truncLE (n : ℤ)),
        IsIso (Q.map r₁) ∧ IsIso (Q.map r₂) ∧
        (∀ n : ℕ, QuasiIso (q n)) ∧
        (∀ n : ℕ, t₀ n ≫ q (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
          q n ≫ P.ιTruncLE (n : ℤ)) ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential E₁ t₁)).comp
          (Cochain.ofHom r₁) (add_zero _) = 0 ∧
        (CochainComplex.mappingCone.inl (flatTelescopeDifferential E₂ t₂)).comp
          (Cochain.ofHom r₂) (add_zero _) = 0 ∧
        Limits.Sigma.map a ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential E₁ t₁) ≫ r₁ =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ∧
        Limits.Sigma.map b ≫
            CochainComplex.mappingCone.inr (flatTelescopeDifferential E₂ t₂) ≫ r₂ =
          Sigma.desc (fun n : ℕ ↦ q n ≫ P.ιTruncLE (n : ℤ)) ≫ f := by
  obtain ⟨E, t, q, hb, hf, hq, _, ht⟩ :=
    CochainComplex.exists_flat_truncation_tower P
  let p : ∀ n : ℕ, E n ⟶ P := fun n ↦ q n ≫ P.ιTruncLE (n : ℤ)
  have hp (n : ℕ) : t n ≫ p (n + 1) = p n := ht n
  obtain ⟨R, F, s, u, c, a, hbR, hfR, hbF, hfF, hc, hs, ha,
    r₁, hr₁, hz₁, he₁⟩ :=
    exists_flat_telescope_target_refinement Y E t hb hf P hP p hp
  let p' : ∀ n : ℕ, R n ⟶ P' := fun n ↦ c n ≫ p n ≫ f
  have hp' (n : ℕ) : s n ≫ p' (n + 1) = p' n := by
    dsimp [p']
    rw [← Category.assoc, hs n, Category.assoc,
      ← Category.assoc (t n) (p (n + 1)) f, hp n]
  obtain ⟨S, G, v, w, d, b, hbS, hfS, hbG, hfG, hd, hv, hb',
    r₂, hr₂, hz₂, he₂⟩ :=
    exists_flat_telescope_target_refinement Y R s hbR hfR P' hP' p' hp'
  let q' : ∀ n : ℕ, S n ⟶ P.truncLE (n : ℤ) := fun n ↦ d n ≫ c n ≫ q n
  let a' : ∀ n : ℕ, S n ⟶ F n := fun n ↦ d n ≫ a n
  have hδ := telescope_square_of_level_square S R v s d hv
  have ha₀ := telescope_square_of_level_square R F s u a ha
  have hb₀ := telescope_square_of_level_square S G v w b hb'
  have ha' : flatTelescopeDifferential S v ≫ Limits.Sigma.map a' =
      Limits.Sigma.map a' ≫ flatTelescopeDifferential F u := by
    simp only [a', ← Sigma.map_comp_map]
    rw [← Category.assoc, hδ, Category.assoc, ha₀, ← Category.assoc]
  have hq' (n : ℕ) : QuasiIso (q' n) := by
    have := hd n
    have := hc n
    have := hq n
    dsimp [q']
    infer_instance
  have ht' (n : ℕ) :
      v n ≫ q' (n + 1) ≫ P.ιTruncLE ((n + 1 : ℕ) : ℤ) =
        q' n ≫ P.ιTruncLE (n : ℤ) := by
    dsimp [q']
    simp only [Category.assoc]
    rw [← Category.assoc (v n) (d (n + 1)), hv n]
    simp only [Category.assoc]
    rw [← Category.assoc (s n) (c (n + 1)), hs n]
    simp only [Category.assoc]
    simpa only [Category.assoc, Int.natCast_succ] using
      congrArg (fun k ↦ d n ≫ c n ≫ k) (ht n)
  refine ⟨S, F, G, v, u, w, a', b, hbS, hfS, hbF, hfF, hbG, hfG,
    ha', hb₀, r₁, r₂, q', hr₁, hr₂, hq', ht', hz₁, hz₂, ?_, ?_⟩
  · simp only [a', ← Sigma.map_comp_map, Category.assoc]
    rw [he₁]
    apply Sigma.hom_ext
    intro n
    simp [q', p, Category.assoc]
  · rw [he₂]
    apply Sigma.hom_ext
    intro n
    simp [q', p', p, Category.assoc]


end AlgebraicGeometry
