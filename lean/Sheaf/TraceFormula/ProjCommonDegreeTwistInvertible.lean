/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties

/-!
# Common-degree twists on a quasi-compact Proj open

Source: Stacks Project, Constructions, Tags 01MU and 01MW, the characterization of the
invertibility locus and the proof after the finite standard-open cover
(blueprint: lem-trf-proj-common-degree-twist-invertible).

The statement records the open `W_e` by its equivalent union of standard opens and records
the canonical multiplication maps by their action on all local pure tensors. They multiply
homogeneous fractions on the standard-open cover.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The common-degree invertibility and multiplication assertion on an open of `Proj`.

Source: Stacks Project, Constructions, Tags 01MU (lemma-where-invertible) and 01MW
(lemma-ample-on-proj), clauses (1)--(4)
(blueprint: lem-trf-proj-common-degree-twist-invertible).

Proof, following the five steps of the DAG node:
1. The given finite positive-degree standard-open cover is the cover that quasi-compactness
   and `lem-weil-pbc-proj-standard-open-inclusion` provide in the source proof.
2. Put `g_i = f_i^(e/d_i)`. Divisibility and positivity give degree `e` and a positive
   exponent. A prime contains a positive power exactly when it contains its base, so
   `D_+(g_i) = D_+(f_i)` and these opens still cover `V`.
3. In the union characterization of `W_e`, take `a = g_i` and `b = 1`, of degrees `e`
   and zero. Thus each `D_+(g_i)` lies in `W_e`, proving `V ≤ W`.
4. On a chart `D_+(ab)` with `deg(a) = deg(b) + e`, the fractions `(a/b)^n`, for all
   integers `n`, trivialize `O(ne)` and multiplication takes tensor products of those
   frames to the corresponding frame. These compatible local maps glue. The description
   of this locus in `lem-trf-proj-twist-section-basic-open` and Tag 01MU therefore gives
   all integer twists invertible and all the stated binary multiplication maps invertible
   after restriction. In particular the twists of degree `e*k`, `k > 0`, are invertible.
5. Start with the restricted unit map to `O(0)` and recursively multiply the first
   `O(e)` factor by the preceding tensor-power map. The displayed zero and successor
   formulas express exactly these canonical maps on arbitrary local sections. Local pure
   tensors generate after sheafification, so the formulas determine the maps uniquely.
   The unit map and binary multiplication isomorphisms show inductively that these maps
   are isomorphisms for every positive `k`. Associativity gives the canonical iterated
   multiplication. If the index type is empty, the cover forces `V` empty and every
   conclusion still holds.
-/
theorem commonDegreeTwistInvertible
    (V : (Proj 𝒜).Opens) [CompactSpace V.toScheme]
    (I : Type v) [Finite I]
    (f : I → A) (d : I → ℕ)
    (hf : ∀ i, f i ∈ 𝒜 (d i))
    (hd : ∀ i, 0 < d i)
    (hcover : V ≤ ⨆ i, basicOpen 𝒜 (f i))
    (e : ℕ) (he : 0 < e)
    (hdiv : ∀ i, d i ∣ e)
    (W : (Proj 𝒜).Opens)
    (hW : W = ⨆ (α : ℕ) (β : ℕ) (a : 𝒜 α) (b : 𝒜 β) (_ : α = β + e),
      basicOpen 𝒜 ((a : A) * (b : A)))
    : V ≤ W ∧
      (∀ n : ℤ, ((twist 𝒜 (n * (e : ℤ))).restrict V.ι).IsInvertible) ∧
      (∀ n m : ℤ,
        ∃ μ : Scheme.Modules.tensorObj
            ((twist 𝒜 (n * (e : ℤ))).restrict V.ι)
            ((twist 𝒜 (m * (e : ℤ))).restrict V.ι) ⟶
            (twist 𝒜 ((n + m) * (e : ℤ))).restrict V.ι,
          IsIso μ ∧ ∀ (Q : V.toScheme.Opens)
            (s : Γ((twist 𝒜 (n * (e : ℤ))).restrict V.ι, Q))
            (t : Γ((twist 𝒜 (m * (e : ℤ))).restrict V.ι, Q)) (x : V.ι ''ᵁ Q),
            (((twist 𝒜 ((n + m) * (e : ℤ))).restrictAppIso V.ι Q).hom
              (μ.app Q (Scheme.Modules.tmulSection s t))).val x =
            ((((twist 𝒜 (n * (e : ℤ))).restrictAppIso V.ι Q).hom s).val x :
              Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) *
              (((twist 𝒜 (m * (e : ℤ))).restrictAppIso V.ι Q).hom t).val x) ∧
      (∀ k : ℕ, 0 < k →
        ((twist 𝒜 (Int.ofNat (e * k))).restrict V.ι).IsInvertible) ∧
      (∃ μ : ∀ k : ℕ,
          ((twist 𝒜 (e : ℤ)).restrict V.ι).tensorPow k ⟶
            (twist 𝒜 (Int.ofNat (e * k))).restrict V.ι,
        (∀ k : ℕ, 0 < k → IsIso (μ k)) ∧
        (∀ (Q : V.toScheme.Opens) (x : V.ι ''ᵁ Q),
          (((twist 𝒜 (Int.ofNat (e * 0))).restrictAppIso V.ι Q).hom
            ((μ 0).app Q (Scheme.Modules.unitSectionsEquiv Q 1))).val x =
              (1 : Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal)) ∧
        (∀ (k : ℕ) (Q : V.toScheme.Opens)
          (s : Γ((twist 𝒜 (e : ℤ)).restrict V.ι, Q))
          (t : Γ(((twist 𝒜 (e : ℤ)).restrict V.ι).tensorPow k, Q))
          (x : V.ι ''ᵁ Q),
          (((twist 𝒜 (Int.ofNat (e * (k + 1)))).restrictAppIso V.ι Q).hom
            ((μ (k + 1)).app Q (Scheme.Modules.tmulSection s t))).val x =
          ((((twist 𝒜 (e : ℤ)).restrictAppIso V.ι Q).hom s).val x :
            Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) *
            (((twist 𝒜 (Int.ofNat (e * k))).restrictAppIso V.ι Q).hom
              ((μ k).app Q t)).val x)) := by
  sorry

end AlgebraicGeometry.Proj
