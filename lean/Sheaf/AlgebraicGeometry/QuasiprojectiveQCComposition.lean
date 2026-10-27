/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.CompositionFiniteAffineTwistBounds
import Sheaf.AlgebraicGeometry.InvertibleTwistOpenRestriction
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover

/-!
# Composition of relatively ample finite-type morphisms

Source: Stacks Project, Morphisms, Tag 0C4M (lemma-composition-quasi-projective),
with Tags 01VH (definition-relatively-ample) and 0C4K (lemma-ample-composition)
(blueprint: lem-sfb-quasiprojective-qc-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite-type morphisms admitting relatively ample invertible modules compose over a
quasi-compact final base. Relative ampleness is written out on every affine base open;
tensor pullback by the inverse-image open inclusion is restriction. The existential
invertibility witnesses for restrictions only supply the proof argument of `IsAmple`.

Source: Stacks Project, Morphisms, Tag 0C4M, using Tags 01VH and 0C4K.
(blueprint: lem-sfb-quasiprojective-qc-composition).

Proof:
1. Apply lem-sfb-finite-type-composition-base-change(1) to obtain finite type of the
composite h = f ≫ g, hence quasi-compactness (def-weil-finite-type-morphism).
2. Choose a finite affine open cover V_i of S using def-pc-scheme and
 def-weil-pbc-quasi-compact-scheme. Restrict to Y_i = g inverse-image V_i and
X_i = h inverse-image V_i. Finite type of the restricted f_i follows by base change
(lem-sfb-finite-type-composition-base-change(2)); L_i remains relatively ample, M_i
is ample, and their invertibility follows by restricting local trivializations
(def-sc-invertible-module).
3. Apply lem-sfb-relative-ample-absolute-twist to f_i, L_i and M_i. Take a common
exponent a as the maximum of zero and the finitely many eventual ampleness bounds.
This works also for the empty cover, with a = 0.
4. Set N = L tensor f^*(M tensor-power a), using def-pc-module-pullback and
 def-pur-sheaf-tensor-product. Invertibility and the monoidal pullback identities of
lem-weil-pbc-invertible-pullback-tensor identify its restriction to X_i with the
ample twist from step 3. For a = 0 the unit comparison sends b tensor c to b f_i^#(c),
with inverse b to b tensor 1. Absolute ampleness is invariant under this isomorphism
(def-weil-pbc-ample-invertible-module).
5. Apply lem-trf-scheme-relative-ample-affine-cover to h and N. Quasi-compactness
from step 1 and ampleness on the cover from step 4 give ampleness over every affine
open of S, precisely relative ampleness. Together with finite type from step 1 this
is the conclusion; the empty-base case has empty sources and is included. -/
theorem exists_isAmple_on_affineOpens_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace S]
    (hf : ∃ (L : X.Modules) (_ : L.IsInvertible),
      ∀ V : Y.Opens, IsAffineOpen V →
        ∃ h : ((tensorPullback (f ⁻¹ᵁ V).ι).obj L).IsInvertible,
          @IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) h)
    (hg : ∃ (M : Y.Modules) (_ : M.IsInvertible),
      ∀ V : S.Opens, IsAffineOpen V →
        ∃ h : ((tensorPullback (g ⁻¹ᵁ V).ι).obj M).IsInvertible,
          @IsAmple (g ⁻¹ᵁ V).toScheme ((tensorPullback (g ⁻¹ᵁ V).ι).obj M) h) :
    LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧
      ∃ (N : X.Modules) (_ : N.IsInvertible),
        ∀ V : S.Opens, IsAffineOpen V →
          ∃ h : ((tensorPullback ((f ≫ g) ⁻¹ᵁ V).ι).obj N).IsInvertible,
            @IsAmple ((f ≫ g) ⁻¹ᵁ V).toScheme
              ((tensorPullback ((f ≫ g) ⁻¹ᵁ V).ι).obj N) h := by
  classical
  obtain ⟨L, hLi, hL⟩ := hf
  obtain ⟨M, hMi, hM⟩ := hg
  obtain ⟨hft, hqc, r, V, hV, hcover, hlocal⟩ :=
    exists_finite_affine_cover_eventually_isAmple_tensorPullback
      f g L M hL hM
  have hdata := fun i : Fin r ↦
    (Classical.choose_spec ((hlocal i).2.2.2)).2.2
  let b : Fin r → ℤ := fun i ↦ Classical.choose (hdata i)
  have hb : ∀ i, 0 ≤ b i := fun i ↦ (Classical.choose_spec (hdata i)).1
  let a : ℤ := ∑ i, b i
  have hle : ∀ i, b i ≤ a := by
    intro i
    dsimp [a]
    exact Finset.single_le_sum (fun j hj ↦ hb j) (Finset.mem_univ i)
  let N : X.Modules := tensorObj L ((tensorPullback f).obj (M.tensorPow a.toNat))
  have hNinv : N.IsInvertible := by
    dsimp [N]
    exact (invertible_twist_open_restriction f L M a.toNat).2.2.1
  have hcoverN : ∀ i : Fin r,
      ∃ h : ((tensorPullback ((f ≫ g) ⁻¹ᵁ V i).ι).obj N).IsInvertible,
        @IsAmple ((f ≫ g) ⁻¹ᵁ V i).toScheme
          ((tensorPullback ((f ≫ g) ⁻¹ᵁ V i).ι).obj N) h := by
    intro i
    obtain ⟨hleft, hright, e, he, hamp⟩ :=
      (invertible_twist_open_restriction f L M a.toNat).2.2.2 (g ⁻¹ᵁ V i)
    obtain ⟨hloc, haloc⟩ := (Classical.choose_spec (hdata i)).2 a (hle i)
    exact ⟨hleft, hamp.mpr (by simpa using haloc)⟩
  refine ⟨hft, hqc, N, hNinv, ?_⟩
  intro W hW
  exact ⟨_, scheme_relative_ample_affine_cover (f ≫ g) N V hV hcover
    (fun i ↦ (hcoverN i).choose_spec) W hW⟩

end AlgebraicGeometry.Scheme.Modules
