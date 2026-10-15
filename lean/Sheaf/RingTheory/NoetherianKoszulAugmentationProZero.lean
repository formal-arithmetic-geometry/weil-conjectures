/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.RingTheory.Filtration
import Sheaf.Algebra.Homology.BoundedDerivedTowerProZero

/-!
# Pro-zero cones of the Noetherian Koszul augmentation

Source: Stacks Project, Tags 0921, 0922 and 0G3B
(blueprint: lem-weil-pbc-noetherian-koszul-augmentation-pro-zero).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace ExteriorAlgebra

/-- The canonical augmentations and power transitions exist and their strict cone transitions
are eventually zero in the derived category. Indices `m : ℕ` mean exponent `m + 1`.
The exterior model is the signed total tensor model: a wedge indexed by an increasing
subset is the corresponding tensor basis vector. All maps are specified on components;
the quotient transition is specified after the surjective quotient map. Thus the existential
maps are uniquely determined, including their strict commuting squares.

Source: Stacks Project, Tags 0921, 0922 and 0G3B
(blueprint: lem-weil-pbc-noetherian-koszul-augmentation-pro-zero).

Proof: put J_m = (a_i^(m+1)). The exterior contraction differential has the usual alternating
signs; the exterior power of the diagonal a_i^(k-m) commutes with contraction. The quotient
kills the degree-one differential, giving the augmentation and strict squares. Signed
insertion of a generator gives dh+hd = a_i^(m+1), so J_m annihilates Koszul homology.
Apply Artin--Rees (lem-weil-pbc-artin-rees) to the cycles inside each finite free term.
For large k the negative-degree transition has image in J_m^(c+1), so its cycle image
lies in J_m times the cycles and hence in boundaries. A maximum kills all negative degrees.
The augmentation cone has H^0=0, H^(-1)=I^(m+1)/J_m, and lower cohomology the shifted
negative Koszul homology. The containment I^(r*m+1) ≤ J_m kills the degree-minus-one
transition eventually. All cones are supported in [-r-1,0]. Apply the uniform bounded-tower
lemma (lem-weil-pbc-bounded-derived-tower-pro-zero), Tag 0G3B, to upgrade eventual
cohomological vanishing to vanishing of these very cone maps. For r=0 the augmentation
is the identity under the degree-zero exterior identification, so its cone is acyclic. -/
theorem noetherian_koszul_augmentation_pro_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (r : ℕ) (a : Fin r → A) :
    ∃ (ε : ∀ m : ℕ, koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))))
      (t : ∀ m k : ℕ, m ≤ k →
        (koszulComplex A r (fun i ↦ a i ^ (k + 1)) ⟶
          koszulComplex A r (fun i ↦ a i ^ (m + 1))))
      (q : ∀ m k : ℕ, m ≤ k →
        ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
            (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (k + 1))) ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj
            (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))))),
      (∀ m, (ε m).f 0 = ModuleCat.ofHom
        (((Ideal.span (Set.range a)) ^ (m + 1)).mkQ.comp
          (_root_.exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap)) ∧
      (∀ m k h n, (t m k h).f n = ModuleCat.ofHom
        (_root_.exteriorPower.map n (Finsupp.linearCombination A
          (fun i ↦ Finsupp.single i (a i ^ (k - m)))))) ∧
      (∀ m k h, ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (k + 1)).mkQ ≫
        (q m k h).f 0 = ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ) ∧
      ∃ hc : ∀ m k h,
        HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat ≫
            HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat =
          HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat ≫
            HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat,
        ∀ m : ℕ, ∃ (k : ℕ) (h : m ≤ k),
          DerivedCategory.Q.map
            (HomologicalComplex.homotopyCofiber.mapArrowHom
              (HomologicalComplex.extendMap (ε k) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (ε m) ComplexShape.embeddingDownNat)
              (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
              (Arrow.homMk
                (HomologicalComplex.extendMap (t m k h) ComplexShape.embeddingDownNat)
                (HomologicalComplex.extendMap (q m k h) ComplexShape.embeddingDownNat)
                (hc m k h))) = 0 := by
  sorry

end ExteriorAlgebra
