/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Concrete terms of the alternating column filtration

Source: Stacks Project, Tag 09KP, filtration construction.
(blueprint: lem-pc-derived-total-filtration-stable)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex
namespace TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))

/-- The inclusion of the full column `-j` into total degree `k`.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def full (j : ℕ) (k : ℤ) :
    (K.X (-(j : ℤ))).X (k + j) ⟶ (K.total (ComplexShape.up ℤ)).X k :=
  K.ιTotal (ComplexShape.up ℤ) (-(j : ℤ)) (k + j) k (by simp)

/-- The inclusion of the lower column piece into total degree `k`.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def lower (j : ℕ) (k : ℤ) :
    (S j).X₁.X (k + j) ⟶ (K.total (ComplexShape.up ℤ)).X k :=
  (S j).f.f (k + j) ≫ (e j).hom.f (k + j) ≫ full K j k

/-- The actual submodule defining stage `n` in degree `k`: full columns enter at
`2*j+2`, their lower pieces at `2*j+1`. Source: Stacks Project, Tag 09KP, proof.
(blueprint: lem-pc-derived-total-filtration-stable) -/
noncomputable def term (n : ℕ) (k : ℤ) :
    Submodule A ((K.total (ComplexShape.up ℤ)).X k) :=
  ⨆ j : ℕ, (if 2 * j + 2 ≤ n then LinearMap.range (full K j k).hom else ⊥) ⊔
    (if 2 * j + 1 ≤ n then LinearMap.range (lower K S e j k).hom else ⊥)

lemma term_zero (k : ℤ) : term K S e 0 k = ⊥ := by
  simp [term]

lemma term_mono {n m : ℕ} (h : n ≤ m) (k : ℤ) :
    term K S e n k ≤ term K S e m k := by
  apply iSup_mono
  intro j
  apply sup_le_sup
  · split_ifs <;> first | exact le_rfl | exact bot_le | omega
  · split_ifs <;> first | exact le_rfl | exact bot_le | omega

/-- The alternating column submodules are preserved by the total differential.
Source: Stacks Project, Tag 09KP, proof, filtration construction.
(blueprint: lem-pc-derived-total-filtration-stable)

Proof. It suffices to check the generators in each range defining `term`.
For a full-column generator the vertical differential remains in that column,
while the horizontal differential goes from `-j` to `-(j-1)`. For `j>0`, that
full column entered two stages earlier. For `j=0`, its target column is positive
and zero by the hypothesis. For a lower-piece generator the vertical differential
remains in the lower piece, because the composite of the short-complex arrow and
`e.hom` is a cochain map. Its horizontal differential lands in the earlier full
column, with the same zero-column exception at `j=0`. Both summands of the total
differential therefore lie in the target submodule. Closure under addition and
scalar multiplication extends the calculation to the suprema of ranges.
-/
theorem differential_mem
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (n : ℕ) (k l : ℤ) (x : (K.total (ComplexShape.up ℤ)).X k)
    (hx : x ∈ term K S e n k) :
    (K.total (ComplexShape.up ℤ)).d k l x ∈ term K S e n l := by sorry

/-- Restriction of a module complex to differential-stable submodules.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def restrictComplex (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l) :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X k := ModuleCat.of A (M k)
  d k l := ModuleCat.ofHom
    (((T.d k l).hom.comp (M k).subtype).codRestrict (M l)
      (fun x ↦ h k l x x.property))
  shape k l hk := by
    ext x
    change T.d k l x.val = 0
    rw [HomologicalComplex.shape _ k l hk]
    rfl
  d_comp_d' k l m _ _ := by
    ext x
    change T.d l m (T.d k l x.val) = 0
    exact congrArg (fun f ↦ f x.val) (T.d_comp_d k l m)

/-- Inclusion from a restricted complex.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def restrictInclusion (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l) :
    restrictComplex T M h ⟶ T where
  f k := ModuleCat.ofHom (M k).subtype
  comm' k l _ := by ext x; rfl

/-- Inclusion for two nested differential-stable submodule families.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def restrictMap (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M N : ∀ k : ℤ, Submodule A (T.X k))
    (hM : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (hN : ∀ k l (x : T.X k), x ∈ N k → T.d k l x ∈ N l)
    (hMN : ∀ k, M k ≤ N k) : restrictComplex T M hM ⟶ restrictComplex T N hN where
  f k := ModuleCat.ofHom (Submodule.inclusion (hMN k))
  comm' k l _ := by ext x; rfl

lemma restrict_zero (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (h0 : ∀ k, M k = ⊥) : IsZero (restrictComplex T M h) := by
  rw [IsZero.iff_id_eq_zero]
  ext k x
  apply Subtype.ext
  exact (Submodule.mem_bot A).mp ((h0 k) ▸ x.property)

lemma restrict_mono (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l) :
    Mono (restrictInclusion T M h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro k
  apply (ModuleCat.mono_iff_injective _).mpr
  exact Subtype.val_injective

lemma restrict_comp (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M N : ∀ k : ℤ, Submodule A (T.X k))
    (hM : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (hN : ∀ k l (x : T.X k), x ∈ N k → T.d k l x ∈ N l)
    (hMN : ∀ k, M k ≤ N k) :
    restrictMap T M N hM hN hMN ≫ restrictInclusion T N hN =
      restrictInclusion T M hM := by
  ext k x
  rfl

lemma restrict_surjective (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ℕ → ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ n k l (x : T.X k), x ∈ M n k → T.d k l x ∈ M n l)
    (he : ∀ k (x : T.X k), ∃ n, x ∈ M n k) (k : ℤ) (x : T.X k) :
    ∃ (n : ℕ) (y : (restrictComplex T (M n) (h n)).X k),
      (restrictInclusion T (M n) (h n)).f k y = x := by
  obtain ⟨n, hx⟩ := he k x
  exact ⟨n, ⟨x, hx⟩, rfl⟩

variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- Restrict the total differential to the explicitly constructed submodules.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def complex (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  restrictComplex (K.total (ComplexShape.up ℤ)) (term K S e n)
    (differential_mem K S e h_positive n)

/-- Inclusion of a constructed stage into the total complex.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def inclusion (n : ℕ) : complex K S e h_positive n ⟶
    K.total (ComplexShape.up ℤ) :=
  restrictInclusion (K.total (ComplexShape.up ℤ)) (term K S e n)
    (differential_mem K S e h_positive n)

/-- Successive inclusion between constructed stages.
Source: Stacks Project, Tag 09KP, proof. -/
noncomputable def step (n : ℕ) : complex K S e h_positive n ⟶
    complex K S e h_positive (n + 1) :=
  restrictMap (K.total (ComplexShape.up ℤ)) (term K S e n) (term K S e (n + 1))
    (differential_mem K S e h_positive n) (differential_mem K S e h_positive (n + 1))
    (fun k ↦ term_mono K S e (Nat.le_succ n) k)

end TotalFreeFiltration
end CochainComplex
