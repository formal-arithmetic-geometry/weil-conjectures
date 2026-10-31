/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import all WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import all WeilConjectures.CategoryTheory.DerivedCoupleExact

/-! # Additivity of iterated exact-couple maps

Source: Stacks Project, Homology, Tags 011R and 011T.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v uK vK

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {B : Type u} [Category.{v} B] [Abelian B]

private theorem next_id_D {s : ℕ} {X : BigradedExactCouple B s}
    (m : CoupleMorphism X X) (h : ∀ p q, m.tD p q = 𝟙 _) (p q : ℤ) :
    (nextMorphism m).tD p q = 𝟙 _ := by
  apply (cancel_mono (X.derivedDInclusion p q)).mp
  rw [nextMorphism_inclusion, h, Category.comp_id, Category.id_comp]

private theorem next_id_E {s : ℕ} {X : BigradedExactCouple B s}
    (m : CoupleMorphism X X) (h : ∀ p q, m.tE p q = 𝟙 _) (p q : ℤ) :
    (nextMorphism m).tE p q = 𝟙 _ := by
  obtain ⟨k, hk, he⟩ := nextMorphism_projection m p q
  have hk' : k = 𝟙 _ := by
    apply (cancel_mono (kernel.ι (X.d p q))).mp
    rw [hk, h, Category.comp_id, Category.id_comp]
  apply (cancel_epi (X.derivedEProjection p q)).mp
  rw [he, hk']
  change (𝟙 _) ≫ X.derivedEProjection p q = X.derivedEProjection p q ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

private theorem next_comp_D {s : ℕ} {X Y Z : BigradedExactCouple B s}
    (m : CoupleMorphism X Y) (n : CoupleMorphism Y Z) (t : CoupleMorphism X Z)
    (h : ∀ p q, t.tD p q = m.tD p q ≫ n.tD p q) (p q : ℤ) :
    (nextMorphism t).tD p q = (nextMorphism m).tD p q ≫ (nextMorphism n).tD p q := by
  apply (cancel_mono (Z.derivedDInclusion p q)).mp
  simp only [Category.assoc, nextMorphism_inclusion, h]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ n.tD p q) (nextMorphism_inclusion m p q).symm

private theorem next_comp_E {s : ℕ} {X Y Z : BigradedExactCouple B s}
    (m : CoupleMorphism X Y) (n : CoupleMorphism Y Z) (t : CoupleMorphism X Z)
    (h : ∀ p q, t.tE p q = m.tE p q ≫ n.tE p q) (p q : ℤ) :
    (nextMorphism t).tE p q = (nextMorphism m).tE p q ≫ (nextMorphism n).tE p q := by
  obtain ⟨k₁, hk₁, he₁⟩ := nextMorphism_projection m p q
  obtain ⟨k₂, hk₂, he₂⟩ := nextMorphism_projection n p q
  obtain ⟨k₃, hk₃, he₃⟩ := nextMorphism_projection t p q
  have hk : k₃ = k₁ ≫ k₂ := by
    apply (cancel_mono (kernel.ι (Z.d p q))).mp
    rw [Category.assoc, hk₂, ← Category.assoc, hk₁, Category.assoc, hk₃, h]
  apply (cancel_epi (X.derivedEProjection p q)).mp
  rw [he₃, hk, Category.assoc, ← he₂, ← Category.assoc, ← he₁, Category.assoc]

private theorem next_add_D {s : ℕ} {X Y : BigradedExactCouple B s}
    (m n t : CoupleMorphism X Y)
    (h : ∀ p q, t.tD p q = m.tD p q + n.tD p q) (p q : ℤ) :
    (nextMorphism t).tD p q = (nextMorphism m).tD p q + (nextMorphism n).tD p q := by
  apply (cancel_mono (Y.derivedDInclusion p q)).mp
  simp only [nextMorphism_inclusion, Preadditive.add_comp, Preadditive.comp_add, h]

private theorem next_add_E {s : ℕ} {X Y : BigradedExactCouple B s}
    (m n t : CoupleMorphism X Y)
    (h : ∀ p q, t.tE p q = m.tE p q + n.tE p q) (p q : ℤ) :
    (nextMorphism t).tE p q = (nextMorphism m).tE p q + (nextMorphism n).tE p q := by
  obtain ⟨k₁, hk₁, he₁⟩ := nextMorphism_projection m p q
  obtain ⟨k₂, hk₂, he₂⟩ := nextMorphism_projection n p q
  obtain ⟨k₃, hk₃, he₃⟩ := nextMorphism_projection t p q
  have hk : k₃ = k₁ + k₂ := by
    apply (cancel_mono (kernel.ι (Y.d p q))).mp
    rw [Preadditive.add_comp, hk₁, hk₂, hk₃, h, Preadditive.comp_add]
  apply (cancel_epi (X.derivedEProjection p q)).mp
  rw [Preadditive.comp_add, he₃, hk, Preadditive.add_comp, he₁, he₂]

/-- Iteration of the uniquely induced image and homology maps. -/
private def iterMap {X Y : BigradedExactCouple B 0} (m : CoupleMorphism X Y) :
    (r : ℕ) → CoupleMorphism (X.pageCouple r) (Y.pageCouple r)
  | 0 => m
  | r + 1 => nextMorphism (iterMap m r)

/-- The image square for the iterated map. -/
private theorem iterMap_inclusion {X Y : BigradedExactCouple B 0} (m : CoupleMorphism X Y)
    (r : ℕ) (p q : ℤ) :
    (iterMap m (r + 1)).tD p q ≫ (Y.pageCouple r).derivedDInclusion p q =
      (X.pageCouple r).derivedDInclusion p q ≫ (iterMap m r).tD p q :=
  nextMorphism_inclusion _ p q

/-- The homology square for the iterated map. -/
private theorem iterMap_projection {X Y : BigradedExactCouple B 0} (m : CoupleMorphism X Y)
    (r : ℕ) (p q : ℤ) :
    ∃ k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q),
      k ≫ kernel.ι ((Y.pageCouple r).d p q) =
        kernel.ι ((X.pageCouple r).d p q) ≫ (iterMap m r).tE p q ∧
      (X.pageCouple r).derivedEProjection p q ≫ (iterMap m (r + 1)).tE p q =
        k ≫ (Y.pageCouple r).derivedEProjection p q :=
  nextMorphism_projection _ p q

variable {K : Type uK} [Category.{vK} K] [Preadditive K]
    (X : K → BigradedExactCouple B 0)
    (m : ∀ {L M : K}, (L ⟶ M) → CoupleMorphism (X L) (X M))
    (hidD : ∀ (L : K) (p q : ℤ), (m (𝟙 L)).tD p q = 𝟙 _)
    (hidE : ∀ (L : K) (p q : ℤ), (m (𝟙 L)).tE p q = 𝟙 _)
    (hcompD : ∀ {L M N : K} (u : L ⟶ M) (v : M ⟶ N) (p q : ℤ),
      (m (u ≫ v)).tD p q = (m u).tD p q ≫ (m v).tD p q)
    (hcompE : ∀ {L M N : K} (u : L ⟶ M) (v : M ⟶ N) (p q : ℤ),
      (m (u ≫ v)).tE p q = (m u).tE p q ≫ (m v).tE p q)
    (haddD : ∀ {L M : K} (u v : L ⟶ M) (p q : ℤ),
      (m (u + v)).tD p q = (m u).tD p q + (m v).tD p q)
    (haddE : ∀ {L M : K} (u v : L ⟶ M) (p q : ℤ),
      (m (u + v)).tE p q = (m u).tE p q + (m v).tE p q)

include hidD in
omit [Preadditive K] in
private theorem iter_id_D (L : K) (r : ℕ) :
    ∀ p q, (iterMap (m (𝟙 L)) r).tD p q = 𝟙 _ := by
  induction r with
  | zero => exact hidD L
  | succ r ih => exact next_id_D _ ih

include hidE in
omit [Preadditive K] in
private theorem iter_id_E (L : K) (r : ℕ) :
    ∀ p q, (iterMap (m (𝟙 L)) r).tE p q = 𝟙 _ := by
  induction r with
  | zero => exact hidE L
  | succ r ih => exact next_id_E _ ih

include hcompD in
omit [Preadditive K] in
private theorem iter_comp_D {L M N : K} (u : L ⟶ M) (v : M ⟶ N) (r : ℕ) :
    ∀ p q, (iterMap (m (u ≫ v)) r).tD p q =
      (iterMap (m u) r).tD p q ≫ (iterMap (m v) r).tD p q := by
  induction r with
  | zero => exact hcompD u v
  | succ r ih => exact next_comp_D _ _ _ ih

include hcompE in
omit [Preadditive K] in
private theorem iter_comp_E {L M N : K} (u : L ⟶ M) (v : M ⟶ N) (r : ℕ) :
    ∀ p q, (iterMap (m (u ≫ v)) r).tE p q =
      (iterMap (m u) r).tE p q ≫ (iterMap (m v) r).tE p q := by
  induction r with
  | zero => exact hcompE u v
  | succ r ih => exact next_comp_E _ _ _ ih

include haddD in
private theorem iter_add_D {L M : K} (u v : L ⟶ M) (r : ℕ) :
    ∀ p q, (iterMap (m (u + v)) r).tD p q =
      (iterMap (m u) r).tD p q + (iterMap (m v) r).tD p q := by
  induction r with
  | zero => exact haddD u v
  | succ r ih => exact next_add_D _ _ _ ih

include haddE in
private theorem iter_add_E {L M : K} (u v : L ⟶ M) (r : ℕ) :
    ∀ p q, (iterMap (m (u + v)) r).tE p q =
      (iterMap (m u) r).tE p q + (iterMap (m v) r).tE p q := by
  induction r with
  | zero => exact haddE u v
  | succ r ih => exact next_add_E _ _ _ ih

/-- D-components of an additive diagram of exact couples are additive functors on every
iterated page. Their maps are the canonical image restrictions. -/
private def iterDFunctor (r : ℕ) (p q : ℤ) : K ⥤ B where
  obj L := ((X L).pageCouple r).D p q
  map u := (iterMap (m u) r).tD p q
  map_id L := iter_id_D X m hidD L r p q
  map_comp u v := iter_comp_D X m hcompD u v r p q

/-- E-components of an additive diagram of exact couples are additive functors on every
iterated page. Their maps are induced on differential homology. -/
private def iterEFunctor (r : ℕ) (p q : ℤ) : K ⥤ B where
  obj L := ((X L).pageCouple r).E p q
  map u := (iterMap (m u) r).tE p q
  map_id L := iter_id_E X m hidE L r p q
  map_comp u v := iter_comp_E X m hcompE u v r p q

/-- Functorial additive realization of all pages of a diagram of exact couples.
Source: Stacks Project, Homology, Tags 011R and 011T
(blueprint: lem-sp-additive-exact-couple-pages). -/
structure AdditivePageData where
  D (r : ℕ) (p q : ℤ) : K ⥤ B
  E (r : ℕ) (p q : ℤ) : K ⥤ B
  additiveD (r : ℕ) (p q : ℤ) : (D r p q).Additive
  additiveE (r : ℕ) (p q : ℤ) : (E r p q).Additive
  dIso (r : ℕ) (p q : ℤ) (L : K) : (D r p q).obj L ≅ ((X L).pageCouple r).D p q
  eIso (r : ℕ) (p q : ℤ) (L : K) : (E r p q).obj L ≅ ((X L).pageCouple r).E p q
  map (r : ℕ) {L M : K} (u : L ⟶ M) :
    CoupleMorphism ((X L).pageCouple r) ((X M).pageCouple r)
  mapD (r : ℕ) {L M : K} (u : L ⟶ M) (p q : ℤ) :
    (map r u).tD p q = (dIso r p q L).inv ≫ (D r p q).map u ≫ (dIso r p q M).hom
  mapE (r : ℕ) {L M : K} (u : L ⟶ M) (p q : ℤ) :
    (map r u).tE p q = (eIso r p q L).inv ≫ (E r p q).map u ≫ (eIso r p q M).hom
  initialD {L M : K} (u : L ⟶ M) (p q : ℤ) : (map 0 u).tD p q = (m u).tD p q
  initialE {L M : K} (u : L ⟶ M) (p q : ℤ) : (map 0 u).tE p q = (m u).tE p q
  image_square (r : ℕ) {L M : K} (u : L ⟶ M) (p q : ℤ) :
    (map (r + 1) u).tD p q ≫ ((X M).pageCouple r).derivedDInclusion p q =
      ((X L).pageCouple r).derivedDInclusion p q ≫ (map r u).tD p q
  homology_square (r : ℕ) {L M : K} (u : L ⟶ M) (p q : ℤ) :
    ∃ k : kernel (((X L).pageCouple r).d p q) ⟶ kernel (((X M).pageCouple r).d p q),
      k ≫ kernel.ι (((X M).pageCouple r).d p q) =
        kernel.ι (((X L).pageCouple r).d p q) ≫ (map r u).tE p q ∧
      ((X L).pageCouple r).derivedEProjection p q ≫ (map (r + 1) u).tE p q =
        k ≫ ((X M).pageCouple r).derivedEProjection p q

include hidD hidE hcompD hcompE haddD haddE in
/-- Iterating an additive diagram of exact couples gives additive page functors.

Source: Stacks Project, Homology, Tags 011R and 011T
(blueprint: lem-sp-additive-exact-couple-pages).

Proof: Restrict each D-map to the image of alpha. Restrict each E-map to the kernel
of the differential and descend to its homology quotient. The image inclusions are
monomorphisms, and the homology projections are epimorphisms. Cancellation therefore
proves that each successor operation preserves identities, composition and addition.
Induction gives the functor laws and additivity on every page. The defining image
and homology squares give the two stated compatibility conditions. -/
theorem exists_additive_page_data : Nonempty (AdditivePageData X m) := by
  refine ⟨{
    D := iterDFunctor X m hidD hcompD
    E := iterEFunctor X m hidE hcompE
    additiveD := fun r p q ↦ ?_
    additiveE := fun r p q ↦ ?_
    dIso := fun _ _ _ _ ↦ Iso.refl _
    eIso := fun _ _ _ _ ↦ Iso.refl _
    map := fun r {L M} u ↦ iterMap (m u) r
    mapD := ?_
    mapE := ?_
    initialD := fun {L M} _ _ _ ↦ rfl
    initialE := fun {L M} _ _ _ ↦ rfl
    image_square := fun r {L M} u p q ↦ iterMap_inclusion (m u) r p q
    homology_square := fun r {L M} u p q ↦ iterMap_projection (m u) r p q }⟩
  · exact ⟨fun {L M u v} ↦ iter_add_D X m haddD u v r p q⟩
  · exact ⟨fun {L M u v} ↦ iter_add_E X m haddE u v r p q⟩
  · intro r L M u p q
    change _ = 𝟙 _ ≫ ((iterMap (m u) r).tD p q ≫ 𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
  · intro r L M u p q
    change _ = 𝟙 _ ≫ ((iterMap (m u) r).tE p q ≫ 𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

end CategoryTheory.BigradedExactCouple
