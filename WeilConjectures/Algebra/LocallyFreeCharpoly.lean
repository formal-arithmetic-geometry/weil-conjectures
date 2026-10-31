/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.CharpolyLocallyFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Characteristic polynomial of a finite locally free module of constant rank

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), characteristic-polynomial paragraph
(blueprint: def-weil-pbc-charpoly-locally-free).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

private theorem charpoly_baseChange_tower
    {S T : Type*} [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    {n : ℕ} (b : Module.Basis (Fin n) S (S ⊗[A] M))
    (e : Module.Basis (Fin n) T (T ⊗[A] M)) (φ : M →ₗ[A] M) :
    (LinearMap.toMatrix b b (φ.baseChange S)).charpoly.map (algebraMap S T) =
      (LinearMap.toMatrix e e (φ.baseChange T)).charpoly := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis e
  have := Module.Finite.of_basis e
  let L := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix,
    ← LinearMap.charpoly_baseChange, LinearMap.baseChange_baseChange]
  change (L.symm.conj (φ.baseChange T)).charpoly = _
  exact LinearEquiv.charpoly_conj _ _

/-- The characteristic polynomial of a finite locally free module of constant rank.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
The polynomial is chosen from `charpoly_locallyFree_exists_unique`, using scalar extensions
in the base ring's universe. Its characterization below holds in every universe. Only the
existence proof is postponed: the definition contains no missing data. -/
noncomputable def locallyFreeCharpoly {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (φ : M →ₗ[A] M) : Polynomial A :=
  Classical.choose (charpoly_locallyFree_exists_unique.{u, v, u} f hgen hfree φ)

/-- Characterization, uniqueness, monic expansion, and the free case.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
Proof (step 1 of the node): apply `lem-weil-pbc-charpoly-locally-free-existence`, whose
hypotheses are exactly this cover and these local bases. Its chosen polynomial has the
characterizing property, the expansion, and the free-case identity. For a larger universe,
apply that lemma there too. Lift each original localization by `ULift` to the larger
universe, transport its local basis, and compare both polynomials there. The lift is a ring
isomorphism, so coefficientwise injectivity on the standard cover identifies them. For a
target ring in a smaller universe, lift it and its scalar-extended basis in the same way;
transport the matrix equality back along the ring isomorphism. The matrix expression is
precisely the determinant of T times identity minus the scalar-extended endomorphism,
independent of the basis, by `def-weil-endomorphism-determinant`. The free case is scalar
extension by the identity ring map, using `def-weil-module-base-change`. -/
theorem locallyFreeCharpoly_spec {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (φ : M →ₗ[A] M) :
    let P : Polynomial A → Prop := fun χ ↦
      ∀ (A' : Type (max u w)) [CommRing A'] (ρ : A →+* A'),
        letI : Algebra A A' := RingHom.toAlgebra ρ;
        ∀ e : Module.Basis (Fin n) A' (A' ⊗[A] M),
          χ.map ρ = (LinearMap.toMatrix e e (φ.baseChange A')).charpoly;
    (P (locallyFreeCharpoly f hgen hfree φ) ∧
      ∀ χ : Polynomial A, P χ → χ = locallyFreeCharpoly f hgen hfree φ) ∧
    (∃ c : Fin n → A,
      locallyFreeCharpoly f hgen hfree φ = Polynomial.X ^ n +
        ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)) ∧
    (∀ e : Module.Basis (Fin n) A M,
      locallyFreeCharpoly f hgen hfree φ = (LinearMap.toMatrix e e φ).charpoly) := by
  classical
  obtain ⟨χ, hχ, hexp, hfreeχ⟩ :=
    charpoly_locallyFree_exists_unique.{u, v, w} f hgen hfree φ
  have hlow : ∀ (S : Type u) [CommRing S] (ρ : A →+* S),
      letI : Algebra A S := ρ.toAlgebra;
      ∀ b : Module.Basis (Fin n) S (S ⊗[A] M),
        χ.map ρ = (LinearMap.toMatrix b b (φ.baseChange S)).charpoly := by
    intro S _ ρ
    let : Algebra A S := ρ.toAlgebra
    intro b
    let T := ULift.{w} S
    let q : S →+* T := ULift.ringEquiv.symm.toRingHom
    let : Algebra S T := q.toAlgebra
    let : Algebra A T := (q.comp ρ).toAlgebra
    let : Module S T := Algebra.toModule
    let : Module A T := Algebra.toModule
    let : SMul S T := (inferInstance : Module S T).toSMul
    let : SMul A T := (inferInstance : Module A T).toSMul
    have : IsScalarTower A S T :=
      IsScalarTower.of_algebraMap_eq (R := A) (S := S) (A := T) fun x ↦ rfl
    let e := (b.baseChange T).map
      (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M)
    apply Polynomial.map_injective q ULift.ringEquiv.symm.injective
    rw [Polynomial.map_map]
    exact (hχ.1 T (q.comp ρ) e).trans (charpoly_baseChange_tower b e φ).symm
  have hχeq : χ = locallyFreeCharpoly f hgen hfree φ :=
    (Classical.choose_spec
      (charpoly_locallyFree_exists_unique.{u, v, u} f hgen hfree φ)).1.2 χ hlow
  rw [← hχeq]
  exact ⟨hχ, hexp, fun e ↦ hfreeχ ⟨e⟩ e⟩

/-- Over a nonzero ring the module determines its constant rank.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
Proof (step 3 of the node): choose a maximal ideal and an element of each cover outside it.
The localization at their product is nonzero and has both bases after further localization
(`def-weil-pbc-module-localization-away`, `def-weil-ring-localization-away`). Tensor with a
residue field (`def-weil-module-base-change`) and compare the two finite basis sizes. -/
theorem locallyFree_constantRank_eq [Nontrivial A] {n m r s : ℕ}
    (f : Fin r → A) (g : Fin s → A)
    (hfgen : Ideal.span (Set.range f) = ⊤)
    (hffree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (hggen : Ideal.span (Set.range g) = ⊤)
    (hgfree : ∀ j : Fin s,
      ∃ _e : Module.Basis (Fin m) (Localization.Away (g j))
        (LocalizedModule.Away (g j) M), True) : n = m := by
  classical
  obtain ⟨p, hp⟩ := Ideal.exists_maximal A
  have : p.IsMaximal := hp
  let K := A ⧸ p
  let : Field K := Ideal.Quotient.field p
  have rank_of_cover {d t : ℕ} (a : Fin t → A)
      (hgen : Ideal.span (Set.range a) = ⊤)
      (hfree : ∀ i : Fin t,
        ∃ _e : Module.Basis (Fin d) (Localization.Away (a i))
          (LocalizedModule.Away (a i) M), True) :
      Module.finrank K (K ⊗[A] M) = d := by
    obtain ⟨i, hi⟩ : ∃ i, a i ∉ p := by
      by_contra h
      have hle : Ideal.span (Set.range a) ≤ p :=
        Ideal.span_le.mpr (by
          rintro _ ⟨i, rfl⟩
          exact not_not.mp (fun hi ↦ h ⟨i, hi⟩))
      exact hp.ne_top (top_le_iff.mp (hgen ▸ hle))
    let S := Localization.Away (a i)
    let q : S →+* K := IsLocalization.Away.lift (a i)
      (show IsUnit (algebraMap A K (a i)) from
        isUnit_iff_ne_zero.mpr (by
          change Ideal.Quotient.mk p (a i) ≠ 0
          exact fun h ↦ hi (Ideal.Quotient.eq_zero_iff_mem.mp h)))
    let : Algebra S K := q.toAlgebra
    have : IsScalarTower A S K :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (IsLocalization.Away.lift_eq (a i) _ x).symm
    let b := (hfree i).choose.map
      (LocalizedModule.isBaseChange (Submonoid.powers (a i)) M).equiv.symm
    let e := (b.baseChange K).map
      (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S K K M)
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis e
  exact (rank_of_cover f hfgen hffree).symm.trans (rank_of_cover g hggen hgfree)

/-- Independence of both the trivializing cover and the stated constant rank.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: def-weil-pbc-charpoly-locally-free).
Proof (steps 2 and 3 of the node): at equal ranks the characterization does not mention the
cover, so uniqueness in `lem-weil-pbc-charpoly-locally-free-existence` identifies the choices.
For different ranks, if A is zero its polynomial ring is zero, hence the choices are equal.
Otherwise choose a maximal ideal, then cover elements f i and g j outside it. Localize both
bases further at their product, using `def-weil-pbc-module-localization-away` and
`def-weil-ring-localization-away`. This common localization is nonzero. Reduce at a maximal
ideal of it and use `def-weil-module-base-change`: the two vector-space bases have sizes n
and m, so invariant basis number gives n = m. Apply the equal-rank argument. -/
theorem locallyFreeCharpoly_eq {n m r s : ℕ} (f : Fin r → A) (g : Fin s → A)
    (hfgen : Ideal.span (Set.range f) = ⊤)
    (hffree : ∀ i : Fin r,
      ∃ _e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (hggen : Ideal.span (Set.range g) = ⊤)
    (hgfree : ∀ j : Fin s,
      ∃ _e : Module.Basis (Fin m) (Localization.Away (g j))
        (LocalizedModule.Away (g j) M), True)
    (φ : M →ₗ[A] M) :
    locallyFreeCharpoly f hfgen hffree φ = locallyFreeCharpoly g hggen hgfree φ := by
  classical
  by_cases hA : Nontrivial A
  · have := hA
    have hnm := locallyFree_constantRank_eq (M := M) f g hfgen hffree hggen hgfree
    subst m
    exact (((locallyFreeCharpoly_spec.{_,_,0} (M := M) f hfgen hffree φ).1.2
      _ (locallyFreeCharpoly_spec.{_,_,0} (M := M) g hggen hgfree φ).1.1).symm)
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    exact Subsingleton.elim _ _

end Algebra
