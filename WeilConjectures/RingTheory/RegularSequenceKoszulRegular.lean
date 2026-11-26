/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.RingTheory.KoszulTensorConeCoordinates
import WeilConjectures.RingTheory.KoszulTensorZerothBoundarySaturation

/-!
# Regular sequences are Koszul-regular

A weakly regular sequence on a module `M` is `M`-Koszul-regular: the tensor Koszul complex has
no positive homology.

## Implementation details

Successive injectivity is Mathlib's `IsWeaklyRegular`; it does not require the final
quotient to be nonzero. `List.ofFn f` lists the given finite sequence in its original order.
Negative terms of the homology and Koszul complexes are zero by their extension convention.

The proof inducts on the length. Splitting each exterior-power basis according to whether the
final generator occurs identifies the new complex with `A_n ⊕ A_(n-1)` and differential
`D(a, b) = (d a + f_r b, -d b)` (Tag 0629), where `A` is the complex of the prefix. A positive
cycle `(a, b)` has `b = d c` (by induction, or by injectivity of `f_r` in degree one), and
subtracting `D(0, -c)` reduces it to a cycle `(a', 0)`, a boundary by induction.

## References

* [Stacks, Tag 062F]
* [Stacks, Tag 0629]
-/

@[expose] public section

universe u v

namespace RingTheory.Sequence

private theorem isKoszulRegularOn_empty {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (f : Fin 0 → R) :
    IsKoszulRegularOn M f := by
  intro n hn
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin 0) R (Fin 0 →₀ R)).exteriorPower n
  have : IsEmpty (Set.powersetCard (Fin 0) n) :=
    ⟨fun s ↦ hn (s.property.symm.trans
      (Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _)))⟩
  have : Subsingleton (⋀[R]^n (Fin 0 →₀ R)) := b.repr.injective.subsingleton
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  change CategoryTheory.Limits.IsZero
    (ModuleCat.of R (TensorProduct R (⋀[R]^n (Fin 0 →₀ R)) M))
  exact ModuleCat.isZero_of_subsingleton _

private theorem cone_positive_exact {R : Type u} [CommRing R]
    (A B : ChainComplex (ModuleCat.{v} R) ℕ) (t : R)
    (e₀ : B.X 0 ≃ₗ[R] A.X 0)
    (e : ∀ n : ℕ, B.X (n + 1) ≃ₗ[R] A.X (n + 1) × A.X n)
    (h₀ : ∀ x : B.X 1, e₀ (B.d 1 0 x) =
      A.d 1 0 (e 0 x).1 + t • (e 0 x).2)
    (hd : ∀ (n : ℕ) (x : B.X (n + 2)), e n (B.d (n + 2) (n + 1) x) =
      (A.d (n + 2) (n + 1) (e (n + 1) x).1 + t • (e (n + 1) x).2,
      -A.d (n + 1) n (e (n + 1) x).2))
    (hA : ∀ (n : ℕ) (x : A.X (n + 1)), A.d (n + 1) n x = 0 →
      ∃ y : A.X (n + 2), A.d (n + 2) (n + 1) y = x)
    (hs : ∀ b : A.X 0, (∃ a : A.X 1, A.d 1 0 a = t • b) →
      ∃ c : A.X 1, A.d 1 0 c = b) :
    ∀ (n : ℕ) (x : B.X (n + 1)), B.d (n + 1) n x = 0 →
      ∃ y : B.X (n + 2), B.d (n + 2) (n + 1) y = x := by
  intro n x hx
  have ha : A.d (n + 1) n (e n x).1 + t • (e n x).2 = 0 := by
    cases n with
    | zero => simpa [hx] using (h₀ x).symm
    | succ n =>
      have hh := congrArg Prod.fst (hd n x)
      simpa [hx] using hh.symm
  obtain ⟨c, hc⟩ : ∃ c : A.X (n + 1), A.d (n + 1) n c = (e n x).2 := by
    cases n with
    | zero =>
      apply hs
      refine ⟨-(e 0 x).1, ?_⟩
      rw [map_neg]
      exact neg_eq_of_add_eq_zero_right ha
    | succ n =>
      apply hA n
      have hh := congrArg Prod.snd (hd n x)
      simpa [hx] using hh
  have hcycle : A.d (n + 1) n ((e n x).1 + t • c) = 0 := by
    rw [map_add, map_smul, hc]
    exact ha
  obtain ⟨a, ha'⟩ := hA n _ hcycle
  refine ⟨(e (n + 1)).symm (a, -c), ?_⟩
  apply (e n).injective
  rw [hd]
  simp only [LinearEquiv.apply_symm_apply, map_neg, hc, ha',
    smul_neg, neg_neg]
  ext <;> simp

private theorem cycles_are_boundaries {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (h : CategoryTheory.Limits.IsZero (K.homology (n + 1))) :
    ∀ x : K.X (n + 1), K.d (n + 1) n x = 0 →
      ∃ y : K.X (n + 2), K.d (n + 2) (n + 1) y = x := by
  have he := (K.exactAt_iff_isZero_homology (n + 1)).mpr h
  have hs := (K.exactAt_iff' (i := n + 2) (j := n + 1) (k := n)
    (by simp) (by simp)).mp he
  exact (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mp hs

private theorem homology_isZero_of_cycles_are_boundaries
    {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (h : ∀ x : K.X (n + 1), K.d (n + 1) n x = 0 →
      ∃ y : K.X (n + 2), K.d (n + 2) (n + 1) y = x) :
    CategoryTheory.Limits.IsZero (K.homology (n + 1)) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (K.exactAt_iff' (i := n + 2) (j := n + 1) (k := n)
    (by simp) (by simp)).mpr
  exact (CategoryTheory.ShortComplex.moduleCat_exact_iff _).mpr h

/-- Successive injectivity on the quotients by the preceding elements implies
`M`-Koszul-regularity. -/
theorem isKoszulRegularOn_of_isWeaklyRegular {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R)
    (h : IsWeaklyRegular M (List.ofFn f)) : IsKoszulRegularOn M f := by
  induction r with
  | zero => exact isKoszulRegularOn_empty M f
  | succ r ih =>
    let g : Fin r → R := fun i ↦ f i.castSucc
    have hh : IsWeaklyRegular M (List.ofFn g) ∧
        IsSMulRegular (M ⧸ (Ideal.ofList (List.ofFn g) • ⊤ : Submodule R M))
          (f (Fin.last r)) := by
      rw [List.ofFn_succ', List.concat_eq_append, isWeaklyRegular_append_iff,
        isWeaklyRegular_singleton_iff] at h
      exact h
    have hp := ih g hh.1
    obtain ⟨e₀, e, h₀, hd⟩ := ExteriorAlgebra.exists_koszulTensorConeCoordinates M f
    have hs := ExteriorAlgebra.koszulTensor_zeroth_boundary_saturation M g
      (f (Fin.last r)) hh.2
    intro n hn
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    apply homology_isZero_of_cycles_are_boundaries
    apply cone_positive_exact _ _ (f (Fin.last r)) e₀ e h₀ hd
    · intro k
      exact cycles_are_boundaries _ k (hp (k + 1) (Nat.succ_ne_zero k))
    · exact hs

/-- Every `M`-regular sequence is `M`-Koszul-regular. -/
theorem IsRegular.isKoszulRegularOn {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {r : ℕ} {f : Fin r → R}
    (h : IsRegular M (List.ofFn f)) : IsKoszulRegularOn M f := by
  exact isKoszulRegularOn_of_isWeaklyRegular M f h.toIsWeaklyRegular

/-- Every regular sequence in a commutative ring is Koszul-regular. -/
theorem IsRegular.isKoszulRegular {R : Type u} [CommRing R]
    {r : ℕ} {f : Fin r → R} (h : IsRegular R (List.ofFn f)) : IsKoszulRegular f := by
  let e : ExteriorAlgebra.koszulComplexTensor R r f R ≅
      ExteriorAlgebra.koszulComplex R r f :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (TensorProduct.rid R (⋀[R]^n (Fin r →₀ R))).toModuleIso)
      (by
        intro i j hij
        have he : i = j + 1 := by simpa using hij.symm
        subst i
        simp only [ExteriorAlgebra.koszulComplexTensor, ExteriorAlgebra.koszulComplex,
          ChainComplex.of_d]
        ext1
        apply TensorProduct.ext
        ext x
        simp)
  intro n hn
  exact (isKoszulRegularOn_of_isWeaklyRegular R f h.toIsWeaklyRegular n hn).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e.symm)

end RingTheory.Sequence
