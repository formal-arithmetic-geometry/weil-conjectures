/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import Sheaf.RingTheory.NormalFlatHilbertConvolution
import Mathlib.RingTheory.Flat.Equalizer

/-! # The tangent initial ideal of a normally flat pair

Source: Hironaka, Certain numerical characters of singularities (1970),
section 2, p.153 and the paragraph after Example (4.2), p.157.
(blueprint: lem-trf-normal-flat-double-initial-ideal).

The coefficient ring `(T/a)/(P/a)` is the canonical third-isomorphism-theorem
model of `T/P`. The fibre uses `k tensor gr`, the symmetric tensor convention.
All three polynomial maps are pinned on constants and every variable.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Hironaka

/-- The canonical coefficient map `(T/a)/(P/a) -> T/M`, obtained from
`(T/a)/(P/a) = T/P` and the quotient factor `T/P -> T/M`.
Source: Hironaka (1970), section 2, p.153, normal-cone fibre construction
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
def normalFlatResidueMap {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x)) :
    ((T ⧸ a) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk a)) →+*
      IsLocalRing.ResidueField T :=
  (Ideal.Quotient.factor (show Ideal.span (Set.range x) ≤ IsLocalRing.maximalIdeal T by
    rw [← hparams.1]
    apply Ideal.span_mono
    rintro z ⟨i, rfl⟩
    exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))).comp
      (DoubleQuot.quotQuotEquivQuotOfLE ha).toRingHom

/-- The normal-cone fibre with the ambient residue field, using the canonical
coefficient map above. This is the tensor construction, not a chosen comparison.
Source: Hironaka (1970), section 2, p.153
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
abbrev normalFlatParameterFibre {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x)) : Type u :=
  letI := (normalFlatResidueMap x y hparams a ha).toAlgebra
  IsLocalRing.ResidueField T ⊗[
    (T ⧸ a) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk a)]
    Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk a))

/-- The tensor-product commutative ring structure on the fibre.
Source: Hironaka (1970), section 2, p.153
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
instance normalFlatParameterFibreCommRing
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x)) :
    CommRing (normalFlatParameterFibre x y hparams a ha) :=
  letI := (normalFlatResidueMap x y hparams a ha).toAlgebra
  inferInstanceAs (CommRing (IsLocalRing.ResidueField T ⊗[
    (T ⧸ a) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk a)]
    Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk a))))

/-- The residue-field action on the tensor fibre, `c -> c tensor 1`.
Source: Hironaka (1970), section 2, p.153
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
instance normalFlatParameterFibreAlgebra
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x)) :
    Algebra (IsLocalRing.ResidueField T) (normalFlatParameterFibre x y hparams a ha) :=
  letI := (normalFlatResidueMap x y hparams a ha).toAlgebra
  inferInstanceAs (Algebra (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField T ⊗[
    (T ⧸ a) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk a)]
    Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk a))))

/-- A homogeneous initial class in the normal-cone fibre, `1 tensor [b]_n`.
Source: Hironaka (1970), section 2, pp.153--154
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
def normalFlatParameterClass {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x)) (n : ℕ)
    (b : (((Ideal.span (Set.range x)).map (Ideal.Quotient.mk a)) ^ n : Ideal (T ⧸ a))) :
    normalFlatParameterFibre x y hparams a ha :=
  letI := (normalFlatResidueMap x y hparams a ha).toAlgebra
  1 ⊗ₜ DirectSum.of
    (Ideal.associatedGradedPiece ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk a))) n
    (Submodule.Quotient.mk b)

/-- The canonical normal-fibre parameter map beta, by polynomial evaluation.
Source: Hironaka (1970), section 2, p.153
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
def normalFlatBeta {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x)) :
    MvPolynomial (Fin (r + 1)) (IsLocalRing.ResidueField T) →+*
      normalFlatParameterFibre x y hparams a ha :=
  MvPolynomial.eval₂Hom (algebraMap (IsLocalRing.ResidueField T) _)
    (fun i ↦ normalFlatParameterClass x y hparams a ha 1
      ⟨Ideal.Quotient.mk a (x i), by
        rw [pow_one]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))⟩)

/-- The residue coefficient map into the tangent graded ring of `T/a`, induced
by the actual quotient `T -> T/a` in degree zero.
Source: Hironaka (1970), section 2, pp.153--154
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
def normalFlatTangentCoefficient {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (a : Ideal T) : IsLocalRing.ResidueField T →+*
      Ideal.associatedGraded ((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a)) :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal T)
    ((Ideal.associatedGradedRingHom
      ((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a))).comp (Ideal.Quotient.mk a))
    (fun _b hb ↦ Ideal.associatedGradedRingHom_ker _ _ (Ideal.mem_map_of_mem _ hb))

/-- The tangent parameter map gamma, pinned by its actual quotient coefficient
map and the degree-one classes of the images of all x and y parameters.
Source: Hironaka (1970), section 2, pp.153--154
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
def normalFlatGamma {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) :
    MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T) →+*
      Ideal.associatedGraded ((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a)) :=
  MvPolynomial.eval₂Hom (normalFlatTangentCoefficient a) (fun i ↦
    DirectSum.of (Ideal.associatedGradedPiece
      ((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a))) 1
      (Submodule.Quotient.mk
        (⟨Ideal.Quotient.mk a (Sum.elim x y i), by
          rw [pow_one]
          apply Ideal.mem_map_of_mem
          rw [← hparams.1]
          apply Ideal.subset_span
          cases i with
          | inl i => exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
          | inr j => exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)⟩ :
            (((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a)) ^ 1 :
              Ideal (T ⧸ a)))))

/-- The ambient tangent parameter map, with constants in degree zero and all
specified parameters in degree one.
Source: Hironaka (1970), section 2, p.153
(blueprint: lem-trf-normal-flat-double-initial-ideal). -/
def normalFlatAmbientMap {T : Type u} [CommRing T] [IsRegularLocalRing T]
    {r s : ℕ} (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y)) :
    MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T) →+*
      Ideal.associatedGraded (IsLocalRing.maximalIdeal T) :=
  MvPolynomial.eval₂Hom
    (algebraMap (T ⧸ IsLocalRing.maximalIdeal T)
      (Ideal.associatedGraded (IsLocalRing.maximalIdeal T))) (fun i ↦
    DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal T)) 1
      (Submodule.Quotient.mk (⟨Sum.elim x y i, by
        rw [pow_one, ← hparams.1]
        apply Ideal.subset_span
        cases i with
        | inl i => exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
        | inr j => exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)⟩ :
          (IsLocalRing.maximalIdeal T ^ 1 : Ideal T))))

/-- The tangent initial ideal is extended from the normal-cone fibre equations.
All maps are the explicitly constructed parameter maps above. The three
homogeneity clauses express preservation of total degree; for the tensor fibre,
its degree-n piece is the residue-field span of the tensors of degree-n classes.
Bijectivity of the ambient map identifies `k[X,Y]` with `gr_M T` as graded rings.
The tensor order `k tensor G` is identified with `G tensor k` by tensor symmetry.

Source: Hironaka, Certain numerical characters of singularities (1970),
section 2, p.153 and paragraph after Example (4.2), p.157
(blueprint: lem-trf-normal-flat-double-initial-ideal).

Proof, following the node's six steps:
1. The parameters generate M. The regular-local generator theorem makes the
full list and its x-prefix regular, and T/P regular local of dimension s.
The regular-sequence graded-polynomial theorem identifies gr_M T with k[X,Y]
and gr_P T with (T/P)[X], using exactly these parameter maps.
2. Products of generators span every power, so their degree-d classes span
G_d and the tangent graded pieces. Tensor balancing gives the fibre spanning
assertion. Evaluation therefore defines graded surjections beta and gamma,
with identity coefficient map in degree zero; ker beta is homogeneous.
3. Each G_d is a direct summand of the flat A-module G, hence flat. Tensor the
exact row 0 -> K_d -> A[X]_d -> G_d -> 0 with k. The flat-quotient tensor
injection theorem identifies ker beta_d with the reduction of K_d.
4. Lift the coefficients of u in K_d to T. Its evaluation t lies in P^d and
maps into I^(d+1). Lift that image to v in P^(d+1). Then t-v belongs to a,
and its M-initial class is u reduced modulo the maximal ideal of A. Thus
extension of ker beta is contained in ker gamma, and gamma factors as the
specified graded surjection S[Y] -> gr_m R.
5. The normal-flat Hilbert convolution theorem and the maximal-adic graded
length bridge give equal cumulative dimensions for S[Y] and gr_m R. Count
Y-monomials of degree at most n-j by choose(n-j+s,s); for s=0 there is one.
All the graded vector spaces involved are finite dimensional.
6. In each finite degree range the factor map is a surjection between spaces
of equal finite dimension, hence injective. Every element is a finite sum of
homogeneous classes, so the factor map is an isomorphism. Its explicit
factorization gives the displayed equality of kernels for these parameters.
No coefficient field in T, reducedness, completeness or characteristic is assumed.
-/
theorem normalFlatDoubleInitialIdeal
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (r s : ℕ) (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (a : Ideal T) (ha : a ≤ Ideal.span (Set.range x))
    [Module.Flat ((T ⧸ a) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk a))
      (Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk a)))] :
    Function.Surjective (normalFlatBeta x y hparams a ha) ∧
    Function.Surjective (normalFlatGamma x y hparams a) ∧
    Function.Bijective (normalFlatAmbientMap x y hparams) ∧
    (∀ (n : ℕ) (p : MvPolynomial (Fin (r + 1)) (IsLocalRing.ResidueField T)),
      p.IsHomogeneous n → normalFlatBeta x y hparams a ha p ∈
        Submodule.span (IsLocalRing.ResidueField T)
          (Set.range (normalFlatParameterClass x y hparams a ha n))) ∧
    (∀ (n : ℕ) (p : MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T)),
      p.IsHomogeneous n → ∃ b : Ideal.associatedGradedPiece
          ((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a)) n,
        normalFlatGamma x y hparams a p = DirectSum.of
          (Ideal.associatedGradedPiece
            ((IsLocalRing.maximalIdeal T).map (Ideal.Quotient.mk a))) n b) ∧
    (∀ (n : ℕ) (p : MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T)),
      p.IsHomogeneous n → ∃ b : Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal T) n,
        normalFlatAmbientMap x y hparams p =
          DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal T)) n b) ∧
    RingHom.ker (normalFlatGamma x y hparams a) =
      (RingHom.ker (normalFlatBeta x y hparams a ha)).map (MvPolynomial.rename Sum.inl) := by
  sorry

end Hironaka
