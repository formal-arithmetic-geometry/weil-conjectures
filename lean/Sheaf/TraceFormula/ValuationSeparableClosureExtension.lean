module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite-height valuation ring admits a same-height faithfully flat extension to a
separable closure, whose singleton spectrum map is fpqc.

Source: literature/stacks-project/more-algebra.tex, valuation extension as in Temkin Section 2.1
(blueprint: lem-trf-valuation-separable-closure-extension).
The stage-2 statement records the assembled valuation-theoretic conclusion.
The proof applies the Nagata valuation-extension and intersection statements, then the
algebraic-extension height correspondence, torsion-free flatness over valuation rings,
the flat-local faithful-flatness criterion, and affine verification of fpqc covering.
-/
theorem exists_valuation_separableClosure_extension
    {K Ks : Type u} [Field K] [Field Ks]
    [Algebra K Ks] [IsSepClosure K Ks]
    (V : ValuationSubring K)
    (hfinite : Set.Finite (Set.univ : Set (PrimeSpectrum V)))
    (hchain : IsChain (· ≤ ·) (Set.univ : Set (PrimeSpectrum V))) :
    ∃ (W : ValuationSubring Ks) (f : V →+* W),
      (∀ x : V, ((f x : W) : Ks) = algebraMap K Ks (x : K)) ∧
      (∀ x : K, ((algebraMap K Ks x : Ks) ∈ W ↔ x ∈ V)) ∧
      IsFractionRing W Ks ∧
      (IsLocalRing.maximalIdeal W).comap f = IsLocalRing.maximalIdeal V ∧
      Set.Finite (Set.univ : Set (PrimeSpectrum W)) ∧
      IsChain (· ≤ ·) (Set.univ : Set (PrimeSpectrum W)) ∧
      Order.krullDim (PrimeSpectrum V) = Order.krullDim (PrimeSpectrum W) ∧
      RingHom.FaithfullyFlat f ∧
      Presieve.ofArrows
          (fun _ : PUnit => Scheme.Spec.obj (Opposite.op (CommRingCat.of W)))
          (fun _ : PUnit =>
            Scheme.Spec.map (CommRingCat.ofHom f).op) ∈
        Scheme.fpqcPrecoverage (Scheme.Spec.obj (Opposite.op (CommRingCat.of V))) := by
  sorry

end AlgebraicGeometry
