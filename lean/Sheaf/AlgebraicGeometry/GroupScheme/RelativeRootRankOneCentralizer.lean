module

public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeRootCentralizerInterfaces
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.RepresentationTheory.RelativeTorusBundleWeights
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree

/-! # Relative rank-one centralizer of a root-kernel torus

Source: Conrad, Reductive group schemes, Lemma 4.1.3 and proof, pp.108--109
(blueprint: lem-sfb-relative-root-rank-one-centralizer).

Root lines are locally free modules, with no choice of a global basis.
The kernel torus and centralizer are specified as actual represented subfunctors.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj TensorProduct

namespace AlgebraicGeometry.RelativeRootCentralizer

/-- The centralizer of the primitive root-kernel torus is reductive, with exactly
the toral and opposite-root tangent summands, compatibly with all scalar extensions.

Source: Conrad, Reductive group schemes, Lemma 4.1.3, pp.108--109
(blueprint: lem-sfb-relative-root-rank-one-centralizer).

Proof plan, following the seven steps of the DAG:
1. Apply lem-sfb-relative-torus-centralizer-normalizer to the rank-zero torus to
   obtain the finite locally free tangent module and canonical base comparisons.
   On finite-free charts apply lem-sfb-relative-torus-bundle-weights; the unique
   coefficient projectors glue, with finite support by affine quasi-compactness.
   Multiplication of dual-number points adds their infinitesimal coefficients,
   and epsilon scaling is scalar multiplication.
2. Euclidean row operations carry the primitive alpha0 to a coordinate vector.
   The quotient lattice is free of rank r-1, with kernel torus Spec A[M/Z alpha0].
   Apply lem-sfb-relative-torus-centralizer-normalizer to this closed split torus.
3. On every geometric fibre use lem-sfb-reductive-rank-one-reflections. The given
   root line makes alpha a root, with opposite root line of dimension one and
   no other roots in Q alpha. The primitive kernel is the largest subtorus in
   ker alpha, since its character lattice is torsion free. Thus the fibre
   centralizer is connected reductive, and T is still maximal in it.
4. Apply lem-weil-pbc-finite-projective-prime-local-free to each weight summand.
   Fibre ranks give the negative root line and zero for every other nonzero
   multiple of alpha0. A nonzero vector has an annihilator in a maximal ideal,
   so vanishing at all localizations proves actual vanishing over nonreduced A.
5. Lie(T) maps to the zero weight. Its geometric-fibre maps are isomorphisms;
   on free charts the square determinant is a unit near each prime. Adjugates
   give the local inverses, proving equality of the actual tangent submodules.
6. The restriction-invariants clause of the relative weight lemma identifies
   Lie(H) with the sum indexed by Z alpha0, hence the displayed three summands.
   Universal commutation makes the kernel torus central in H.
7. Tensor the Laurent quotient and the split weight projectors along any A to B.
   Centralizer comparisons are the identity on the corresponding G-points.
   On a pure tensor b tensor D the tangent comparison has coefficient b D(c).
   Under B to C both successive and direct comparisons have coefficient
   c h(b) D(c0); pure tensors generate, giving successive coherence of weights,
   inclusions, and the decomposition. No flatness or line trivialization enters.
-/
theorem relative_root_rankOne_centralizer
    {A : Type u} [CommRing A] (r : ℕ) (G : Grp (Over (Spec (.of A))))
    [Smooth G.X.hom] [IsAffine G.X.left] [LocallyOfFinitePresentation G.X.hom]
    (i : RingGroupSchemes.splitTorus A r ⟶ G) [IsClosedImmersion i.hom.hom.left]
    (hred : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsReductive ((extend f).obj G))
    (hmax : ∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
      ReductiveTorusCentralizer.IsMaximalTorus ((extend f).map i))
    (α : Fin r → ℤ) (hα : α ≠ 0) (hline : IsLine (A := A) (weight i α))
    (α0 : Fin r → ℤ) (d : ℕ) (hd : 0 < d) (hdiv : α = d • α0)
    (hprimitive : ∃ c : Fin r → ℤ, ∑ j : Fin r, c j * α0 j = 1) :
    ∃ (K H : Grp (Over (Spec (.of A))))
      (k : K ⟶ RingGroupSchemes.splitTorus A r) (h : H ⟶ G)
      (j : RingGroupSchemes.splitTorus A r ⟶ H) (q : K ⟶ H),
      IsClosedImmersion k.hom.hom.left ∧
      Nonempty (K ≅ RingGroupSchemes.splitTorus A (r - 1)) ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B],
        Set.range (fun t : points K.X B ↦ t ≫ k.hom.hom) =
          {t | characterValue r α0 t = 1}) ∧
      IsClosedImmersion h.hom.hom.left ∧
      Smooth H.X.hom ∧ IsAffine H.X.left ∧ LocallyOfFinitePresentation H.X.hom ∧
      (∀ (F : Type u) [Field F] [IsAlgClosed F] (f : A →+* F),
        ReductiveTorusCentralizer.IsReductive ((extend f).obj H)) ∧
      j ≫ h = i ∧ q ≫ h = k ≫ i ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B]
        (t : points K.X B) (x : points H.X B), Commute (t ≫ q.hom.hom) x) ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B],
        centralizer (k ≫ i) B = Set.range (fun x : points H.X B ↦ x ≫ h.hom.hom)) ∧
      lieImage h = lieImage i ⊔ weight i α ⊔ weight i (-α) ∧
      Disjoint (lieImage i) (weight i α ⊔ weight i (-α)) ∧
      Disjoint (weight i α) (weight i (-α)) ∧ IsLine (A := A) (weight i (-α)) ∧
      (∀ (F : Type u) [Field F] [IsAlgClosed F] [Algebra A F],
        ReductiveTorusCentralizer.IsMaximalTorus ((extend (algebraMap A F)).map j) ∧
        ∀ m : Fin r → ℤ, (m ≠ 0 ∧ weightBase j F m ≠ ⊥) ↔ m = α ∨ m = -α) ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B],
        ∃ (eG : B ⊗[A] GrpObj.Lie G.X ≃ₗ[B]
            GrpObj.Lie ((extend (algebraMap A B)).obj G).X)
          (eH : B ⊗[A] GrpObj.Lie H.X ≃ₗ[B]
            GrpObj.Lie ((extend (algebraMap A B)).obj H).X),
          IsLieComparison G B eG.toLinearMap ∧ IsLieComparison H B eH.toLinearMap ∧
          (∀ m : Fin r → ℤ,
            ((weight i m).baseChange B).map eG.toLinearMap = weightBase i B m) ∧
          ((lieImage h).baseChange B).map eG.toLinearMap =
            lieImage ((extend (algebraMap A B)).map h) ∧
          ((lieImage i).baseChange B).map eG.toLinearMap =
            lieImage ((extend (algebraMap A B)).map i) ∧
          (∀ (C : Type u) [CommRing C] [Algebra B C],
            centralizer ((extend (algebraMap A B)).map (k ≫ i)) C =
              Set.range (fun x : points ((extend (algebraMap A B)).obj H).X C ↦
                x ≫ ((extend (algebraMap A B)).map h).hom.hom))) ∧
      ComparisonsCompose G ∧ ComparisonsCompose H := by
  sorry

end AlgebraicGeometry.RelativeRootCentralizer
