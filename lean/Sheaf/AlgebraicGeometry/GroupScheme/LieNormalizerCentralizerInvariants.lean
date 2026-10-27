/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Lie spaces of scheme centralizers and normalizers

Source: Milne, Algebraic Groups (2017), Proposition 10.34, printed pp.197--198
(blueprint: lem-sfb-lie-normalizer-centralizer-invariants).

The Lie space is the existing `GrpObj.Lie`, canonically the identity tangent space.
The adjoint calculus is normalized by actual dual-number points. The quotient action
is characterized by intertwining with the quotient map, and is rational in every basis.
The last equality uses the image of Lie(N) in g/h: together with h contained in Lie(N)
and injectivity of the tangent inclusions, this is precisely Lie(N)/h as a subspace.
All fixed-vector tests quantify over algebras, including nonreduced and zero algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj TensorProduct

namespace AlgebraicGeometry

/-- Lie spaces of represented centralizers and normalizers are whole-group invariants.
Source: Milne, Algebraic Groups (2017), Proposition 10.34, printed pp.197--198;
Sections 10a--10d for the tangent functor and adjoint action
(blueprint: lem-sfb-lie-normalizer-centralizer-invariants).

Proof, following the five steps of the DAG node:
1. Apply lem-sfb-affine-group-dual-number-calculus simultaneously to the five groups
and their inclusions. It gives finite dimension, injective differentials, and the
rational conjugation action. Equivariance for H proves stability of h. Extend a basis
of h to one of g: the quotient diagonal block gives the rational quotient action Q,
and the same splitting identifies the kernel after any scalar extension with R tensor h.
2. A tangent point E(v) in C commutes with every K-point after all dual-number algebra
extensions. Over R[delta] this says Ad(k)(v_R)=v_R by conjugation and injectivity of E.
Conversely, test invariance over every dual-number algebra S, then specialize
S[delta] to S by delta mapping to the image of epsilon. Naturality proves E(v) is in C.
This gives the centralizer equality, with no reducedness assumption on the test ring.
3. H normalizes itself, hence h is contained in Lie(N). For v in Lie(N) and h in H(R),
the commutator E(v_R) h E(-v_R) h inverse lies in H(R[delta]) and reduces to one.
The calculus identifies it with E(v_R-Ad(h)v_R). The subgroup-kernel identification
and the split quotient kernel say precisely that the class of v is fixed.
4. Conversely a fixed class gives v_R-Ad(h)v_R in R tensor h. The same commutator
therefore lies in H(R[delta]). For every dual-number algebra S, specialize delta to
epsilon_S. This gives x H(S) x inverse contained in H(S), where x is E(v) specialized.
Repeat for -v to obtain the reverse containment. Thus E(v) lies in N, as required.
5. The quotient map is surjective with kernel h, contained in Lie(N). Its restriction
induces an injection Lie(N)/h into g/h. Steps 3 and 4 identify its image with all
Q-fixed classes; step 2 gives the other equality. No Lie-algebra invariants,
characteristic restriction, or smoothness of C or N is used. -/
theorem lie_normalizer_centralizer_invariants
    (F : Type u) [Field F] [IsAlgClosed F]
    (G K H C N : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsAffine K.X.left] [LocallyOfFiniteType K.X.hom] [QuasiCompact K.X.hom]
    [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [IsAffine C.X.left] [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [Smooth H.X.hom]
    (iK : K.X ⟶ G.X) (iH : H.X ⟶ G.X) (iC : C.X ⟶ G.X) (iN : N.X ⟶ G.X)
    [IsClosedSubgroupScheme iK] [IsClosedSubgroupScheme iH]
    [IsClosedSubgroupScheme iC] [IsClosedSubgroupScheme iN]
    (hC : ∀ (A : Type u) [CommRing A] [Algebra F A],
      Set.range (fun c : points C.X A ↦ c ≫ iC) =
        {g : points G.X A | ∀ (B : Type u) [CommRing B] [Algebra F B]
          (f : A →ₐ[F] B) (k : points K.X B),
          points.map G.X f g * (k ≫ iK) = (k ≫ iK) * points.map G.X f g})
    (hN : ∀ (A : Type u) [CommRing A] [Algebra F A],
      Set.range (fun n : points N.X A ↦ n ≫ iN) =
        {g : points G.X A | ∀ (B : Type u) [CommRing B] [Algebra F B]
          (f : A →ₐ[F] B),
          (fun h : points G.X B ↦ points.map G.X f g * h * (points.map G.X f g)⁻¹) ''
              Set.range (fun h : points H.X B ↦ h ≫ iH) =
            Set.range (fun h : points H.X B ↦ h ≫ iH)}) :
    ∃ D : AffineGroupDualNumberCalculus.Data G,
      Module.Finite F (GrpObj.Lie K.X) ∧ Module.Finite F (GrpObj.Lie H.X) ∧
      Module.Finite F (GrpObj.Lie C.X) ∧ Module.Finite F (GrpObj.Lie N.X) ∧
      Function.Injective (GrpObj.differential iK) ∧
      Function.Injective (GrpObj.differential iH) ∧
      Function.Injective (GrpObj.differential iC) ∧
      Function.Injective (GrpObj.differential iN) ∧
      (∀ (R : Type u) [CommRing R] [Algebra F R] (h : points H.X R)
          (v : R ⊗[F] GrpObj.Lie H.X),
        (D.Ad R (h ≫ iH)).toLinearEquiv
            (LinearMap.baseChange R (GrpObj.differential iH).toLinearMap v) ∈
          LinearMap.range (LinearMap.baseChange R (GrpObj.differential iH).toLinearMap)) ∧
      ∃ Q : ∀ (R : Type u) [CommRing R] [Algebra F R],
          points H.X R →* LinearMap.GeneralLinearGroup R
            (R ⊗[F] (GrpObj.Lie G.X ⧸ LinearMap.range (GrpObj.differential iH).toLinearMap)),
        (∀ (R : Type u) [CommRing R] [Algebra F R] (h : points H.X R)
            (v : R ⊗[F] GrpObj.Lie G.X),
          (Q R h).toLinearEquiv
              (LinearMap.baseChange R
                (LinearMap.range (GrpObj.differential iH).toLinearMap).mkQ v) =
            LinearMap.baseChange R (LinearMap.range (GrpObj.differential iH).toLinearMap).mkQ
              ((D.Ad R (h ≫ iH)).toLinearEquiv v)) ∧
        (∀ (n : ℕ) (b : Module.Basis (ULift.{u} (Fin n)) F
            (GrpObj.Lie G.X ⧸ LinearMap.range (GrpObj.differential iH).toLinearMap)),
          ∃! ρ : H.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) F, IsMonHom ρ ∧
            ∀ (R : Type u) [CommRing R] [Algebra F R] (h : points H.X R),
              Q R h = Matrix.GeneralLinearGroup.toLin' (b.baseChange R)
                (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) F R (h ≫ ρ))) ∧
        LinearMap.range (GrpObj.differential iH).toLinearMap ≤
          LinearMap.range (GrpObj.differential iN).toLinearMap ∧
        (Set.range (GrpObj.differential iC) =
          {v : GrpObj.Lie G.X | ∀ (R : Type u) [CommRing R] [Algebra F R]
            (k : points K.X R), (D.Ad R (k ≫ iK)).toLinearEquiv (1 ⊗ₜ[F] v) =
              1 ⊗ₜ[F] v}) ∧
        (Set.range ((LinearMap.range (GrpObj.differential iH).toLinearMap).mkQ.comp
            (GrpObj.differential iN).toLinearMap) =
          {z | ∀ (R : Type u) [CommRing R] [Algebra F R] (h : points H.X R),
            (Q R h).toLinearEquiv (1 ⊗ₜ[F] z) = 1 ⊗ₜ[F] z}) := by
  sorry

end AlgebraicGeometry
