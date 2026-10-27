module

public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Fixed vectors in rational representations of smooth unipotent groups

Source: Milne, Algebraic Groups (2017), Proposition 14.3, p.280, Corollary 14.12,
p.283, and Lemma 19.16, p.401. The proof uses Section 9.19, p.171, and
Proposition 14.1, pp.279-280.
(blueprint: lem-sfb-unipotent-rational-representation-fixed-vector)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every positive-dimensional rational representation of the stated smooth affine
unipotent group has a nonzero vector fixed by all its K-points.
Source: Milne, Algebraic Groups (2017), Proposition 14.3 and Section 14.b, p.280;
Corollary 14.12, p.283; applied in Lemma 19.16, p.401.
(blueprint: lem-sfb-unipotent-rational-representation-fixed-vector)

Proof plan:
1. For each point x, apply lem-sfb-rational-representation-unipotent-point to i and rho.
   The faithful representation, affine finite-type group and algebraically closed field
   are exactly its hypotheses. Thus rho(x)-I is nilpotent, with exponent depending on x.
2. The image H of U(K) in GL_d(K) is a subgroup: the group-of-points construction and
   homMulEquiv preserve identity, multiplication and inverse. Every element of H is
   unipotent by step 1 (def-sc-group-scheme and def-sc-general-linear-group).
3. Apply lem-sfb-unipotent-matrix-group-fixed-vector to H and the positive dimension d.
   Its common nonzero fixed vector is fixed by rho(x) for every x in U(K).

The indices ULift (Fin m) and ULift (Fin d) retain exactly m and d coordinates while
matching the universe of the existing general linear group scheme. Matrix.mulVec is
ordinary multiplication on column vectors. Faithfulness is tested on all K-algebras,
including nonreduced ones, rather than only on K-points. -/
theorem exists_nonzero_fixedVector_of_faithful_unipotent
    (K : Type u) [Field K] [IsAlgClosed K]
    (U : Over (Spec (.of K))) [GrpObj U]
    [IsAffine U.left] [Smooth U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (m : ℕ) (_hm : 1 ≤ m)
    (i : U ⟶ GeneralLinearGroup (ULift.{u} (Fin m)) K) [IsMonHom i]
    (_hfaithful : ∀ (R : Type u) [CommRing R] [Algebra K R],
      Function.Injective
        (fun x : (Spec (.of R)).asOver (Spec (.of K)) ⟶ U ↦ x ≫ i))
    (_hunipotent : ∀ x : (Spec (.of K)).asOver (Spec (.of K)) ⟶ U,
      ∃ N : ℕ, 1 ≤ N ∧
        ((GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin m)) K K (x ≫ i)).val - 1) ^ N = 0)
    (d : ℕ) (_hd : 1 ≤ d)
    (ρ : U ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) K) [IsMonHom ρ] :
    ∃ v : ULift.{u} (Fin d) → K, v ≠ 0 ∧
      ∀ x : (Spec (.of K)).asOver (Spec (.of K)) ⟶ U,
        Matrix.mulVec
          (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) K K (x ≫ ρ)).val v = v := by
  sorry

end AlgebraicGeometry
