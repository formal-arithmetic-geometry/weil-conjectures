/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.TorusCharacterTangentWeights
import WeilConjectures.AlgebraicGeometry.TorusPositiveRaySubgroup

/-! # Root subgroups and their parametrizations

Source: Milne, Algebraic Groups (2017), Theorem 21.11(b),(c),(e), pp.428--430,
and paragraph 21.19, formula (135), p.431
(blueprint: lem-sfb-reductive-root-subgroup-parametrizations).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.TorusCharacterTangent

/-- The point of the recorded additive group with coordinate a, given by polynomial
substitution. This helper spells out the parameter in Milne's formula (135), p.431
(blueprint: lem-sfb-reductive-root-subgroup-parametrizations). -/
def additiveParameterPoint (F : Type u) [Field F]
    {A : Type u} [CommRing A] [Algebra F A] (a : A) :
    StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.additive F :=
  StandardGroupSchemes.map F (Polynomial.aeval a)

/-- Evaluate the Laurent coordinate at an A-point of the recorded multiplicative
group. Its value is the scalar in Milne's formula (135), p.431
(blueprint: lem-sfb-reductive-root-subgroup-parametrizations). -/
def multiplicativePointCoordinate (F : Type u) [Field F]
    {A : Type u} [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F) : A :=
  (Scheme.ΓSpecIso (.of A)).hom
    (s.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
      (LaurentPolynomial.T 1)))

/-- Every nontrivial adjoint character weight integrates to a unique smooth connected
closed normalized subgroup, isomorphic to the additive group. Every parametrization
has the root-character conjugation formula, and a coroot has pairing two.

The internal action is explicitly identified with conjugation by the inclusion i;
thus weightSpace uses torus characters, including in positive characteristic.
Uniqueness is equality of subgroup schemes, expressed by an isomorphism over G.
Source: Milne, Theorem 21.11(b),(c),(e), pp.428--430, and 21.19, formula (135), p.431
(blueprint: lem-sfb-reductive-root-subgroup-parametrizations).

Proof:
1. Apply lem-sfb-reductive-rank-one-reflections to (G,T). It gives dimension one
   of the alpha weight space and that the only rational multiples of alpha among
   roots are alpha and -alpha. The positive-ray tangent space is therefore g_alpha.
2. Apply lem-sfb-torus-positive-ray-subgroup to the conjugation action. Its two
   tangent-inclusion implications identify any other smooth connected normalized
   closed subgroup with this tangent space with U. The group U is unipotent and
   has tangent dimension one; lem-sfb-one-dimensional-unipotent-additive gives Ga ≅ U.
3. For any isomorphism u, transport conjugation to Ga. At the universal T-point,
   the action is a polynomial automorphism P over the Laurent domain F[T], fixing
   zero. A polynomial inverse Q gives deg(P)deg(Q)=1, so P(X)=cX for a unit c.
   Its tangent multiplier is c, which the weight condition identifies with alpha.
   Specializing this identity along F[T] → A gives the formula for every A,
   including nonreduced algebras.
4. The coroot from lem-sfb-reductive-rank-one-reflections has pairing two, giving
   alpha(alphaCoroot(s))=s² on every test algebra. If there are no roots the
   root-indexed assertion is vacuous. -/
theorem reductive_root_subgroup_parametrizations
    (F : Type u) [Field F] [IsAlgClosed F]
    (G T : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (i : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (r : ℕ) (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    [ModObj T.X G.X]
    (hconj : γ[T.X,G.X] =
      (fst T.X G.X ≫ i.hom.hom) * snd T.X G.X * (fst T.X G.X ≫ i.hom.hom)⁻¹)
    (α : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))
    (hα : α.hom.hom ≠ 1) (hweight : weightSpace T G α ≠ ⊥) :
    ∃ (U : Grp (Over (Spec (.of F)))) (j : U ⟶ G),
      IsClosedSubgroupScheme j.hom.hom ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsStable T G j ∧ (GrpObj.differential j.hom.hom).toLinearMap.range = weightSpace T G α ∧
      Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ U) ∧
      (∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ G),
        IsClosedSubgroupScheme k.hom.hom → Smooth K.X.hom → ConnectedSpace K.X.left →
        IsStable T G k →
        (GrpObj.differential k.hom.hom).toLinearMap.range = weightSpace T G α →
          ∃ e : K ≅ U, e.hom ≫ j = k) ∧
      (∀ (v : Grp.mk (StandardGroupSchemes.additive F) ≅ U)
        (A : Type u) [CommRing A] [Algebra F A]
        (t : StandardGroupSchemes.affine F A ⟶ T.X) (a : A),
        (t ≫ i.hom.hom) * (additiveParameterPoint F a ≫ v.hom.hom.hom ≫ j.hom.hom) *
            (t ≫ i.hom.hom)⁻¹ =
          additiveParameterPoint F (multiplicativePointCoordinate F (t ≫ α.hom.hom) * a) ≫
            v.hom.hom.hom ≫ j.hom.hom) ∧
      (∃ αcoroot : Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T,
        ∀ (A : Type u) [CommRing A] [Algebra F A]
          (s : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F),
          s ≫ αcoroot.hom.hom ≫ α.hom.hom = s ^ 2) := by
  sorry

end AlgebraicGeometry.TorusCharacterTangent
