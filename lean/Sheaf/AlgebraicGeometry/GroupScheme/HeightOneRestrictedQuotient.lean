module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Topology.KrullDimension

import Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-! # Height-one quotients from restricted tangent subalgebras

Source: Milne, Algebraic Groups (2017), Propositions 11.35--11.37 and Corollary 11.38,
pp.222--223; Proposition 17.80, p.378
(blueprint: lem-sfb-height-one-restricted-quotient).

The Lie algebra is the canonical tangent Lie algebra. Its fixed faithful differential
embeds it in matrices. Restricted closure is matrix pth-power closure, and the adjoint
conditions are conjugation on the scalar-extended matrix subspace over every test algebra.
The pth-power description agrees with composition of invariant derivations, by rational
restricted differentiation (Milne 10.39 and 11.36). No arbitrary restricted operation or
adjoint representation is supplied as an extra hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped Matrix MonObj

namespace AlgebraicGeometry

/-- The scalar extension of a tangent subalgebra in its fixed faithful matrix representation.
This is the R-linear span of the coefficientwise images of its matrices, equivalently the
image of R tensor h. It uses the recorded differential, not a separately chosen Lie map.
Source: Milne, Corollary 11.38, p.223, and the matrix realization in 10.39
(blueprint: lem-sfb-height-one-restricted-quotient). -/
def restrictedTangentMatrixSpan {k : Type u} [Field k]
    {J : Grp (Over (Spec (.of k)))} {n : Type u} [Fintype n] [DecidableEq n]
    (ρ : GeneralLinearGroup.RationalHom J.X n) [IsMonHom ρ]
    (h : LieSubalgebra k (GrpObj.Lie J.X))
    (R : Type u) [CommRing R] [Algebra k R] : Submodule R (Matrix n n R) :=
  Submodule.span R {M | ∃ x : h, M = (ρ.differential x.val).map (algebraMap k R)}

/-- An invariant restricted tangent subalgebra integrates to a normal height-one subgroup
and a finite faithfully flat radicial quotient, with the given Lie kernel and dimension.
The trivial adjoint toral case gives a central kernel of multiplicative type.
Source: Milne, Propositions 11.35--11.37 and Corollary 11.38, pp.222--223;
Proposition 17.80, p.378 (blueprint: lem-sfb-height-one-restricted-quotient).

Proof:
1. Restricted rational differentiation identifies invariant derivations with the canonical
   tangent Lie algebra, preserving commutators, pth powers and the differential of ρ.
   Its finite dimension follows from finite generation of the coordinate algebra.
2. Apply height-one integration to h and its inclusion in Lie(J). This gives a finite
   closed subgroup H with differential image h, local coordinate algebra, and augmentation
   elements killed by pth powers. A basis of the augmentation ideal shows that its power
   above dim(I)*(p-1) vanishes; hence this ideal is nilpotent.
3. For every test algebra R and g in J(R), adjoint stability restricts conjugation to a
   restricted automorphism of R tensor h. Relative integration and its uniqueness produce
   an automorphism of H_R whose inclusion intertwines conjugation. Thus H is normal as a
   group scheme, including over nonreduced test algebras.
4. The affine normal quotient theorem gives the affine finite-type quotient Q=J/H, its
   fppf quotient presentation and smoothness. Surjectivity implies connectedness of Q.
   The torsor identifies the base change of q along itself with J times H -> J, finite
   because k[H] is finite dimensional. Fpqc finiteness descent makes q finite faithfully flat.
5. Every geometric point of H kills its augmentation ideal, so H has only its identity
   geometric point. Equality of images under q then implies equality of geometric points,
   proving radiciality. On dual numbers the kernel of dq is exactly Lie(H)=h.
   Finite-surjective dimension invariance gives dim Q=dim J.
6. If the adjoint action on h is trivial over every test algebra, relative integration
   uniqueness makes conjugation on H trivial. Hence H(R) commutes with J(R) for every R.
7. Over the algebraic closure the matrices in h commute, since differentiation of the
   trivial adjoint action gives zero brackets. Their assumed diagonalizability and the
   joint-generalized-eigenspace spanning theorem give a simultaneous eigenbasis.
8. Integrate h into the diagonal torus in this basis. Uniqueness identifies its composite
   into GL with H -> J -> GL. This composite is a closed immersion, hence so is the map
   to the torus (the coordinate surjection factors through its coordinate algebra).
   Thus H is of multiplicative type. The empty basis and h=0 cause no exception:
   integration of zero is the trivial group, and Q=J, q=id is allowed.
-/
theorem exists_heightOne_restricted_quotient
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (J : Grp (Over (Spec (.of k))))
    [IsAffine J.X.left] [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    [Smooth J.X.hom] [ConnectedSpace J.X.left]
    (n : Type u) [Fintype n] [DecidableEq n]
    (ρ : GeneralLinearGroup.RationalHom J.X n) [IsClosedSubgroupScheme ρ]
    (h : LieSubalgebra k (GrpObj.Lie J.X))
    (hp : ∀ x : h, ∃ y : h, ρ.differential y.val = ρ.differential x.val ^ p)
    (hAd : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : points J.X R)
      (X : restrictedTangentMatrixSpan ρ h R),
      (ρ.points R g).val * X.val * ((ρ.points R g)⁻¹).val ∈
        restrictedTangentMatrixSpan ρ h R) :
    ∃ (H Q : Grp (Over (Spec (.of k)))) (i : H ⟶ J) (q : J ⟶ Q),
      IsClosedSubgroupScheme i.hom.hom ∧ IsNormalSubgroupScheme i.hom.hom ∧
      IsFinite H.X.hom ∧
      IsLocalRing Γ(H.X.left, ⊤) ∧
      IsNilpotent (RingHom.ker (GrpObj.unitSection H.X).appTop.hom) ∧
      (∀ a ∈ RingHom.ker (GrpObj.unitSection H.X).appTop.hom, a ^ p = 0) ∧
      (GrpObj.differential i.hom.hom).range = h ∧
      IsAffine Q.X.left ∧ LocallyOfFiniteType Q.X.hom ∧ QuasiCompact Q.X.hom ∧
      Smooth Q.X.hom ∧ ConnectedSpace Q.X.left ∧
      IsFppfGroupQuotient i q ∧ IsFinite q.hom.hom.left ∧
      q.hom.hom.left.appTop.hom.FaithfullyFlat ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω],
        Function.Injective (fun x : points J.X Ω ↦ x ≫ q.hom.hom)) ∧
      ((GrpObj.differential q.hom.hom).ker : LieSubalgebra k (GrpObj.Lie J.X)) = h ∧
      topologicalKrullDim Q.X.left = topologicalKrullDim J.X.left ∧
      ((∀ (R : Type u) [CommRing R] [Algebra k R] (g : points J.X R)
          (X : restrictedTangentMatrixSpan ρ h R),
          (ρ.points R g).val * X.val * ((ρ.points R g)⁻¹).val = X.val) →
        (∀ X : restrictedTangentMatrixSpan ρ h (AlgebraicClosure k),
          ∃ (b : GL n (AlgebraicClosure k)) (d : n → AlgebraicClosure k),
            b.val * X.val * (b⁻¹).val = Matrix.diagonal d) →
        (∀ (R : Type u) [CommRing R] [Algebra k R]
          (a : points H.X R) (b : points J.X R),
          (a ≫ i.hom.hom) * b = b * (a ≫ i.hom.hom)) ∧
        MultiplicativeType.IsMultiplicativeType H) := by
  sorry

end AlgebraicGeometry
