/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Semisimple
import Sheaf.AlgebraicGeometry.AffineGroupTensorReconstruction

/-! # Additive Jordan decomposition in algebraic group Lie algebras

Source: Milne, Algebraic Groups (2017), Proposition 17.74, printed p.377,
with geometric faithful detection by extension to an algebraic closure
(blueprint: lem-sfb-algebraic-lie-additive-jordan).

The Lie algebra is the canonical tangent Lie algebra `GrpObj.Lie`, identified with
`schemeTangentSpace` by `GrpObj.lieIdentityTangentEquiv`. Only differentials of
homomorphisms of group schemes are tested. Geometric semisimplicity is semisimplicity
of the matrix endomorphism over the fixed algebraic closure, hence diagonalizability.
Scalar extension is specified on dual-number points by the actual pullback projection;
no choice of a comparison map is part of the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A pair of tangent Lie elements is the additive Jordan pair of `Y` if it sums to `Y`,
commutes, and has geometrically semisimple and nilpotent images in every positive-dimensional
rational representation. Over the algebraically closed field `Ω`, semisimplicity of a
finite-dimensional endomorphism is equivalent to diagonalizability.
Source: Milne, Proposition 17.74(a), printed p.377
(blueprint: lem-sfb-algebraic-lie-additive-jordan). -/
def IsAlgebraicLieJordanPair {k : Type u} [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (H : Over (Spec (.of k))) [GrpObj H] (Y Ys Yn : GrpObj.Lie H) : Prop :=
  Y = Ys + Yn ∧ ⁅Ys, Yn⁆ = 0 ∧
    ∀ (n : ℕ), 0 < n → ∀ (r : GeneralLinearGroup.RationalHom H
      (LinearGroupSchemes.Index.{u} n)) [IsMonHom r],
      Module.End.IsSemisimple (Matrix.toLin' ((r.differential Ys).map (algebraMap k Ω))) ∧
        IsNilpotent (r.differential Yn)

/-- Over a perfect field every tangent Lie element has a unique additive Jordan pair,
characterized simultaneously by all algebraic rational representations.
Source: Milne, Proposition 17.74(a), printed p.377
(blueprint: lem-sfb-algebraic-lie-additive-jordan).

Proof:
1. Choose a closed faithful representation by
   lem-sfb-affine-group-faithful-linear-representation. Its differential is injective:
   equality of images of dual-number tangent points implies equality of those points.
   Use lem-sfb-affine-group-lie-tangent-calculus to identify its differential with matrices.
2. Apply lem-sfb-additive-jordan-linear-compatibility to dr(Y) for every representation.
   Equivariant maps intertwine the resulting parts, by the coefficient of epsilon in
   equivariance. On tensor products the differential is A tensor 1 + 1 tensor B,
   so its parts satisfy the tensor-sum identities; on the trivial representation both vanish.
3. The families 1 + epsilon S and 1 + epsilon N are tensor-compatible natural families
   over the dual numbers. Apply lem-sfb-affine-group-tensor-reconstruction to obtain
   two group points. Their reductions are the identity by the faithful representation,
   so they are tangent vectors Ys and Yn with the required differentials.
4. Linearity and bracket compatibility give di(Ys+Yn)=di(Y) and di([Ys,Yn])=0.
   Injectivity gives the sum and commutation assertions. Matrix uniqueness followed by
   the same injectivity gives uniqueness of the ordered pair. No smoothness is used. -/
theorem existsUnique_algebraicLieJordanPair {k : Type u} [Field k] [PerfectField k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (H : Over (Spec (.of k))) [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] (Y : GrpObj.Lie H) :
    ∃! p : GrpObj.Lie H × GrpObj.Lie H, IsAlgebraicLieJordanPair Ω H Y p.1 p.2 := by
  sorry

/-- Differentials of algebraic group homomorphisms preserve the additive Jordan pair.
Source: Milne, Proposition 17.74(b), printed p.377
(blueprint: lem-sfb-algebraic-lie-additive-jordan).

Proof: compose each rational representation of H' with f and use the chain rule in
lem-sfb-affine-group-lie-tangent-calculus. The representation clause of the Jordan pair
for H gives the required semisimple and nilpotent images for H'. Linearity and bracket
preservation give the sum and commutation clauses. Existence and uniqueness above identify
these images with the unique parts of df(Y); equivalently use a faithful representation
of H' from lem-sfb-affine-group-faithful-linear-representation and matrix uniqueness. -/
theorem algebraicLieJordanPair_differential {k : Type u} [Field k] [PerfectField k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {H H' : Over (Spec (.of k))} [GrpObj H] [GrpObj H']
    [IsAffine H.left] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [IsAffine H'.left] [LocallyOfFiniteType H'.hom] [QuasiCompact H'.hom]
    (f : H ⟶ H') [IsMonHom f] (Y Ys Yn : GrpObj.Lie H)
    (h : IsAlgebraicLieJordanPair Ω H Y Ys Yn) :
    IsAlgebraicLieJordanPair Ω H' (GrpObj.differential f Y)
      (GrpObj.differential f Ys) (GrpObj.differential f Yn) := by
  sorry

/-- Scalar extension of a tangent vector, expressed by its canonical dual-number point:
the point of the actual pullback projects to the old point precomposed with
Spec(k[epsilon] -> K[epsilon]). This specifies the image of 1 tensor Y uniquely.
Source: Milne, 10.19, printed p.192, and the scalar-extension step for Proposition 17.74
(blueprint: lem-sfb-algebraic-lie-additive-jordan). -/
def IsLieScalarExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
    (H : Over (Spec (.of k))) [GrpObj H]
    (Y : GrpObj.Lie H)
    (YK : GrpObj.Lie
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
        (Grp.mk H)).X)) : Prop :=
  (GrpObj.tangentPoint YK).left ≫
      pullback.fst H.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
    Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (algebraMap k K))) ≫
      (GrpObj.tangentPoint Y).left

/-- Extension between perfect fields preserves the additive Jordan pair. The three scalar
extension hypotheses specify the canonical extensions of Y, Ys and Yn, without requiring
representations over K to descend to k. The closure over K is independently chosen.
Source: Milne, preliminaries on printed p.376, Proposition 17.74 and 10.19, printed p.192
(blueprint: lem-sfb-algebraic-lie-additive-jordan).

Proof: extend a closed faithful representation from
lem-sfb-affine-group-faithful-linear-representation to K. By
lem-sfb-affine-group-lie-tangent-calculus the matrices of the extended tangent vectors
are obtained by entrywise scalar extension. By lem-sfb-additive-jordan-linear-compatibility
the extended matrices are the unique matrix parts. Construct the pair over K by the
existence assertion above and use injectivity of the extended faithful differential to
identify its parts with the extensions of Ys and Yn. This proves the representation
property for every representation over K, including those that do not descend. -/
theorem algebraicLieJordanPair_scalarExtension {k K : Type u}
    [Field k] [PerfectField k] [Field K] [PerfectField K] [Algebra k K]
    (Ω ΩK : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [Field ΩK] [Algebra K ΩK] [IsAlgClosure K ΩK]
    (H : Over (Spec (.of k))) [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (Y Ys Yn : GrpObj.Lie H)
    (YK YsK YnK : GrpObj.Lie
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
        (Grp.mk H)).X))
    (h : IsAlgebraicLieJordanPair Ω H Y Ys Yn)
    (hY : IsLieScalarExtension H Y YK) (hs : IsLieScalarExtension H Ys YsK)
    (hn : IsLieScalarExtension H Yn YnK) :
    IsAlgebraicLieJordanPair ΩK
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapGrp.obj
        (Grp.mk H)).X) YK YsK YnK := by
  sorry

/-- A closed faithful representation has injective differential and detects geometric
semisimplicity and nilpotence in every algebraic rational representation, over any field.
Source: Milne, Proposition 17.74 over an algebraic closure, printed p.377, and 10.14,
printed p.190 (blueprint: lem-sfb-algebraic-lie-additive-jordan).

Proof:
1. A closed immersion is injective on algebra-valued points, hence on dual-number
   tangent points; use lem-sfb-affine-group-lie-tangent-calculus to conclude injectivity.
   This remains true after extension to the algebraic closure, without smoothness.
2. Over that perfect closure construct the unique Jordan pair. If di(Y) is geometrically
   semisimple its nilpotent matrix part is zero. Injectivity makes Yn zero. If di(Y) is
   nilpotent its semisimple matrix part is zero, so injectivity makes Ys zero. These use
   matrix uniqueness from lem-sfb-additive-jordan-linear-compatibility.
3. Apply the representation clause over the closure and the scalar-extension matrix
   formula of lem-sfb-affine-group-lie-tangent-calculus. In the first case dr(Y) becomes
   diagonalizable. In the second some positive power vanishes after extension; injectivity
   of k -> its closure descends the entrywise vanishing of that power. -/
theorem algebraicLie_faithful_differential_detection {k : Type u} [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (H : Over (Spec (.of k))) [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (m : ℕ) (hm : 0 < m)
    (i : GeneralLinearGroup.RationalHom H (LinearGroupSchemes.Index.{u} m))
    [IsMonHom i] [IsClosedImmersion i.left] :
    Function.Injective i.differential ∧
      ∀ (Y : GrpObj.Lie H) (n : ℕ), 0 < n →
        ∀ (r : GeneralLinearGroup.RationalHom H (LinearGroupSchemes.Index.{u} n))
          [IsMonHom r],
          (Module.End.IsSemisimple (Matrix.toLin' ((i.differential Y).map (algebraMap k Ω))) →
            Module.End.IsSemisimple (Matrix.toLin' ((r.differential Y).map (algebraMap k Ω)))) ∧
          (IsNilpotent (i.differential Y) → IsNilpotent (r.differential Y)) := by
  sorry

end AlgebraicGeometry
