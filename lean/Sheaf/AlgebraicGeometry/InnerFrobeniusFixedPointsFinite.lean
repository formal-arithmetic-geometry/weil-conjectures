module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.FieldTheory.UniqueSubfieldOfClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Finiteness of the fixed points of an inner twist of Frobenius

Source: Milne, Algebraic Groups (2017), Theorem 17.96, proof, printed pp.382–383
(blueprint: lem-sfb-inner-frobenius-fixed-points-finite).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Inner twists of arithmetic Frobenius have finitely many geometric fixed points on
an affine finite-type group scheme over a finite field. No smoothness, connectedness,
reducedness or commutativity is required.

Here `points A Ω` is the group of morphisms `Spec Ω ⟶ A` over `Spec k`. For affine `A`,
`A.hom.overHomEquivAlgHom Ω` identifies these with the `k`-algebra homomorphisms
`Γ(A.left, ⊤) →ₐ[k] Ω`, using the algebra structure `A.hom.ΓAlgebra`. The map
`points.map A (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom` postcomposes
such a homomorphism with `z ↦ z ^ Fintype.card k`, exactly the specified arithmetic Frobenius.

Source: Milne, Algebraic Groups (2017), Theorem 17.96, proof, printed pp.382–383
(blueprint: lem-sfb-inner-frobenius-fixed-points-finite).

Proof plan:
1. By lem-pc-affine-finite-type-algebra, the coordinate algebra is finitely generated.
   Evaluation on a finite generating family is injective, even for an empty family
   (def-weil-pbc-finite-type-algebra).
2. The coordinates of x generate a finite extension L of k by
   lem-weil-pbc-algebraic-generators-finite-extension. A finite basis over the finite
   field makes L finite, and every coordinate value of x lies in L.
3. The arithmetic Frobenius permutes L, so some positive power σ^m fixes x.
   Functoriality of group-scheme points makes σ a group automorphism, with
   σ^n(u)(c) = u(c)^(q^n) (def-weil-frobenius-substitution, def-sc-group-scheme).
4. For n positive, the subgroup H_n of σ^n-fixed points is finite: evaluation embeds it
   into a finite power of the q^n-element subfield of Ω from
   lem-weil-unique-subfield-of-closure.
5. Put f(u) = xσ(u)x⁻¹ and y_n = xσ(x)⋯σ^(n-1)(x). Induction gives
   f^n(u) = y_n σ^n(u) y_n⁻¹. As σ^m fixes x, y = y_m belongs to H_m.
6. The finite group H_m gives y finite order r > 0. Since σ^m(y) = y, induction gives
   (f^m)^j(u) = y^j σ^(mj)(u) y^(-j), and hence f^(mr) = σ^(mr).
7. Every f-fixed point is σ^(mr)-fixed, hence lies in the finite set H_(mr).
   This uses only finite affine generators and the group laws. -/
theorem inner_frobenius_fixedPoints_finite
    (k : Type u) [Field k] [Fintype k]
    (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAffine A.left]
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] (x : points A Ω) :
    Set.Finite {v : points A Ω |
      x * points.map A (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom v * x⁻¹ = v} := by
  sorry

end AlgebraicGeometry
