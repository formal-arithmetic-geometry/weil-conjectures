module
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
@[expose] public section
set_option autoImplicit false
universe u v w
open scoped TensorProduct
namespace Algebra.TensorProduct
/-- Locality, residue, and closed-fibre properties of purely inseparable tensor base change.
Source: Stacks Project, More on Algebra, proof of Proposition Tag 07E5, (3) => (1),
where locality and finite flatness are used without proof; expanded argument below.
(blueprint: lem-weil-pbc-purely-inseparable-base-change-residue)

Proof: Write m for the maximal ideal of A, K = A/m, and d = [k':k]. A k-basis of k'
extends to a finite A-basis of A' = A tensor k', so A' is finite over A. The tensor
quotient isomorphism, the swap, and cancellation of base change identify C = A'/mA'
with B = K tensor k'; on pure tensors the map is [a tensor x] to residue(a) tensor x.
A scalar-extended k-basis of k' is a K-basis of B of size d. Transporting that basis
through the isomorphism, with precisely the K-action induced by its inverse as in the
statement, proves the displayed finrank equality. Since k' is a nonzero field, d is
positive, and this basis also shows B is nonzero.

Every z in B has a positive power in the image of K, by
`IsPurelyInseparable.exists_pow_mem_range_tensorProduct`. If that scalar is zero then
z is nilpotent; otherwise that power, hence z, is a unit. Thus the nilradical N of B
is proper and every element outside it is a unit. Every proper ideal lies in N, so
N is maximal. Every prime contains all nilpotents, hence N is the only prime of B.
Pull N back along A' to C to B to obtain m'. Its quotient is B/N, a field, and prime
correspondence shows m' is the only prime containing mA'. Every maximal ideal of A'
contracts to a maximal ideal of A, since the finite algebra A' is integral over A.
That contraction is m, so every maximal ideal contains mA' and equals m'. Thus A'
is local. The map A to A'/m' kills m and descends to the required ring map f from K;
its formula on residue classes gives the stated compatibility. Finally C surjects
onto A'/m' because mA' is contained in m'. This map is K-linear for f, so images
of the d basis vectors span A'/m' over K, proving its finiteness. -/
theorem purelyInseparable_baseChange_residue
    (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [IsPurelyInseparable k k'] [Module.Finite k k']
    [IsLocalRing A] [IsNoetherianRing A] :
    IsLocalRing (A ⊗[k] k') ∧
      (∃ m' : Ideal (A ⊗[k] k'),
        m'.IsMaximal ∧
        (∀ P : Ideal (A ⊗[k] k'), P.IsPrime →
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A) ≤ P ↔ P = m')) ∧
        (∃ f : IsLocalRing.ResidueField A →+* ((A ⊗[k] k') ⧸ m'),
          (∀ a : A, f (IsLocalRing.residue A a) =
            Ideal.Quotient.mk m' (algebraMap A (A ⊗[k] k') a)) ∧
          @Module.Finite (IsLocalRing.ResidueField A) ((A ⊗[k] k') ⧸ m')
            _ _ (@Algebra.toModule _ _ _ _ f.toAlgebra))) ∧
      (∃ e : ((A ⊗[k] k') ⧸
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))) ≃+*
          ((IsLocalRing.ResidueField A) ⊗[k] k'),
        (∀ (a : A) (x : k'), e (Ideal.Quotient.mk
          (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A))
          (a ⊗ₜ[k] x)) = (IsLocalRing.residue A a) ⊗ₜ[k] x) ∧
        @Module.finrank (IsLocalRing.ResidueField A)
          ((A ⊗[k] k') ⧸
            (Ideal.map (algebraMap A (A ⊗[k] k')) (IsLocalRing.maximalIdeal A)))
          _ _ (@Algebra.toModule _ _ _ _
            (e.symm.toRingHom.comp (algebraMap (IsLocalRing.ResidueField A)
              ((IsLocalRing.ResidueField A) ⊗[k] k'))).toAlgebra) =
            Module.finrank k k') := by
  sorry
end Algebra.TensorProduct
