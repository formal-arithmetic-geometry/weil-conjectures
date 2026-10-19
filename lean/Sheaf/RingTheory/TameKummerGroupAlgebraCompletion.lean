/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Algebra.Pi
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProductPrincipalOpen
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Tame finite-index group algebra base change

Source: ILO, Travaux de Gabber, VI 2.2, printed p.72; Stacks Tags 0325 and 02G8
(blueprint: lem-per-tame-kummer-group-algebra-completion).

The abelian groups are written multiplicatively. The helpers supply the canonical
character base change, with its actual tensor-product ring and coefficient algebra.
-/

@[expose] public section

universe u v w

namespace MonoidAlgebra

/-- The character base change `E ⊗[ℤ[L]] ℤ[M]`, using the inclusion `f` and character `ρ`.
Its data are the ordinary Mathlib algebra tensor product, with `[l] ↦ ρ(l)` on `E`.
Source: ILO VI 2.2, printed p.72
(blueprint: lem-per-tame-kummer-group-algebra-completion). -/
def characterBaseChange (E : Type u) (L : Type v) (M : Type w)
    [CommRing E] [CommGroup L] [CommGroup M] (f : L →* M) (ρ : L →* Eˣ) :
    Type (max u w) :=
  letI := (lift ℤ E L ((Units.coeHom E).comp ρ)).toRingHom.toAlgebra
  letI := (mapDomainRingHom ℤ f).toAlgebra
  TensorProduct (MonoidAlgebra ℤ L) E (MonoidAlgebra ℤ M)

/-- The tensor-product commutative ring on the character base change: pure tensors multiply
componentwise. Source: ILO VI 2.2, printed p.72
(blueprint: lem-per-tame-kummer-group-algebra-completion). -/
noncomputable instance characterBaseChangeCommRing
    (E : Type u) (L : Type v) (M : Type w)
    [CommRing E] [CommGroup L] [CommGroup M] (f : L →* M) (ρ : L →* Eˣ) :
    CommRing (characterBaseChange E L M f ρ) := by
  unfold characterBaseChange
  infer_instance

/-- The canonical coefficient algebra on the character base change, with `a ↦ a ⊗ 1`.
Source: ILO VI 2.2, printed p.72
(blueprint: lem-per-tame-kummer-group-algebra-completion). -/
noncomputable instance characterBaseChangeAlgebra
    (E : Type u) (L : Type v) (M : Type w)
    [CommRing E] [CommGroup L] [CommGroup M] (f : L →* M) (ρ : L →* Eˣ) :
    Algebra E (characterBaseChange E L M f ρ) := by
  unfold characterBaseChange
  infer_instance

/-- Finite-index abelian group algebra base change along a character is finite free of
rank the index and étale. Over a nonzero complete Noetherian local coefficient ring it
is a product indexed by its maximal ideals of nonzero complete Noetherian local finite
étale coefficient algebras, with finite separable residue extensions.

Source: ILO VI 2.2, printed p.72; Stacks Tags 0325 and 02G8
(blueprint: lem-per-tame-kummer-group-algebra-completion).

Proof:
1. Choose coset representatives for M/f(L). Their monomials form a basis of ℤ[M]
   over ℤ[L]. Tensoring gives an E-basis of U indexed by the same quotient: the inverse
   sends a ⊗ [f(l)s(c)] to the vector with coefficient aρ(l) in coordinate c.
   This respects balancing, so both composites fix the generators.
2. Choose generators of the quotient and adjoin them successively. Their relative
   orders d divide N, hence are units. At each stage the algebra is A[T]/(T^d-u),
   where u is a unit monomial; compare the coset bases to obtain the isomorphism.
   This argument uses no splitting and allows torsion in both groups.
3. The class t of T is a unit, so dt^(d-1) is a unit. The standard étale monic
   derivative lemma proves each stage étale; use composition (including the empty
   tower, where the algebra is E). The algebra tensor pushout supplies all ring maps.
4. Apply finite_over_complete_local_product (Stacks 0325) to obtain the complete
   Noetherian local factors. Nonzero E and the nonempty coset basis imply U is nonzero.
5. Each factor is finite over E by projection. Its spectrum is a clopen component of
   Spec U (finite_product_principal_open at 1, and scheme coproducts), hence is étale
   over E. Coordinate idempotents show that each maximal ideal belongs to exactly
   one local factor, giving the stated indexing and projection-preimage equality.
6. Maximal ideals in a finite algebra contract to the base maximal ideal. Thus the
   factor residue fields are quotients of finite-dimensional E/m-vector spaces and
   are finite. Étale residue-field separability (Stacks 02G8) makes them separable.
-/
theorem tame_group_algebra_baseChange
    (E : Type u) (L : Type v) (M : Type w)
    [CommRing E] [CommGroup L] [CommGroup M] [Group.FG L] [Group.FG M]
    (f : L →* M) (_hf : Function.Injective f)
    [Finite (M ⧸ f.range)] (N : ℕ) (_hN : 0 < N)
    (_hkill : ∀ m : M, m ^ N ∈ f.range) (_hunit : IsUnit (N : E))
    (ρ : L →* Eˣ) :
    Nonempty (Module.Basis (M ⧸ f.range) E (characterBaseChange E L M f ρ)) ∧
      Algebra.Etale E (characterBaseChange E L M f ρ) ∧
      (∀ [Nontrivial E] [IsNoetherianRing E] [IsLocalRing E]
        [IsAdicComplete (IsLocalRing.maximalIdeal E) E],
        Finite {m : Ideal (characterBaseChange E L M f ρ) // m.IsMaximal} ∧
        ∃ (A : {m : Ideal (characterBaseChange E L M f ρ) // m.IsMaximal} →
            CommRingCat.{max u w})
          (algebras : ∀ i, Algebra E (A i))
          (locals : ∀ i, IsLocalRing (A i))
          (localMaps : ∀ i, IsLocalHom (algebraMap E (A i)))
          (e : characterBaseChange E L M f ρ ≃ₐ[E] (∀ i, A i)),
          (∀ i, Nontrivial (A i)) ∧
          (∀ i, IsNoetherianRing (A i)) ∧
          (∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i)) ∧
          (∀ i, Module.Finite E (A i) ∧ Algebra.Etale E (A i)) ∧
          (∀ i, (IsLocalRing.maximalIdeal (A i)).comap
            ((Pi.evalRingHom (fun i ↦ A i) i).comp e.toRingHom) = i.1) ∧
          (∀ i, Module.Finite (IsLocalRing.ResidueField E) (IsLocalRing.ResidueField (A i)) ∧
            Algebra.IsSeparable (IsLocalRing.ResidueField E)
              (IsLocalRing.ResidueField (A i)))) := by
  sorry

end MonoidAlgebra
