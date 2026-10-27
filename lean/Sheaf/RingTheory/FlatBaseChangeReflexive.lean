module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat base change of finite reflexive modules

Source: Stacks Project, More on Algebra, Tag 0EB9, lemma-flat-pullback-reflexive
(blueprint: lem-per-flat-base-change-reflexive-modules).

The scalar extension is written `B ⊗[A] M`, with `B` acting on its first factor.
Tensor commutation identifies this canonically with the source's `M ⊗[A] B`,
with `B` acting on its second factor.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Module

/-- A finite reflexive module stays finite and reflexive after flat extension of
Noetherian domains. Reflexivity is bijectivity of the evaluation map to the double dual.

Source: Stacks Project, Tag 0EB9, lemma-flat-pullback-reflexive
(blueprint: lem-per-flat-base-change-reflexive-modules).

Proof plan:
1. By `lem-per-reflexive-saturated-free-embedding` over `A`, embed `M` in a finite free
   module `A^r` with torsion-free quotient `N`.
2. Flat tensor exactness (`lem-weil-pbc-flat-tensor-exact`, using
   `def-weil-pbc-flat-ring-map`) gives injectivity and middle exactness after tensoring.
   Surjectivity follows by lifting each first factor of a finite sum of pure tensors.
3. If `m_j` generate `M`, the tensors `1 ⊗ m_j` generate `B ⊗[A] M`.
   The coordinate map identifies `B ⊗[A] A^r` with `B^r`; its inverse sends a tuple
   to the sum of its coordinates tensored with the standard basis vectors.
4. By `lem-per-flat-base-change-torsion-free`, `B ⊗[A] N` is torsion free over `B`.
5. Apply the converse of `lem-per-reflexive-saturated-free-embedding` over `B` to
   this finite module embedded in `B^r` with torsion-free quotient. This proves
   reflexivity, and step 3 already proves finite generation. No normality,
   projectivity, local freeness, or finite-type assumption is used. -/
theorem finite_isReflexive_baseChange
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsReflexive A M]
    (hflat : (algebraMap A B).Flat) :
    Module.Finite B (B ⊗[A] M) ∧ Module.IsReflexive B (B ⊗[A] M) := by
  sorry

end Module
