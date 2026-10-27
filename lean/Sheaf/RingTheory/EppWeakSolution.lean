module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Weak Epp solutions via normalized tensor branches

Source: Stacks Project, More on Algebra, Tag 09EM (remark-construction)
and Tag 09EN (definition-solution). The branch criterion is written for
compatible ring and field algebras, specializing to the DVR fraction-field situation.
(blueprint: def-sfb-epp-weak-solution)
-/

@[expose] public section

set_option autoImplicit false

universe u v f g h

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The normalized branch criterion for a finite coefficient extension to be
an Epp weak solution. Set T = (L tensor_K H)_red, take the integral closures
of A in H and B in T, and restrict the canonical map H -> T between them.
Every maximal upper ideal must have maximal contraction; both corresponding
localizations must be DVRs, and extension of their maximal ideals must agree.

The defining construction applies to compatible ring and field algebras;
for an injective local DVR map A -> B with fraction fields K -> L this is
exactly the weak-solution condition of the source. No branch or map is chosen.

Source: Stacks Project, More on Algebra, Tag 09EM (remark-construction)
and Tag 09EN (definition-solution).
(blueprint: def-sfb-epp-weak-solution) -/
def IsEppWeakSolution
    (A : Type u) (B : Type v) (K : Type f) (L : Type g) (H : Type h)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field H]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra K H] [Algebra A H] [IsScalarTower A K H] : Prop :=
  let T := (L ⊗[K] H) ⧸ nilradical (L ⊗[K] H)
  let C := integralClosure B T
  let f : integralClosure A H →+* C :=
    (((Ideal.Quotient.mkₐ K (nilradical (L ⊗[K] H))).comp
      Algebra.TensorProduct.includeRight).restrictScalars A |>.comp
        (integralClosure A H).val).codRestrict
          ((integralClosure B T).restrictScalars A)
          (fun a ↦ (a.property.map
            (((Ideal.Quotient.mkₐ K (nilradical (L ⊗[K] H))).comp
              Algebra.TensorProduct.includeRight).restrictScalars A)).tower_top) |>.toRingHom
  Module.Finite K H ∧
    ∀ (q : Ideal C) [q.IsMaximal],
      (q.comap f).IsMaximal ∧
      (∃ hA : IsDomain (Localization.AtPrime (q.comap f)),
        @IsDiscreteValuationRing (Localization.AtPrime (q.comap f)) _ hA) ∧
      (∃ hB : IsDomain (Localization.AtPrime q),
        @IsDiscreteValuationRing (Localization.AtPrime q) _ hB) ∧
      Ideal.map ((algebraMap C (Localization.AtPrime q)).comp f) (q.comap f) =
        Ideal.map (algebraMap C (Localization.AtPrime q)) q

end IsDiscreteValuationRing
