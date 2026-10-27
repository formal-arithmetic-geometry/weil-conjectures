module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Weak Epp solutions

Source: Stacks Project, More on Algebra, Tags 09EM and 09EN
(blueprint: def-sfb-weak-epp-solution).

The normalized branch predicate is defined for compatible commutative ring and
field diagrams; on local DVR extensions with their fraction fields it is the
weak-solution condition of Tag 09EN.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- A finite coefficient extension is a weak solution if every maximal upper
normalization branch contracts maximally, both local rings are DVRs, and the
contracted ideal generates the upper maximal ideal. The canonical normalization
map is built from `h ↦ 1 ⊗ h`, reduction, and preservation of integral equations.
The lower coefficient algebra is the composite X to P to H.

Source: Stacks Project, More on Algebra, Tags 09EM and 09EN
(blueprint: def-sfb-weak-epp-solution). -/
def IsWeakEppSolution
    (X : Type u) (Y : Type v) (P : Type w) (Q : Type x) (H : Type y)
    [CommRing X] [CommRing Y] [Field P] [Field Q] [Field H]
    [Algebra X Y] [Algebra X P] [Algebra Y Q] [Algebra P Q]
    [Algebra X Q] [IsScalarTower X Y Q] [IsScalarTower X P Q]
    [Algebra P H] : Prop :=
  letI : Algebra X H := Algebra.compHom H (algebraMap X P)
  letI : IsScalarTower X P H := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let C := integralClosure Y ((Q ⊗[P] H) ⧸ nilradical (Q ⊗[P] H))
  let f : integralClosure X H →+* C :=
    (((Ideal.Quotient.mkₐ P (nilradical (Q ⊗[P] H))).comp
      Algebra.TensorProduct.includeRight).restrictScalars X |>.comp
        (integralClosure X H).val).codRestrict
          ((integralClosure Y ((Q ⊗[P] H) ⧸ nilradical (Q ⊗[P] H))).restrictScalars X)
          (fun a ↦ (a.property.map
            (((Ideal.Quotient.mkₐ P (nilradical (Q ⊗[P] H))).comp
              Algebra.TensorProduct.includeRight).restrictScalars X)).tower_top) |>.toRingHom
  Module.Finite P H ∧ ∀ (q : Ideal C) [q.IsMaximal],
    ∃ hn : (q.comap f).IsMaximal,
      letI := hn
      (∃ hdom : IsDomain (Localization.AtPrime (q.comap f)),
        @IsDiscreteValuationRing (Localization.AtPrime (q.comap f)) _ hdom) ∧
      (∃ hdom : IsDomain (Localization.AtPrime q),
        @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
      Ideal.map ((algebraMap C (Localization.AtPrime q)).comp f) (q.comap f) =
        Ideal.map (algebraMap C (Localization.AtPrime q)) q

end IsDiscreteValuationRing
