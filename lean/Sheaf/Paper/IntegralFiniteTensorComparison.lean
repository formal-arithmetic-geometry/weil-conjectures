/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices

/-!
# Finite scalar extension of total tensor complexes

Source: Stacks Project, Tags 03EL and 0G6E.
(blueprint: lem-sf-integral-finite-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- Scalar extension commutes with total tensor, with its balanced pure-tensor formula.
Source: Stacks Project, Tags 03EL and 0G6E
(blueprint: lem-sf-integral-finite-tensor-comparison).

Proof: identify the recorded reduction functor with sheafified extension of scalars using
the object and map equations of reductionWitness. The scalar tensor comparison is defined
sectionwise by `(a tensor x) tensor (1 tensor y)` and its inverse by multiplication of the
two finite scalars; balancing and sheafification prove inverse and naturality identities.
Scalar extension is a left adjoint and preserves the coproducts defining the total complex.
The HomologicalComplex bifunctor comparison then gives the degreewise isomorphism. Its
summand inclusion equation, generator naturality, and scalar linearity give the displayed
formula, while naturality handles both signed differential summands. The argument applies
to arbitrary unbounded complexes, including zero complexes. -/
theorem integralFiniteTensorComparison (P Q : Cx l E X none) (n : ℕ) :
    let F := (reduction l E X none n).mapHomologicalComplex (.up ℤ)
    let S := (coefficientTotalTensor.{u, t + 1, t}
      (topology X none) (ring l E X none)).obj (P, Q)
    ∃ β : F.obj S ≅
        (coefficientTotalTensor.{u, t + 1, t} (topology X none)
          (finite l E X none n)).obj (F.obj P, F.obj Q),
      ∀ (p q k : ℤ) (hpq : p + q = k) (V : (Site X none)ᵒᵖ)
          (a : (finite l E X none n).obj.obj V)
          (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (β.hom.f k).val.app V
            (generator l E X none n (S.X k) V a
              (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                (ring l E X none) P Q p q k hpq V x y)) =
          coefficientTensorGenerator.{u, t + 1, t} (topology X none)
            (finite l E X none n) (F.obj P) (F.obj Q) p q k hpq V
            (generator l E X none n (P.X p) V a x)
            (generator l E X none n (Q.X q) V 1 y) := by sorry

end WeilConjectures
