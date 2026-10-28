/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.IntegralHomReductionModels

/-! # The completed-coefficient two-term quotient resolution

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 093M, 06YQ and 0657.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The finite coefficient sheaf, restricted to the completed ring, has a K-flat
resolution with two free rank-one terms. The target of the augmentation is the
actual restriction of the finite coefficient unit in degree zero.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1;
Stacks Tags 093M, 06YQ and 0657
(blueprint: lem-sf-integral-reduction-two-term-resolution).

Proof: use the DVR uniformizer of the ring of integers of E. Its (n+1)-st
power is a non-zero-divisor. The complex with that multiplication from the
free rank-one module in degree -1 to the same module in degree zero resolves
the quotient by its (n+1)-st power. Apply constant sheafification on the pro-etale
site and extend scalars to the completed coefficient ring. Flatness of the
completed constant sheaf and its finite-quotient identification preserve the
augmentation quasi-isomorphism. The quotient identification commutes with the
coordinate projection of the completed ring, so its target is exactly the
restricted coefficient unit below. Scalar extension carries the two free terms
to the completed unit and preserves the zero terms. A bounded complex of flat
terms is K-flat. These constructions work in the coefficient universe
max(u,t+1) without identifying the site and coefficient universes, also for the
empty scheme and n=0. -/
theorem integralReduction_twoTerm_resolution (n : ℕ) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    ∃ (Q : CochainComplex (Modules.{t, u} Y R) ℤ)
      (_ : flat.{t, u} Y R Q)
      (_ : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
      (_ : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (_ : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (epsilon : Q ⟶
        ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (scalarReductionTarget l E Y n) 0).obj
            (SheafOfModules.unit (integralCoefficientSheaf l E Y n)))),
      QuasiIso epsilon := by sorry

end WeilConjectures.IntegralHom
