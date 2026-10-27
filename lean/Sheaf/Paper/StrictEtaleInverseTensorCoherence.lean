/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
-/
module

public import Sheaf.Paper.StrictEtaleSystemInterfaces

/-! # Coherence of inverse image with quotient coefficient extension

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The normalized inverse-image tensor comparisons preserve the multiplication unit
and balanced associator of quotient scalar extension.

Source: Zheng, Construction 4.1 and Lemma 5.16, printed pp. 21 and 34--35;
Stacks Tag 0D6D (derived pullback composition).
(blueprint: lem-pur-strict-etale-inverse-tensor-coherence).

Proof: first work on ordinary modules. Transpose under the scalar adjunctions.
The comparison `tensor` is fixed by `tensor_unit`: insertion of `1 tensor x`,
followed by the restriction comparison, is insertion after inverse image.
The ordinary restriction comparisons are fixed on underlying sheaves by the
geometric lift, so their composites are the comparison for the composite quotient
map. For the identity map the same comparison is the restriction multiplication
unit. The normalized ordinary tensor associators take two successive insertions
to the direct insertion. Injectivity of the scalar Hom transposes proves the
ordinary unit and composition squares.

Choose a flat-term K-flat resolution of the input complex. Exact geometric inverse
image preserves flat-term K-flat complexes, as does coefficient extension. Apply
`derivedTensor_rep`, `derivedUnit_rep` and `derivedAssoc_rep` to these complexes.
Naturality moves the scalar computation maps past the inverse-image comparison.
After postcomposing with the inverse-image factorization and the direct scalar
computation map, the proposed composition square becomes the localization of the
ordinary composition square just proved, degree by degree. Those computation maps
are invertible on the chosen complexes, so cancel them. The unit square follows
from the same argument using ordinary multiplication instead of association.
Finally every derived object is isomorphic to its chosen resolution; naturality
transports the two equations across that isomorphism. This uses neither a direct
image projection nor an open extension or a Brown adjoint. Identity quotient maps,
the zero coefficient ring and repeated indices satisfy the same insertion formulas;
no flatness of the quotient homomorphism or boundedness of the input is assumed. -/
theorem strictEtaleInverseTensorCoherence
    {O : Type (u + 1)} [CommRing O] {t : O}
    {V W : Scheme.{u}} (g : V ⟶ W)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (A : StrictEtaleOrdinaryImage O t g)
    (E : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      O t _ _ _ A PW PV) :
    (∀ (n : ℕ) P,
      (E.derivedTensor (Nat.le_refl n)).hom.app P ≫
        (PV.derivedUnit n).hom.app ((E.level n).inverse.obj P) =
      (E.level n).inverse.map ((PW.derivedUnit n).hom.app P)) ∧
    (∀ {r m n : ℕ} (h₁ : m ≤ r) (h₂ : n ≤ m) P,
      (E.level n).inverse.map ((PW.derivedAssoc h₁ h₂).hom.app P) ≫
        (E.derivedTensor (h₂.trans h₁)).hom.app P =
      (E.derivedTensor h₂).hom.app ((PW.scalar h₁).derived.obj P) ≫
        (PV.scalar h₂).derived.map ((E.derivedTensor h₁).hom.app P) ≫
        (PV.derivedAssoc h₁ h₂).hom.app ((E.level r).inverse.obj P)) := by sorry

end AlgebraicGeometry
