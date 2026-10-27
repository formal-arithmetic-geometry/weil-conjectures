/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y6
-/
module

public import Sheaf.Paper.PowerTorsionSheafLimitModels

/-! # The left Koszul unit under termwise nilpotent action

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze, The pro-etale topology for schemes, Sections 3.4--3.5
(blueprint: lem-sp-left-koszul-nilpotent-unit). -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PrincipalKoszulStrictReplacement (uniformizer)

namespace WeilConjectures.PowerTorsionLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (T : AlgebraicGeometry.Scheme.{t})

/-- The canonical left-tensor completion unit is natural on all strict complexes,
and is a quasi-isomorphism when one positive power kills every term.

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.12;
blueprint sec-smooth-purity/sk-lem-sp-tower, completeness sentence, steps 1--3
(blueprint: lem-sp-left-koszul-nilpotent-unit).

Proof: apply nilpotentActionKoszulUnit to the completed coefficient sheaf and
its uniformizer. Use the signed total-tensor symmetry to move each two-term
Koszul complex from the right to the left. On the degree-zero tensor summand
this sends x tensor 1 to 1 tensor x. Identify the rearranged tower Roos functor
with integralOperationsRoosFunctor: both are the shifted cone of one minus the
product shift, and their maps are the shifted mapping-cone maps on the same
product maps. The coordinate normalization of that theorem therefore makes
its transported unit exactly mappingCocone.lift with the stipulated product
augmentation and zero homotopy, namely unit. Naturality follows from tensor
symmetry and naturality of the generic unit. For a complex killed termwise by
pi^r, use that theorem's nilpotent-action clause. More concretely, the quotient
of the Koszul inclusion is the tower P[1] with transition pi; its product shift
s satisfies s^r=0 and 1+s+...+s^(r-1) inverts 1-s. Its Roos complex is acyclic,
whereas the constant tower has limit P by the finite partial-sum contraction.
The associated split-exact triangle proves that the specified unit is a
quasi-isomorphism. Neither the natural transformation nor its normalization
requires nilpotence; the exponent is used only for the final assertion. -/
theorem left_koszul_nilpotent_unit :
    ∃ η : 𝟭 (CochainComplex (integralTowerModules l E T) ℤ) ⟶ completion l E T,
      (∀ P, η.app P = unit l E T P) ∧
      ∀ (P : CochainComplex (integralTowerModules l E T) ℤ) (r : ℕ), 1 ≤ r →
        (∀ (a : ℤ) (U : T.ProEtᵒᵖ) (x : (P.X a).val.obj U),
          (@id ((completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
            ((uniformizer l E T).val U)) ^ r • x = 0) →
        QuasiIso (unit l E T P) := by sorry

end WeilConjectures.PowerTorsionLimit
