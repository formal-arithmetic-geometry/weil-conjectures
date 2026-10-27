/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y6
-/
module

public import Sheaf.Paper.PowerTorsionSheafLimitModels

/-! # Signed exchange for the left Koszul tower

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze, The pro-etale topology for schemes, Sections 3.4--3.5
(blueprint: lem-sp-left-koszul-roos-exchange). -/

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

/-- The signed interchange and finite Koszul tensor exchange in the actual
left-tensor, tower-of-complexes model. This assertion has no torsion hypothesis.

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness sentence,
steps 4--6; Stacks Tags 014E, 012Z and 0941
(blueprint: lem-sp-left-koszul-roos-exchange).

Proof: install the exact countable products of pro-etale module sheaves and
apply signed_double_roos_tensor_exchange to the completed coefficient sheaf.
Conjugate its right-tensor tower by the standard signed symmetry to the
left-tensor tower. Identify its rearranged strict Roos map with the shifted
mapping-cone map defining integralOperationsRoosFunctor. Both comparisons
preserve the two cone projections. Consequently the generic beta has the
asserted four coordinates: interchange the product indices and multiply the
coordinate with both Roos degrees one by minus one. Its inverse performs the
same interchange, so the sign squares to one. The tensor exchange gamma uses
only Koszul degrees -1 and 0: the tensor unit constraints commute with products,
and each total degree is a sum of two product coordinates. This yields an
isomorphism of strict j-towers, compatible with transitions. The canonical
augmentation has only j-Roos degree zero; its four coordinates after beta are
(the unshifted inclusion, the shifted outer inclusion, 0, 0), giving the second
clause. Tensor exchange preserves these inclusions, so composing with Roos of
gamma inverse is precisely the zero-homotopy canonical unit of Roos Q. All
these identities are strict chain-map identities, independent of nilpotence,
regularity, or any choice of a flat resolution. -/
theorem left_koszul_roos_exchange
    (η : 𝟭 (CochainComplex (integralTowerModules l E T) ℤ) ⟶ completion l E T)
    (hη : ∀ P, η.app P = unit l E T P)
    (Q : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E T) ℤ) :
    ∃ (β : (roos l E T).obj (Q ⋙ completion l E T) ≅
        (roos l E T).obj (columns l E T Q)),
        (∀ (p q : Bool) (k : ℤ) (n j : ℕ),
          β.hom.f k ≫ columnCoordinate l E T Q p q k n j =
            if p && q then -rowCoordinate l E T Q p q k n j
            else rowCoordinate l E T Q p q k n j) ∧
        (∀ (k : ℤ) (n j : ℕ),
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q false false k n j =
            coordinateZero l E T Q k n ≫
              (koszulRepresentativeAugmentation
                (completedIntegralCommRingSheafUnrestricted l E T)
                (Q.obj (op n)) (uniformizer l E T) j).f k ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q true false k n j =
            coordinateOne l E T Q k n ≫
              (koszulRepresentativeAugmentation
                (completedIntegralCommRingSheafUnrestricted l E T)
                (Q.obj (op n)) (uniformizer l E T) j).f (k - 1) ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q false true k n j = 0 ∧
          (((roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η)) ≫ β.hom).f k ≫
              columnCoordinate l E T Q true true k n j = 0) ∧
        ∃ γ : (tensorTower l E T).obj ((roos l E T).obj Q) ≅ columns l E T Q,
          (roos l E T).map (Q.rightUnitor.inv ≫ Functor.whiskerLeft Q η) ≫
              β.hom ≫ (roos l E T).map γ.inv =
            unit l E T ((roos l E T).obj Q) := by sorry

end WeilConjectures.PowerTorsionLimit
