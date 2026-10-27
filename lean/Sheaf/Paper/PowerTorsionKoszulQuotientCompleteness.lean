/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y6
-/
module

public import Sheaf.Paper.PowerTorsionSheafLimitModels

/-! # From the Koszul unit to actual quotient completeness

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness sentence;
Bhatt--Scholze, The pro-etale topology for schemes, Sections 3.4--3.5
(blueprint: lem-sp-left-koszul-quotient-completeness). -/

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

/-- An invertible canonical Koszul unit gives the actual quotient-completion
comparison, its normalized projections, and integral derived completeness.
The input is an arbitrary complex, with no outer tower or torsion hypothesis.

Source: blueprint sec-smooth-purity/sk-lem-sp-tower, completeness sentence,
steps 7--9; Bhatt--Scholze Lemmas 3.5.4--3.5.7; Stacks Tags 06YP, 06YQ and 0941
(blueprint: lem-sp-left-koszul-quotient-completeness).

Proof: multiplication by the completed uniformizer is injective, and its
power quotients are the actual finite coefficient sheaves, by
sp_completed_coefficients_regular. Choose one flat-term K-flat resolution
f:P to M. Apply koszulQuotientStrictResolutionBridge to this resolution,
using the normalized ordinary change-of-rings presentation of IntegralOnSlice.
Its left span arrow tensors f with the finite free Koszul complex, and its
right arrow tensors the quotient augmentation with P; both are levelwise
quasi-isomorphisms. Exact products make their Roos maps quasi-isomorphisms.
Identify its localization with DerivedCategory.Q by quotientCompQhIso and
its strict Roos maps with integralOperationsRoosFunctor. The resulting
isomorphism s obeys Q(unit M) s = Q(f)^(-1) Q(roosUnit P); each unshifted
projection is Q(f)^(-1) times the ordinary scalar-unit component. These are
exactly the two stated normalization equations. The given quasi-isomorphism
of the unit makes this quotient augmentation invertible. Take the canonical
distinguished Roos triangle of the quotient tower and transport its first
object along this augmentation. Its first map has the stated product
components; its second map stays one minus shift, and its last map is the
old connecting morphism followed by the shifted inverse augmentation.
Finally identify the unrestricted coefficient convention with the none slice:
its tower and its augmentation are the legacy integral reduction tower and
unit on P. Choosing an auxiliary finite field of characteristic different
from l realizes the same coefficients. The transported triangle is therefore
exactly IsDerivedCompleteUnrestricted, hence IntegralOnSlice.IsComplete.
No completeness assumption on M was used before applying the given unit
quasi-isomorphism, and one common P is used at every quotient level. -/
theorem left_koszul_quotient_completeness
    (M : CochainComplex (integralTowerModules l E T) ℤ)
    (hu : QuasiIso (unit l E T M)) :
        ∃ (P : (IntegralOnSlice.Good l E T none).FullSubcategory)
          (f : P.obj ⟶ M)
          (eP : DerivedCategory.Q.obj P.obj ≅ DerivedCategory.Q.obj M)
          (s : DerivedCategory.Q.obj ((completion l E T).obj M) ≅
            DerivedCategory.Q.obj ((roos l E T).obj
              ((IntegralOnSlice.tower l E T none).obj P.obj))),
          QuasiIso f ∧ eP.hom = DerivedCategory.Q.map f ∧
          DerivedCategory.Q.map (unit l E T M) ≫ s.hom =
            eP.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj) ∧
          (∀ j : ℕ,
            DerivedCategory.Q.map (unit l E T M) ≫ s.hom ≫
                DerivedCategory.Q.map (evaluation l E T
                  ((IntegralOnSlice.tower l E T none).obj P.obj) j) =
              eP.inv ≫ DerivedCategory.Q.map
                (((IntegralOnSlice.augmentation l E T none).app P.obj).app (op j))) ∧
          (∃ (hprod : HasProduct (fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j))),
            (fun [_hp : HasProduct (fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j))] ↦
            ∃ (p : DerivedCategory.Q.obj M ⟶
                ∏ᶜ fun j : ℕ ↦ (IntegralOnSlice.derivedTower l E T none P).obj (op j))
            (δ : (∏ᶜ fun j : ℕ ↦
                (IntegralOnSlice.derivedTower l E T none P).obj (op j)) ⟶
              (DerivedCategory.Q.obj M)⟦(1 : ℤ)⟧),
            IsDerivedLimitTriangle
              (fun j : ℕ ↦ (IntegralOnSlice.derivedTower l E T none P).map
                (homOfLE j.le_succ).op) (DerivedCategory.Q.obj M) p δ ∧
            ∀ j : ℕ, p ≫ Pi.π _ j = eP.inv ≫ DerivedCategory.Q.map
              (((IntegralOnSlice.augmentation l E T none).app P.obj).app (op j)))
              (_hp := hprod)) ∧
          IntegralOnSlice.IsComplete l E T none
            (DerivedCategory.Q.obj M) := by sorry

end WeilConjectures.PowerTorsionLimit
