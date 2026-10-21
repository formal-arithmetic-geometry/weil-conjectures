/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.Paper.CoefficientSystemImageData

/-! # Unbounded evaluation comparison for strict coefficient systems

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09T5 and 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules



variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

set_option maxHeartbeats 800000 in
-- Elaborate the dependent normalized comparison equations.
/-- Derived direct image commutes with evaluation, including its canonical mates.
Source: Zheng, Construction 4.1 and Lemma 4.10, printed pp. 21 and 23--24.

Proof: Present systems as modules over the quotient-ring sheaf on the sequence site.
That site is essentially small in the coefficient universe, so its module category
has K-injective resolutions. Exact inverse image descends termwise; K-injective
resolutions give total right derived image. Localize the ordinary adjunction with
the canonical fraction-transpose formula to obtain the specified derived adjunction.
On a flat-term K-flat complex P at level n, inverse image commutes with the extension
E_n: both are zero above n, and below n they agree by the inverse-image/tensor
comparison. On quotient tensor generators this is x tensor a mapped to u* x tensor a.
It commutes with reduction of a. The comparison therefore respects the extension
maps sigma and descends to u* LE_n = LE_n u*. The chain of the two LE_n/e_n adjunctions
and the system and level geometric adjunctions gives, naturally in both arguments,
Hom(A,e_n Ru* M) = Hom(A,Ru* e_n M). Yoneda gives directEvaluation. The component at
n of the extension comparison is the identity, so transposing the evaluated counit
proves the counit equation; the triangle identities give the unit equation.
Exact scalar restriction descends termwise. Its left adjoint is derived scalar
extension, computed by the same flat-term K-flat complexes; the pullback/tensor
comparison gives derivedTensor with its representative formula. Composition of the
right derived direct images with restriction gives restrictedDirect. Transposing the
tensor comparison gives exactly restrictedDirect_mate. The localized ordinary
restriction/inverse-image isomorphism gives restrictedInverse; transposing its
underlying identity gives restrictedInverse_mate. On complexes the inverse evaluation
square is the ordinary transition square. For direct image, transpose the sigma
compatibility through the Hom chain above. Its explicit sigma-mate formula is exactly
directTransition. These arguments are natural in every derived system morphism and
use no preservation of K-injectives by evaluation or flatness of a coefficient quotient.
(blueprint: lem-pur-coefficient-system-unbounded-comparison). -/
theorem coefficientSystemUnboundedComparison
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) :
    Nonempty (CoefficientSystemUnboundedImage O ell L V adj S PY PX) := by
  sorry

end SheafOfModules
