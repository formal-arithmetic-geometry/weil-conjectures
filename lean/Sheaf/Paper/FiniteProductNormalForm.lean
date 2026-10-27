/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.FiniteProperProductMaps
import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Tensor normal form for two evaluation arrows

Source: Stacks Tags 07A4, 0D6D and 0E48; step 5 of the finite proper product calculation.
(blueprint: lem-pur-finite-product-normal-form).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteProperProduct

/-- The successive tensor evaluations agree with the single tensor of evaluations.
This concerns arbitrary arrows and contains neither exchange, projection nor direct image.
Source: Stacks Tags 07A4 and 0D6D, and step 5 of
lem-pur-finite-proper-product-transpose.
(blueprint: lem-pur-finite-product-normal-form).

Proof: expand pullback of the composite using functoriality. Naturality of the
canonical tensor comparison moves the arrow d across mu for the second projection.
Combine the two tensor maps by bifunctoriality. Apply the canonical tensor comparison's
composition identity for b and the second projection. Expand theta; its inverse
compositor cancels the first tensor component's compositor, leaving the pullback
square's equality followed by the first-projection compositor and the pullback of e.
The second component is the second-projection compositor followed by the pullback of d.
These are exactly the two components in pairEvaluation. Naturality of mu follows by
taking the natural isomorphism supplied by derivedPullbackTensorIso and replacing
its components by canonicalFinitePullbackTensor. No invertibility of e or d is used. -/
theorem finiteProductNormalForm (P : PurityFiniteSetting.{u})
    {B Y Z : Scheme.{u}} (a : Y ⟶ B) (b : Z ⟶ B)
    (sB : B ⟶ Spec (.of P.field.k)) (sZ : Z ⟶ Spec (.of P.field.k))
    (F G : D P B) (H : D P Y) (J : D P Z)
    (e : (pull P a).obj F ⟶ H) (d : (pull P b).obj G ⟶ J) :
    (comp P (pullback.snd a b) b).hom.app ((tensor P B).obj (F, G)) ≫
        (pull P (pullback.snd a b)).map
          ((mu P b sZ sB F G).hom ≫ (tensor P Z).map (Prod.mkHom (𝟙 _) d)) ≫
        (mu P (pullback.snd a b) (pullback.snd a b ≫ sZ) sZ _ J).hom ≫
        (tensor P (pullback a b)).map (Prod.mkHom
          ((theta P a b).hom.app F ≫ (pull P (pullback.fst a b)).map e) (𝟙 _)) =
      pairEvaluation P a b sB sZ F G H J e d := by
  sorry

end WeilConjectures.FiniteProperProduct
