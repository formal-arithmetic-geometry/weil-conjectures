/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences

/-! # Projection mates at tensor-invertible coefficients

Source: the scalar-generator proof of the finite proper projection formula.
(blueprint: lem-coef-left-mate-equivalence).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.CoefPairingFrame

/-- Projection is invertible for any tensor comparison if tensoring by the chosen
coefficient before and after pullback gives equivalences.
Source: the mates correspondence and the shifted free scalar step of proper projection.
(blueprint: lem-coef-left-mate-equivalence).
Proof: fix the first tensor variable. The tensor comparison becomes an invertible
square whose vertical sides are the two tensor equivalences. Its mate is invertible
by invariance of mates under equivalences. Transposing its component identifies it
with leftMate: both transposes are tensor comparison followed by tensor of the counit. -/
theorem leftMate_isIso_of_tensor_equivalences
    {V W : Type*} [Category* V] [Category* W]
    (TV : V × V ⥤ V) (TW : W × W ⥤ W) (L : V ⥤ W) (G : W ⥤ V)
    (adj : L ⊣ G) (mu : TV ⋙ L ≅ L.prod L ⋙ TW) (H : V)
    [(Prod.sectR H V ⋙ TV).IsEquivalence]
    [(Prod.sectR (L.obj H) W ⋙ TW).IsEquivalence] (M : W) :
    IsIso (leftMate TV TW L G adj mu H M) := by
  let θ : (Prod.sectR H V ⋙ TV) ⋙ L ≅
      L ⋙ Prod.sectR (L.obj H) W ⋙ TW :=
    NatIso.ofComponents (fun N ↦ mu.app (H, N)) (by
      intro N N' f
      simpa using mu.hom.naturality (Prod.mkHom (𝟙 H) f))
  have := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj
    (Prod.sectR H V ⋙ TV) (Prod.sectR (L.obj H) W ⋙ TW) θ
  have he : (mateEquiv adj adj θ.hom).natTrans.app M = leftMate TV TW L G adj mu H M := by
    apply (adj.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit]
    erw [mateEquiv_counit]
    dsimp only [leftMate]
    erw [Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app]
    simp [θ, Functor.curryObjProdComp_hom_app_app]
    rfl
  rw [← he]
  infer_instance

end CategoryTheory.CoefPairingFrame
