/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates and transported adjunctions commuting with shifts

* If two adjunctions commute with shifts, the mate of a natural transformation which
  commutes with shifts commutes with shifts (`NatTrans.CommShift.mateEquiv`).
* An adjunction commuting with shifts, transported along an isomorphism of left adjoints
  commuting with shifts, commutes with shifts (`Adjunction.commShift_ofNatIsoLeft`).
-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {A : Type*} [AddMonoid A]

namespace NatTrans.CommShift

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [HasShift C A] [HasShift D A] [HasShift E A] [HasShift F A]
  {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
  [G.CommShift A] [H.CommShift A] [L₁.CommShift A] [R₁.CommShift A] [L₂.CommShift A]
  [R₂.CommShift A]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

/-- The mate of a natural transformation commuting with shifts, with respect to adjunctions
commuting with shifts, commutes with shifts. -/
lemma mateEquiv (α : TwoSquare G L₁ L₂ H) [NatTrans.CommShift α.natTrans A] :
    NatTrans.CommShift (mateEquiv adj₁ adj₂ α).natTrans A := by
  dsimp only [CategoryTheory.mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

end NatTrans.CommShift

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] [HasShift C A] [HasShift D A]
  {F G : C ⥤ D} {H : D ⥤ C} [F.CommShift A] [G.CommShift A] [H.CommShift A]

/-- An adjunction commuting with shifts, transported along an isomorphism of left adjoints
commuting with shifts, commutes with shifts. -/
lemma commShift_ofNatIsoLeft (adj : F ⊣ H) (iso : F ≅ G) [adj.CommShift A]
    [NatTrans.CommShift iso.hom A] : (adj.ofNatIsoLeft iso).CommShift A where
  commShift_unit := by dsimp only [ofNatIsoLeft]; infer_instance
  commShift_counit := by dsimp only [ofNatIsoLeft]; infer_instance

end Adjunction

end CategoryTheory
