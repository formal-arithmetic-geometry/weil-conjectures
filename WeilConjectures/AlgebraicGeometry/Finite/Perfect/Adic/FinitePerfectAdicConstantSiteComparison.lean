/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Normalized constant sheaf units and site comparisons -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J E] [HasWeakSheafify K E]
  (F : C ⥤ D) [F.IsContinuous J K]
  (L : Sheaf J E ⥤ Sheaf K E)
  (a : L ⊣ F.sheafPushforwardContinuous E J K)
  {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T))

end

section
variable {C : Type (t + 1)} [Category.{t} C] [EssentiallySmall.{t + 1} C]
  (J : GrothendieckTopology C) {B D : Type (t + 1)} [CommRing B] [CommRing D]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} D)] (q : B →+* D)
  [J.PreservesSheafification (ModuleCat.restrictScalars.{t + 1} q)]

end

section
variable {C D : Type (t + 1)} [Category.{t} C] [Category.{t} D]
  [EssentiallySmall.{t + 1} C] [EssentiallySmall.{t + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {B E : Type (t + 1)} [CommRing B] [CommRing E]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} E)]
  [HasWeakSheafify K (ModuleCat.{t + 1} B)]
  [HasWeakSheafify K (ModuleCat.{t + 1} E)]
  (F : C ⥤ D) [F.IsContinuous J K] {T : C}
  (hT : IsTerminal T) (hFT : IsTerminal (F.obj T)) (q : B →+* E)

end

section
variable {C D : Type (t + 1)} [Category.{t} C] [Category.{t} D]
  [EssentiallySmall.{t + 1} C] [EssentiallySmall.{t + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {B E : Type (t + 1)} [CommRing B] [CommRing E]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} E)]
  [HasWeakSheafify K (ModuleCat.{t + 1} B)]
  [HasWeakSheafify K (ModuleCat.{t + 1} E)]
  (F : C ⥤ D) [F.IsContinuous J K] (q : B →+* E)
  (eB : constantSheaf K (ModuleCat.{t + 1} B) ⋙
      F.sheafPushforwardContinuous (ModuleCat.{t + 1} B) J K ≅
    constantSheaf J (ModuleCat.{t + 1} B))
  (eE : constantSheaf K (ModuleCat.{t + 1} E) ⋙
      F.sheafPushforwardContinuous (ModuleCat.{t + 1} E) J K ≅
    constantSheaf J (ModuleCat.{t + 1} E))
  (hB : ∀ N, toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫
    (eB.inv.app N).hom = whiskerLeft F.op
      (toSheafify K ((Functor.const Dᵒᵖ).obj N)))
  (hE : ∀ N, whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N)) ≫
    (eE.hom.app N).hom = toSheafify J ((Functor.const Cᵒᵖ).obj N))

end

section
variable {C D A : Type*} [Category C] [Category D] [Category A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  (F : C ⥤ D) [F.IsContinuous J K]
  (e : constantSheaf K A ⋙ F.sheafPushforwardContinuous A J K ≅ constantSheaf J A)
  (h : ∀ N, toSheafify J ((Functor.const Cᵒᵖ).obj N) ≫ (e.inv.app N).hom =
    whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj N)))
end

section
variable {C D H : Type (t + 1)} [Category.{t} C] [Category.{t} D] [Category.{t} H]
  [EssentiallySmall.{t + 1} C] [EssentiallySmall.{t + 1} D] [EssentiallySmall.{t + 1} H]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology H)
  {B E : Type (t + 1)} [CommRing B] [CommRing E]
  [HasWeakSheafify J (ModuleCat.{t + 1} B)]
  [HasWeakSheafify J (ModuleCat.{t + 1} E)]
  [HasWeakSheafify K (ModuleCat.{t + 1} B)]
  [HasWeakSheafify K (ModuleCat.{t + 1} E)]
  [HasWeakSheafify L (ModuleCat.{t + 1} B)]
  [HasWeakSheafify L (ModuleCat.{t + 1} E)]
  (q : B →+* E)
  (FB : Sheaf J (ModuleCat.{t + 1} B) ⥤ Sheaf K (ModuleCat.{t + 1} B))
  (FE : Sheaf J (ModuleCat.{t + 1} E) ⥤ Sheaf K (ModuleCat.{t + 1} E))
  (GB : Sheaf K (ModuleCat.{t + 1} B) ⥤ Sheaf L (ModuleCat.{t + 1} B))
  (GE : Sheaf K (ModuleCat.{t + 1} E) ⥤ Sheaf L (ModuleCat.{t + 1} E))
  (βF : sheafCompose J (ModuleCat.restrictScalars.{t + 1} q) ⋙ FB ⟶
    FE ⋙ sheafCompose K (ModuleCat.restrictScalars.{t + 1} q))
  (βG : sheafCompose K (ModuleCat.restrictScalars.{t + 1} q) ⋙ GB ⟶
    GE ⋙ sheafCompose L (ModuleCat.restrictScalars.{t + 1} q))
  (eFB : constantSheaf J (ModuleCat.{t + 1} B) ⋙ FB ≅ constantSheaf K (ModuleCat.{t + 1} B))
  (eFE : constantSheaf J (ModuleCat.{t + 1} E) ⋙ FE ≅ constantSheaf K (ModuleCat.{t + 1} E))
  (eGB : constantSheaf K (ModuleCat.{t + 1} B) ⋙ GB ≅ constantSheaf L (ModuleCat.{t + 1} B))
  (eGE : constantSheaf K (ModuleCat.{t + 1} E) ⋙ GE ≅ constantSheaf L (ModuleCat.{t + 1} E))
  (hF : ∀ N, FB.map ((constantCommuteCompose J
      (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
    βF.app ((constantSheaf J (ModuleCat.{t + 1} E)).obj N) ≫
    (sheafCompose K (ModuleCat.restrictScalars.{t + 1} q)).map (eFE.hom.app N) =
      eFB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) ≫
        (constantCommuteCompose K (ModuleCat.restrictScalars.{t + 1} q)).inv.app N)
  (hG : ∀ N, GB.map ((constantCommuteCompose K
      (ModuleCat.restrictScalars.{t + 1} q)).inv.app N) ≫
    βG.app ((constantSheaf K (ModuleCat.{t + 1} E)).obj N) ≫
    (sheafCompose L (ModuleCat.restrictScalars.{t + 1} q)).map (eGE.hom.app N) =
      eGB.hom.app ((ModuleCat.restrictScalars.{t + 1} q).obj N) ≫
        (constantCommuteCompose L (ModuleCat.restrictScalars.{t + 1} q)).inv.app N)

end

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
