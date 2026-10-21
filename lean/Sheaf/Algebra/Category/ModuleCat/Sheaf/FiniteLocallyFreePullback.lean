/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Finite locally free modules under ringed site pullback

Source: Stacks Project, Modules on Sites, Tags 03DO and 04J0.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
open RingedSitePullback

/-- Ringed inverse image transports finite local bases along a covering family.
Source: Stacks Project, Tags 03DO and 04J0.
(blueprint: lem-sfb-finite-locally-free-ringed-pullback)

Proof: choose local generators that form finite bases. Localize the site morphism
at each covering object. Localization commutes with pullback, and pullback takes
a free module to the free module on the same basis. The transported covering
family and these finite bases prove finite local freeness, including rank zero. -/
theorem finiteLocallyFree_pullback
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [PreservesFiniteLimits F]
    {R : Sheaf J RingCat.{max u v w}} {S : Sheaf K RingCat.{max u v w}}
    (a : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    [(pushforward.{max u v w} a).IsRightAdjoint]
    (hc : CoverPreserving J K F)
    [∀ V, HasSheafify (J.over V) Ab.{max u v w}]
    [∀ V, (J.over V).WEqualsLocallyBijective Ab.{max u v w}]
    [∀ V, HasSheafify (K.over V) Ab.{max u v w}]
    [∀ V, (K.over V).WEqualsLocallyBijective Ab.{max u v w}]
    (M : SheafOfModules.{max u v w} R) [hM : M.IsFiniteLocallyFree] :
    ((pullback a).obj M).IsFiniteLocallyFree := by
  classical
  let : (pushforward.{max u v w} a).IsRightAdjoint :=
    module_pushforward_isRightAdjoint_of_universes a
  have ht {I : Type u} (V : I → C) (hV : J.CoversTop V) :
      K.CoversTop (F.obj ∘ V) := by
    apply (K.coversTop_iff_of_isTerminal (F.obj (⊤_ C))
      ((terminalIsTerminal (C := C)).isTerminalObj F) (F.obj ∘ V)).2
    apply K.superset_covering _ (hc.cover_preserve (hV (⊤_ C)))
    rintro Z g ⟨W, t, h, ⟨i, ⟨k⟩⟩, _⟩
    exact ⟨i, ⟨h ≫ F.map k⟩⟩
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let := hq
  let := hf
  let V := q.X
  let κ (i : q.I) := (q.generators i).I
  let (i : q.I) : Finite (κ i) := by
    let := hf.isFiniteType i
    infer_instance
  apply isFiniteLocallyFree_of_exists_over_iso_free (F.obj ∘ V) (ht V q.coversTop) κ
  intro i
  let := local_continuous (U := F) hc (V i)
  let b := locMap a (V i)
  let := module_pushforward_isRightAdjoint_of_universes b
  let : RepresentablyFlat (Over.post (X := V i) F) := flat_of_preservesFiniteLimits _
  let : (Over.post (X := V i) F).Final := final_of_representablyFlat _
  exact ⟨(asIso (localComparison a (V i) M)).symm ≪≫
    (pullback b).mapIso (asIso (q.generators i).π).symm ≪≫ pullbackObjFreeIso b (κ i)⟩

end SheafOfModules
