module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! Internal Hom compatibility obtained from an exceptional projection isomorphism. -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
  [MonoidalCategory D] [MonoidalClosed D] [BraidedCategory D]
  {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) (F : D ⥤ C)

/-- An exceptional projection isomorphism identifies the right adjoints of tensoring
before and after the exceptional pushforward. -/
def ihomIsoOfExceptionalProjection (K : D)
    (pf : P ⋙ tensorRight K ≅ tensorRight (F.obj K) ⋙ P) :
    ihom K ⋙ S ≅ S ⋙ ihom (F.obj K) :=
  (adj.comp (ihom.adjunction K)).rightAdjointUniq
    (((ihom.adjunction (F.obj K)).comp adj).ofNatIsoLeft
      (Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight (F.obj K)) P ≪≫
        pf.symm ≪≫
        Functor.isoWhiskerLeft P (BraidedCategory.tensorLeftIsoTensorRight K).symm))

end CategoryTheory.Adjunction
