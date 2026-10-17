module

public import Mathlib.RingTheory.SimpleModule.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory
namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {Λ : Type (u + 1)} [CommRing Λ]

set_option synthInstance.maxHeartbeats 400000 in
set_option diagnostics true in
set_option diagnostics.threshold 2000 in
lemma mono_whiskerRight_of_smul_id_eq_zero (r : Λ) [(Ideal.span {r}).IsMaximal]
    {X Y : Sheaf J (ModuleCat.{u + 1} Λ)} (f : X ⟶ Y) [Mono f] (hY : r • 𝟙 Y = 0)
    (F : Sheaf J (ModuleCat.{u + 1} Λ)) : Mono (f ▷ F) := by
  have : Mono f.hom := inferInstanceAs (Mono ((sheafToPresheaf J _).map f))
  have (U : Cᵒᵖ) : Mono ((f.hom ▷ F.obj).app U) := by
    have : IsSplitMono (f.hom.app U) :=
      ModuleCat.isSplitMono_of_smul_id_eq_zero r _ congr(($hY).hom.app U)
    exact inferInstanceAs (Mono ((tensorRight _).map (f.hom.app U)))
  have : Mono (f.hom ▷ F.obj) := NatTrans.mono_of_mono_app _
  have : Mono ((sheafToPresheaf J _ ⋙ tensorRight F.obj ⋙ presheafToSheaf J _).map f) :=
    inferInstanceAs (Mono ((presheafToSheaf J _).map (f.hom ▷ F.obj)))
  change Mono ((tensorRight F).map f)
  rw [← NatIso.naturality_2 (Sheaf.tensorRightIso F) f]
  infer_instance
end CategoryTheory.Sheaf
