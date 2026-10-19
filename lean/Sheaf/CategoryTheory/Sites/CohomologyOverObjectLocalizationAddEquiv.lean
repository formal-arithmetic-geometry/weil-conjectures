module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.CategoryTheory.Sites.OverPullbackPreservesInjectives
import Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections

@[expose] public section

universe u₁

namespace CategoryTheory

/-- Additive equivalence underlying the comparison of cohomology over an object
with cohomology on the localized site.

This is the chain-level comparison induced by restricting an injective resolution
along the slice localization; its construction follows Stacks Project, Lemma 03F3.
(blueprint: lem-weil-pbc-cohomology-over-object-localization-addEquiv)

Proof: Restrict an injective resolution along the localized-site restriction.
Use exactness and preservation of injectives, then identify the resulting section complexes.
Taking cohomology yields the additive equivalence.
-/
theorem cohomology_over_object_localization_addEquiv
    {C : Type u₁} [Category.{u₁} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u₁}]
    [HasExt.{u₁} (Sheaf J AddCommGrpCat.{u₁})]
    (F : Sheaf J AddCommGrpCat.{u₁}) (W : C) (q : ℕ)
    [HasSheafify (J.over W) AddCommGrpCat.{u₁}]
    [HasExt.{u₁} (Sheaf (J.over W) AddCommGrpCat.{u₁})] :
    Nonempty ((Sheaf.H' F q W) ≃+ Sheaf.H'
      ((GrothendieckTopology.overPullback J AddCommGrpCat.{u₁} W).obj F) q (Over.mk (𝟙 W))) := by
  let R := J.overPullback AddCommGrpCat.{u₁} W
  have : R.Additive := by
    constructor
    intro F G f g
    ext V
    rfl
  have : R.PreservesInjectiveObjects := overPullback_preservesInjectiveObjects J W
  have : R.IsLeftAdjoint :=
    ((Over.forget W).sheafAdjunctionCocontinuous AddCommGrpCat.{u₁}
      (J.over W) J).isLeftAdjoint
  have : Limits.PreservesFiniteColimits R := inferInstance
  have : R.IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget W) AddCommGrpCat.{u₁} (J.over W) J).isRightAdjoint
  have : Limits.PreservesFiniteLimits R := inferInstance
  have : R.PreservesHomology := inferInstance
  let I := injectiveResolution F
  let I' : InjectiveResolution (R.obj F) :=
    { cocomplex := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective := fun n ↦ R.injective_obj (I.cocomplex.X n)
      ι := (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app F ≫
        (R.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι }
  let S := sheafToPresheaf J AddCommGrpCat.{u₁} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u₁}).obj (Opposite.op W)
  let S' := sheafToPresheaf (J.over W) AddCommGrpCat.{u₁} ⋙
    (evaluation (Over W)ᵒᵖ AddCommGrpCat.{u₁}).obj (Opposite.op (Over.mk (𝟙 W)))
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived J W q
  obtain ⟨e'⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    (J.over W) (Over.mk (𝟙 W)) q
  let h : ((S.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      ((S'.mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex) := Iso.refl _
  let a := e.app F ≪≫ I.isoRightDerivedObj S q ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u₁} (ComplexShape.up ℕ) q).mapIso h ≪≫
      (I'.isoRightDerivedObj S' q).symm ≪≫ (e'.app (R.obj F)).symm
  exact ⟨a.addCommGroupIsoToAddEquiv⟩

end CategoryTheory
