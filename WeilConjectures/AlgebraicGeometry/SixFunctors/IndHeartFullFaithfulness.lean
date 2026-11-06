/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.Ind
import WeilConjectures.CategoryTheory.SixFunctors.IndHeartRealization
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Constructible sheaves are finitely presented and realize the ind-heart fully faithfully

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`det-ind-heart-full-faithfulness` (blueprint: det-ind-heart-full-faithfulness).

The coefficient ring objects carry their canonical ring-object structures: the one of
`Profinite.continuousMapRingObj E` resp. `Profinite.padicAlgClRingObj ℓ`, and on
`Λ_X = condensedRingObj Λ X` the one transported along `upperStarFromPoint X` (the scoped
instance `Functor.monObjObj` of `CategoryTheory.Obj`). Small diagrams are indexed by categories
in `Type (u + 1)`, the hom universe of the module category, as in `CategoryTheory.Ind`
(size convention def-weil-size-convention).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem finitelyPresentable_of_continuity
    {A : Type*} [Category.{u + 1} A] [HasFilteredColimits A]
    {D : Type*} [Category.{u + 1} D] [Preadditive D]
    (F : A ⥤ D) [F.Full] [F.Faithful] (C : A) (T : D) (e : F.obj C ≅ T)
    (h : ∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (M : J ⥤ A),
      IsIso (colimit.post M (F ⋙ preadditiveCoyoneda.obj (Opposite.op T)))) :
    IsFinitelyPresentable.{u + 1} C := by
  let G := F ⋙ preadditiveCoyoneda.obj (Opposite.op T)
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} G := by
    constructor
    intro J _ _
    constructor
    intro M
    have := h J M
    exact preservesColimit_of_isIso_post G M
  let i : coyoneda.obj (Opposite.op C) ≅ G ⋙ forget AddCommGrpCat :=
    NatIso.ofComponents (fun Y ↦
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
        (Iso.homCongr e (Iso.refl (F.obj Y)))).toIso) (by
          intro Y Z f
          ext g
          change e.inv ≫ F.map (g ≫ f) ≫ 𝟙 _ =
            (e.inv ≫ F.map g ≫ 𝟙 _) ≫ F.map f
          simp [Functor.map_comp, Category.assoc])
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  exact ⟨fun J _ _ ↦ preservesColimitsOfShape_of_natIso i.symm⟩

/-- The two assertions of det-ind-heart-full-faithfulness for a condensed coefficient ring
object `Λ` and a scheme `X`, in `Mod_{Λ_X}` (internal modules over `Λ_X = p_X^* Λ`):
1. every constructible module (sk-def-sfb-constructible) is finitely presentable, i.e.
`Hom(C, -)` preserves all small filtered colimits;
2. there is a functor `Φ : Ind(Cons(X, Λ)) ⥤ Mod_{Λ_X}` which is the realization: its
restriction along `Ind.yoneda` is isomorphic to the inclusion of the constructible modules,
and it sends the canonical colimit of the presentation diagram of every ind-object to an actual
colimit; this `Φ` is full and faithful, and its essential image is `ObjectProperty.ind.{u + 1}`
of the constructible modules, i.e. `IndCons(X, Λ)`.
Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
`det-ind-heart-full-faithfulness`, clauses 1 and 2 (blueprint: det-ind-heart-full-faithfulness). -/
def IndHeartFullFaithfulnessAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  (∀ C : ObjectProperty.FullSubcategory (IsConstantModelConstructible Λ X),
    IsFinitelyPresentable.{u + 1}
      (C.1 : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) ∧
  ∃ Φ : CategoryTheory.Ind (ObjectProperty.FullSubcategory
      (IsConstantModelConstructible Λ X)) ⥤
    CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    Nonempty (CategoryTheory.Ind.yoneda ⋙ Φ ≅
      ObjectProperty.ι (IsConstantModelConstructible Λ X)) ∧
    (∀ Z : CategoryTheory.Ind (ObjectProperty.FullSubcategory
        (IsConstantModelConstructible Λ X)),
      Nonempty (IsColimit
        (Φ.mapCocone (colimit.cocone
          ((CategoryTheory.Ind.presentation Z).F ⋙ CategoryTheory.Ind.yoneda))))) ∧
    Φ.Full ∧ Φ.Faithful ∧
    (∀ M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      Φ.essImage M ↔ ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M)

end AlgebraicGeometry.ProEtale
