/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Filtered continuity for derived abelian evaluation on affine pro-etale objects

Source: Stacks, Tags 03Q6 and 09A3, with localization of derived sections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem globalCohomology_preservesFiltered
    (Y : Scheme.{u}) [IsAffine Y]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] (q : ℕ) :
    PreservesColimitsOfShape I
      (Sheaf.functorH.{u + 1} (Scheme.ProEt.topology Y) q) := by
  constructor
  intro D
  constructor
  intro c hc
  have : ReflectsColimit (D ⋙ Sheaf.functorH (Scheme.ProEt.topology Y) q)
      (forget AddCommGrpCat.{u + 1}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (forget AddCommGrpCat.{u + 1}) ?_⟩
  have hcont :
      (∀ x : Sheaf.H.{u + 1} c.pt q, ∃ (i : I) (y : Sheaf.H.{u + 1} (D.obj i) q),
        Sheaf.H.map (c.ι.app i) q y = x) ∧
      (∀ (i : I) (y : Sheaf.H.{u + 1} (D.obj i) q),
        Sheaf.H.map (c.ι.app i) q y = 0 →
          ∃ (j : I) (f : i ⟶ j), Sheaf.H.map (D.map f) q y = 0) := by
    exact Sheaf.H_map_isColimit_of_isFiltered_small
      (MorphismProperty.Over.mkIdTerminal @WeaklyEtale Y)
      (fun W : Y.ProEt ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left)
      (show CompactSpace Y ∧ QuasiSeparatedSpace Y from ⟨inferInstance, inferInstance⟩)
      (fun _ hW _ hR ↦ Scheme.ProEt.exists_finite_cechNerve_of_mem_topology hW hR) hc q
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨i, y, hy⟩ := hcont.1 x
    exact ⟨i, y, hy.symm⟩
  · intro i a b hab
    change Sheaf.H.map.{u + 1} (c.ι.app i) q a =
      Sheaf.H.map.{u + 1} (c.ι.app i) q b at hab
    have hz : Sheaf.H.map.{u + 1} (c.ι.app i) q (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨j, f, hf⟩ := hcont.2 i (a - b) hz
    refine ⟨j, f, ?_⟩
    change Sheaf.H.map.{u + 1} (D.map f) q a =
      Sheaf.H.map.{u + 1} (D.map f) q b
    exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

private theorem globalDerived_preservesFiltered
    (Y : Scheme.{u}) [IsAffine Y]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] (q : ℕ) :
    PreservesColimitsOfShape I
      ((globalSectionsFunctor AddCommGrpCat.{u + 1} Y).rightDerived q) := by
  have := globalCohomology_preservesFiltered Y I q
  let T : Y.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 Y) (MorphismProperty.id_mem _ Y)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale Y
  obtain ⟨e⟩ := Sheaf.nonempty_rightDerived_sections_iso_functorH
    (Scheme.ProEt.topology Y) hT q
  let e' : (globalSectionsFunctor AddCommGrpCat.{u + 1} Y).rightDerived q ≅
      Sheaf.functorH.{u + 1} (Scheme.ProEt.topology Y) q :=
    NatIso.ofComponents (fun F ↦ e.app ⟨F, trivial⟩)
      (fun {F G} f ↦ e.hom.naturality
        (ObjectProperty.homMk (X := ⟨F, trivial⟩) (Y := ⟨G, trivial⟩) f))
  exact preservesColimitsOfShape_of_natIso e'.symm

/-- Derived evaluation of degree-zero abelian sheaves on an affine pro-etale object
commutes with filtered colimits in every nonnegative degree.
Source: Stacks, Tags 03Q6 and 09A3, and Tag 03F3 for localization.
(blueprint: lem-sfb-proetale-derived-evaluation-continuity).

Proof: localization along the object's weakly etale map is exact, preserves colimits
and preserves injectives. Its composite with global sections is ordinary evaluation.
The derived-composition isomorphism therefore identifies the classical derived
functors of evaluation with localization followed by derived global sections.
On the affine object, pro-etale cohomology commutes with filtered colimits. The
natural identification with classical derived sections gives the same assertion for
that composite. Finally use the natural comparison between classical derived
functors and the homology of the total derived functor on degree-zero sheaves. -/
theorem derivedEvaluation_preservesFiltered
    (X : Scheme.{u}) (W : X.ProEt) [IsAffine W.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] (q : ℕ) :
    PreservesColimitsOfShape I
      ((DerivedCategory.singleFunctor
          (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) 0 ⋙
        (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
          (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)).rightDerivedFunctor) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)) := by
  let E := sectionsFunctor AddCommGrpCat.{u + 1} W
  let L := localizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop
  let Γ := globalSectionsFunctor AddCommGrpCat.{u + 1} W.left
  have : E.Additive := ⟨by intros; rfl⟩
  have : L.Additive := ⟨by intros; rfl⟩
  have : Γ.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits L := by
    dsimp [L, localizationRestriction]
    infer_instance
  have : L.IsLeftAdjoint :=
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} W.hom W.prop).isLeftAdjoint
  have := globalDerived_preservesFiltered W.left I q
  let e₀ : E ≅ L ⋙ Γ :=
    let e : W ≅ (MorphismProperty.Over.map ⊤ W.prop).obj
        (MorphismProperty.Over.mk ⊤ (𝟙 W.left) (MorphismProperty.id_mem _ W.left)) :=
      MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
    NatIso.ofComponents (fun F ↦ F.obj.mapIso e.op)
      (fun a ↦ (a.hom.naturality e.inv.op).symm)
  let e₁ := NatIso.rightDerived e₀ q ≪≫ Functor.rightDerivedCompIsoOfExact L Γ q
  have : PreservesColimitsOfShape I (E.rightDerived q) :=
    preservesColimitsOfShape_of_natIso e₁.symm
  have : PreservesColimitsOfShape I
      (DerivedCategory.singleFunctor _ 0 ⋙ E.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)) :=
    preservesColimitsOfShape_of_natIso
      (E.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso q).symm
  exact preservesColimitsOfShape_of_natIso (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale
