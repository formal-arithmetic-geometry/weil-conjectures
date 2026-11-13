/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteConstantAbelianRefinement
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-!
# Finite local constancy after forgetting an abelian structure

## References

* Stacks Project, Tags 03RU and 03RW
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private instance : etalePrecoverage.{u}.IsStableUnderComposition :=
  inferInstanceAs (precoverage @Etale).IsStableUnderComposition

private theorem finite_constant_value {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale)
    (S : Type (u + 1))
    (e : ((sheafCompose Y.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj S)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)))
    [Nonempty U.left] : Finite S := by
  classical
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let x : U.left := Classical.arbitrary _
  let s := U.left.algClosurePoint x
  let E := (Etale.overSheafEquiv U AddCommGrpCat.{u + 1}).functor
  let es : (sheafCompose U.left.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (E.obj (G.over U)) ≅
      (constantSheaf U.left.smallEtaleTopology (Type (u + 1))).obj S :=
    (Etale.overSheafEquiv U (Type (u + 1))).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        (Type (u + 1)) CategoryTheory.Over.mkIdTerminal).app S
  let eG := (overSheafEquivFunctorObjOverIso AddCommGrpCat.{u + 1} U G).symm
  let eStalk := ((pointSmallEtale (s ≫ U.hom)).sheafFiberCompIso
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app G ≪≫
    (CategoryTheory.forget AddCommGrpCat.{u + 1}).mapIso
      (((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} U.hom s).app G).symm ≪≫
        (pointSmallEtale s).sheafFiber.mapIso eG) ≪≫
    (((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app (E.obj (G.over U))).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso es ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso S
  exact @Finite.of_equiv _ _ (hfinite _ (s ≫ U.hom)) eStalk.toEquiv

/-- Finite local constancy of an abelian sheaf can be tested on its underlying set sheaf
(Stacks, Tags 03RU, 03RW). -/
theorem finite_local_abelian_forget_iff {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose Y.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G) ↔
    IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G) := by
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have hfinite (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
        ((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G)) ↔
      Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G) := by
    let e := ((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app G
    exact ⟨fun h ↦ @Finite.of_equiv _ _ h e.toEquiv,
      fun h ↦ @Finite.of_equiv _ _ h e.toEquiv.symm⟩
  constructor
  · intro h
    refine ⟨?_, fun Ω _ _ s ↦ (hfinite Ω s).mp (h.finite_sheafFiber Ω s)⟩
    classical
    obtain ⟨𝒰₀, h𝒰₀⟩ := h.1
    let 𝒰 : Cover.{u} etalePrecoverage Y :=
      { I₀ := { i : 𝒰₀.I₀ // Nonempty (𝒰₀.X i) }
        X i := 𝒰₀.X i.1
        f i := 𝒰₀.f i.1
        mem₀ := by
          refine (presieve₀_mem_precoverage_iff _).mpr
            ⟨fun y ↦ ?_, fun i ↦ 𝒰₀.map_prop i.1⟩
          obtain ⟨i, x, hx⟩ := 𝒰₀.exists_eq y
          exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩ }
    have hrefine (i : 𝒰.I₀) : ∃ 𝒱 : Cover.{u} etalePrecoverage (𝒰.X i),
        ∀ j : 𝒱.I₀,
          (G.over ((MorphismProperty.Over.map ⊤ (𝒰.etalePrecoverageToEtale i).prop).obj
            (𝒱.etalePrecoverageToEtale j))).IsConstant _ := by
      have := h𝒰₀ i.1
      obtain ⟨S, ⟨e⟩⟩ :=
        (((sheafCompose Y.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).over
            (𝒰₀.etalePrecoverageToEtale i.1)).mem_essImage_of_isConstant
      have : Nonempty (𝒰.etalePrecoverageToEtale i).left := i.2
      have : Finite S := finite_constant_value G (𝒰.etalePrecoverageToEtale i) S e.symm
        (fun Ω _ _ s ↦ h.finite_sheafFiber Ω s)
      exact finite_constant_abelian_refinement G (𝒰.etalePrecoverageToEtale i) S e.symm
    choose 𝒱 h𝒱 using hrefine
    refine ⟨⟨⟨𝒰.bind 𝒱, fun i ↦ ?_⟩⟩⟩
    exact h𝒱 i.1 i.2
  · rintro ⟨hlocal, hstalk⟩
    refine ⟨?_, isFiniteSheaf_of_finite_algClosed_stalks _
      fun Ω _ _ s ↦ (hfinite Ω s).mpr (hstalk Ω s)⟩
    obtain ⟨⟨𝒰, h𝒰⟩⟩ := hlocal.nonempty_locallyConstantDatum
    refine ⟨𝒰, fun i ↦ ?_⟩
    have := h𝒰 i
    change ((sheafCompose (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        (G.over (𝒰.etalePrecoverageToEtale i))).IsConstant _
    infer_instance

end AlgebraicGeometry.Scheme
