/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GeneratingPullbackChart
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Data.Fintype.EquivFin
import WeilConjectures.CategoryTheory.InverseImageCoverRefinement

/-! # A covering family of generating pullback charts

Source: Stacks Project, algebraization.tex, Tag 099E; Sites, Tag 00WL.
(blueprint: lem-weil-pbc-generating-pullback-charts).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Finite generating lists on a target cover give generating slice charts on a
source cover.

Source: Stacks Project, algebraization.tex, Tag 099E; Sites, Tag 00WL.
(blueprint: lem-weil-pbc-generating-pullback-charts).

Proof: choose a finite ideal-generating cover. Refine its inverse image by all
sections on source objects; the local lifting property makes these objects cover.
Construct the generating slice chart of each such section. Its source object is
the indexing source object, so the resulting chart objects still cover. -/
theorem exists_generating_pullback_charts
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX] [IX.IsFiniteType]
    (hImage : ∀ (N : ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf
            ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf
            ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶
              (sheafCompose K (forget RingCat)).obj
                ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶
              f.inverse.obj ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (G : ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [G.PreservesZeroMorphisms]
    (hG : G ⊣ f.modules)
    (u : G.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) :
    ∃ (A : Type u) (chart : A → PullbackCechChart RY RX G u),
      K.CoversTop (fun a ↦ (chart a).U) ∧
      ∀ a : A,
        IsRingedIdealGeneratingList RY IY ιY (chart a).V (chart a).r (chart a).b ∧
        IsRingedIdealGeneratingList RX IX ιX (chart a).U (chart a).r (chart a).c := by
  classical
  let := f.leftExact
  obtain ⟨A, V, r, b, hV, hb⟩ := exists_finiteIdealGeneratingCover RY IY ιY
  let B := Σ U : D, Σ a : A,
    (f.inverse.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj (V a)))).obj.obj (op U)
  have hB : K.CoversTop (fun t : B ↦ t.1) :=
    inverseImage_cover_refinement f.inverse f.direct f.adj A V hV
  have hc : ∀ t : B, ∃ s : PullbackCechChart RY RX G u,
      s.U = t.1 ∧
      IsRingedIdealGeneratingList RY IY ιY s.V s.r s.b ∧
      IsRingedIdealGeneratingList RX IX ιX s.U s.r s.c := by
    intro t
    obtain ⟨s, hU, _, _, _, hg⟩ := exists_generating_pullback_chart RY RX f
      IY ιY IX ιX hImage G hG u t.1 (V t.2.1) (r t.2.1) (b t.2.1)
      (hb t.2.1) t.2.2
    exact ⟨s, hU, hg⟩
  choose chart hU hg using hc
  refine ⟨B, chart, ?_, hg⟩
  intro T
  apply K.superset_covering _ (hB T)
  rintro W g ⟨i, ⟨a⟩⟩
  exact ⟨i, ⟨a ≫ eqToHom (hU i).symm⟩⟩

end CategoryTheory
