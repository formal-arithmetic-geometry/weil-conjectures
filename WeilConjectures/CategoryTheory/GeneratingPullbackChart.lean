/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.GeneratingPullbackChartCore
import WeilConjectures.CategoryTheory.GeneratingPullbackChartGenerators
import WeilConjectures.CategoryTheory.GeneratingPullbackImageQuotient
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # A generating object-slice chart for a ringed inverse image

Source: Stacks Project, algebraization.tex, Tags 099E and 0A0G;
sites-modules.tex, Tags 03D7, 04IE and 04J4.
(blueprint: lem-weil-pbc-generating-pullback-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- An object-slice pullback chart, with its ordinary module comparison and generators.
Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4.
(blueprint: lem-weil-pbc-generating-pullback-chart). -/
structure PullbackCechChart
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (u : G.obj (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) where
  U : D
  V : C
  r : ℕ
  b : Fin r → RY.obj.obj (op V)
  c : Fin r → RX.obj.obj (op U)
  morphism : RingedToposMorphism
    ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V))
  F : ringedSiteModules.{u}
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V)) ⥤
    ringedSiteModules.{u} ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
  additive : F.Additive
  adjunction : F ⊣ morphism.modules
  ringIso : F.obj (SheafOfModules.unit
    ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V))) ≅
    SheafOfModules.unit ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U))
  comparison : SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) V ⋙ F ≅
    G ⋙ SheafOfModules.overFunctor.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) U
  ring_compatibility :
    F.map (ringedOverRingIso RY V).hom ≫ ringIso.hom =
      comparison.hom.app (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫
        (SheafOfModules.overFunctor.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) U).map u.hom ≫
          (ringedOverRingIso RX U).hom
  scalar_compatibility : ∀ i : Fin r,
    F.map (ringedKoszulScalar (RY.over V) (ringedSliceSection RY V (b i))) ≫
        ringIso.hom =
      ringIso.hom ≫ ringedKoszulScalar (RX.over U) (ringedSliceSection RX U (c i))

set_option maxHeartbeats 2000000 in
-- The naturality square compares nested slice-module functors.
/-- A section of an inverse-image representable determines a generating object-slice chart.

Source: Stacks Project, algebraization.tex, Tags 099E and 0A0G;
sites-modules.tex, Tags 03D7, 04IE and 04J4; sites.tex, Tag 00WL.
(blueprint: lem-weil-pbc-generating-pullback-chart).

Proof:
1. Regard the supplied section s as a map from the associated representable of U
to the inverse image of the associated representable of V. Slice the geometric morphism
at the associated representable of V, then relocalize
along s. The representable-slice equivalences identify its endpoints with X/U and Y/V.
The module adjunction and uniqueness of left adjoints identify its pullback F with
restriction after G. Its ring comparison is chosen to agree with u under that comparison.
2. The map G(IY) to RX induced by the structural map has monic coimage J. A factorization
through any monic ideal N is equivalent, by the tensor adjunction and cancellation of N,
to a factorization of the structural image. Thus J and IX have the same least-ideal
property. The two resulting maps over RX are inverse by monicity. Hence G(IY) maps
epimorphically onto IX, compatibly with the inclusions.
3. Pull back the finite free epimorphism on each target chart and restrict this image
quotient. Their composite is an epimorphism from a finite free module onto IX on U.
Its basis images give c and its generating-sections witness. The module comparison
intertwines multiplication by b_i with multiplication by c_i; multiplying the ring
comparison by the unit automorphism prescribed by u preserves that equation.
The empty generating list yields the zero ideal, and empty covers need no extra case. -/
theorem exists_generating_pullback_chart
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
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (U : D) (V : C) (r : ℕ) (b : Fin r → RY.obj.obj (op V))
    (hb : IsRingedIdealGeneratingList RY IY ιY V r b)
    (s : (f.inverse.obj
      ((presheafToSheaf J (Type u)).obj (yoneda.obj V))).obj.obj (op U)) :
    ∃ t : PullbackCechChart RY RX G u,
      t.U = U ∧ t.V = V ∧ t.r = r ∧ HEq t.b b ∧
      IsRingedIdealGeneratingList RY IY ιY t.V t.r t.b ∧
      IsRingedIdealGeneratingList RX IX ιX t.U t.r t.c := by
  classical
  obtain ⟨core, hU, hV, hr, hb'⟩ := exists_generating_pullback_chart_core
    RY RX f G hG u U V r b s
  have hbcore : IsRingedIdealGeneratingList RY IY ιY core.V core.r core.b := by
    cases hV
    cases hr
    cases eq_of_heq hb'
    exact hb
  obtain ⟨e, he, heq⟩ := exists_ringed_image_ideal_quotient
    RY RX f IY ιY IX ιX (fun N j hj ↦
      ⟨fun hk ↦ (hImage N j).mp (fun _ ↦ hk),
        fun ha ↦ (hImage N j).mpr ha hj⟩) G hG u
  let := he
  let R := SheafOfModules.overFunctor
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) core.U
  let : PreservesFiniteColimits R := (SheafOfModules.overFunctor_exact _ core.U).2
  let q : core.F.obj (IY.over core.V) ⟶ IX.over core.U :=
    core.comparison.hom.app IY ≫ R.map e
  have hring : core.ringIso.hom = core.comparison.hom.app (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ≫ R.map u.hom := by
    simpa only [ringedOverRingIso, Iso.refl_hom, Functor.map_id,
      Category.id_comp, Category.comp_id]
      using core.ring_compatibility
  have hq : q ≫ ιX.over core.U = core.F.map (ιY.over core.V) ≫ core.ringIso.hom := by
    change (core.comparison.hom.app IY ≫ R.map e) ≫ R.map ιX = _
    rw [Category.assoc, ← R.map_comp, heq, R.map_comp]
    have hn : core.F.map (ιY.over core.V) ≫ core.comparison.hom.app _ =
        core.comparison.hom.app IY ≫ R.map (G.map ιY) :=
      core.comparison.hom.naturality ιY
    rw [← Category.assoc, ← hn, Category.assoc, ← hring]
  obtain ⟨c, hc, hscalar⟩ := exists_generating_pullback_chart_generators
    RY RX G u core IY ιY IX ιX q hq hbcore
  let t : PullbackCechChart RY RX G u :=
    { U := core.U
      V := core.V
      r := core.r
      b := core.b
      c := c
      morphism := core.morphism
      F := core.F
      additive := core.additive
      adjunction := core.adjunction
      ringIso := core.ringIso
      comparison := core.comparison
      ring_compatibility := core.ring_compatibility
      scalar_compatibility := hscalar }
  exact ⟨t, hU, hV, hr, hb', hbcore, hc⟩

end CategoryTheory
