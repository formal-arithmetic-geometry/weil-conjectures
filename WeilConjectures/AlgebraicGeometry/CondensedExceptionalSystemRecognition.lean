/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedExceptionalReconstructionData
import WeilConjectures.AlgebraicGeometry.CondensedExceptionalConcentratedLift
import WeilConjectures.AlgebraicGeometry.CondensedExceptionalBoundedOriginComparisons
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # CondensedExceptionalSystemRecognition

Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-system-recognition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  (P : Context l k X Y f c)

section Evaluation
universe a v w
variable {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

private theorem concentrated_hom_ext (r : ℤ) {M N : DerivedCategory A}
    [M.IsGE r] [M.IsLE r] [N.IsGE r] [N.IsLE r]
    {f g : M ⟶ N}
    (h : (DerivedCategory.homologyFunctor A r).map f =
      (DerivedCategory.homologyFunctor A r).map g) : f = g := by
  obtain ⟨U, ⟨eM⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M r
  obtain ⟨V, ⟨eN⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE N r
  apply (cancel_epi eM.inv).mp
  apply (cancel_mono eN.hom).mp
  have hh : (DerivedCategory.homologyFunctor A r).map (eM.inv ≫ f ≫ eN.hom) =
      (DerivedCategory.homologyFunctor A r).map (eM.inv ≫ g ≫ eN.hom) := by
    simp only [Functor.map_comp, h]
  obtain ⟨b, hb⟩ := (DerivedCategory.singleFunctor A r).map_surjective
    (eM.inv ≫ f ≫ eN.hom)
  obtain ⟨c, hc⟩ := (DerivedCategory.singleFunctor A r).map_surjective
    (eM.inv ≫ g ≫ eN.hom)
  simp only [Category.assoc] at ⊢
  rw [← hb, ← hc] at hh ⊢
  have : (DerivedCategory.singleFunctor A r ⋙ DerivedCategory.homologyFunctor A r).Faithful :=
    Functor.Faithful.of_iso (DerivedCategory.singleFunctorCompHomologyFunctorIso A r).symm
  exact congrArg (DerivedCategory.singleFunctor A r).map
    ((DerivedCategory.singleFunctor A r ⋙ DerivedCategory.homologyFunctor A r).map_injective hh)
end Evaluation

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem coefficient_hom_ext {M N : ClopenProEtaleSystem l (Field.{u} l) X.scheme}
    (f g : M ⟶ N) (h : ∀ n, f.app n = g.app n) : f = g := by
  change SheafOfModules.CoefficientSystem.Hom (J := Scheme.ProEt.topology X.scheme) M N at f g
  have hh : f.app = g.app := funext h
  cases f
  cases g
  cases hh
  rfl

local instance evaluation_limits (n : ℕ) : PreservesFiniteLimits
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
      (O := clopenSystemRing l (Field.{u} l))
      (ell := clopenSystemUniformizer l (Field.{u} l)) n) :=
  (SheafOfModules.coefficientEvaluation_exact.{u + 1, u, u + 1} n).1

local instance evaluation_colimits (n : ℕ) : PreservesFiniteColimits
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
      (O := clopenSystemRing l (Field.{u} l))
      (ell := clopenSystemUniformizer l (Field.{u} l)) n) :=
  (SheafOfModules.coefficientEvaluation_exact.{u + 1, u, u + 1} n).2

private def evaluationModel (n : ℕ) : P.source.proEtaleEvaluation.evaluation n ≅
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
      (O := clopenSystemRing l (Field.{u} l))
      (ell := clopenSystemUniformizer l (Field.{u} l)) n).mapDerivedCategory := by
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ClopenProEtaleSystem l (Field.{u} l) X.scheme) (.up ℤ))
    (DerivedCategory.Q ⋙ P.source.proEtaleEvaluation.evaluation n)
    (DerivedCategory.Q ⋙ _)
    (P.source.proEtaleEvaluation.evaluation n) _
    (P.source.proEtaleEvaluation.evaluationFactors n ≪≫
      (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
        (O := clopenSystemRing l (Field.{u} l))
        (ell := clopenSystemUniformizer l (Field.{u} l)) n).mapDerivedCategoryFactors.symm)

set_option synthInstance.maxHeartbeats 100000 in
-- The exact-functor comparison contains the two large coefficient-system categories.
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem evaluation_homology_ext (r : ℤ)
    {M N : DerivedCategory (ClopenProEtaleSystem l (Field.{u} l) X.scheme)}
    {f g : M ⟶ N}
    (h : ∀ n, (P.source.proEtaleEvaluation.evaluation n).map f =
      (P.source.proEtaleEvaluation.evaluation n).map g) :
    (DerivedCategory.homologyFunctor _ r).map f =
      (DerivedCategory.homologyFunctor _ r).map g := by
  apply coefficient_hom_ext l k
  intro n
  let F := SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
    (O := clopenSystemRing l (Field.{u} l))
    (ell := clopenSystemUniformizer l (Field.{u} l)) n
  have he : F.mapDerivedCategory.map f = F.mapDerivedCategory.map g := by
    apply (cancel_epi ((evaluationModel l k P n).hom.app M)).mp
    rw [← (evaluationModel l k P n).hom.naturality f,
      ← (evaluationModel l k P n).hom.naturality g, h n]
  have hh := congrArg (DerivedCategory.homologyFunctor _ r).map he
  have hf := (F.mapDerivedCategoryHomologyFunctorIso r).hom.naturality f
  have hg := (F.mapDerivedCategoryHomologyFunctorIso r).hom.naturality g
  change F.map ((DerivedCategory.homologyFunctor _ r).map f) =
    F.map ((DerivedCategory.homologyFunctor _ r).map g)
  apply (cancel_mono ((F.mapDerivedCategoryHomologyFunctorIso r).hom.app N)).mp
  exact hf.trans ((congrArg
    (fun z ↦ (F.mapDerivedCategoryHomologyFunctorIso r).hom.app M ≫ z) hh).trans hg.symm)

private def evaluationHomology (r : ℤ)
    (M : DerivedCategory (ClopenProEtaleSystem l (Field.{u} l) X.scheme)) (n : ℕ) :
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
      (O := clopenSystemRing l (Field.{u} l))
      (ell := clopenSystemUniformizer l (Field.{u} l)) n).obj
        ((DerivedCategory.homologyFunctor _ r).obj M) ≅
      (DerivedCategory.homologyFunctor _ r).obj
        ((P.source.proEtaleEvaluation.evaluation n).obj M) := by
  let F := SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
    (O := clopenSystemRing l (Field.{u} l))
    (ell := clopenSystemUniformizer l (Field.{u} l)) n
  exact (F.mapDerivedCategoryHomologyFunctorIso r).app M ≪≫
    (DerivedCategory.homologyFunctor _ r).mapIso ((evaluationModel l k P n).app M).symm

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem evaluation_zero_homology (r : ℤ)
    (M : DerivedCategory (ClopenProEtaleSystem l (Field.{u} l) X.scheme))
    (h : ∀ n, IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((P.source.proEtaleEvaluation.evaluation n).obj M))) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj M) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply coefficient_hom_ext l k
  intro n
  let F := SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
    (O := clopenSystemRing l (Field.{u} l))
    (ell := clopenSystemUniformizer l (Field.{u} l)) n
  change F.map (𝟙 _) = F.map 0
  rw [F.map_id, F.map_zero]
  exact ((h n).of_iso (evaluationHomology l k P r M n)).eq_of_src _ _

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem evaluation_ge (r : ℤ)
    (M : DerivedCategory (ClopenProEtaleSystem l (Field.{u} l) X.scheme))
    (h : ∀ n, ((P.source.proEtaleEvaluation.evaluation n).obj M).IsGE r) : M.IsGE r := by
  apply (DerivedCategory.isGE_iff M r).2
  intro q hq
  apply evaluation_zero_homology l k P q M
  intro n
  exact (DerivedCategory.isGE_iff _ r).1 (h n) q hq

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem evaluation_le (r : ℤ)
    (M : DerivedCategory (ClopenProEtaleSystem l (Field.{u} l) X.scheme))
    (h : ∀ n, ((P.source.proEtaleEvaluation.evaluation n).obj M).IsLE r) : M.IsLE r := by
  apply (DerivedCategory.isLE_iff M r).2
  intro q hq
  apply evaluation_zero_homology l k P q M
  intro n
  exact (DerivedCategory.isLE_iff _ r).1 (h n) q hq

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem single_degree_maps
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (sd : SystemIdentification l k d hd) (se : SystemIdentification l k e he)
    (r : ℤ) (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower)
    (hdeg : ∀ n : ℕ,
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsLE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj e.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj e.tower).IsLE r)
    (hmap : ∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).map a ≫
        (e.toBrown l k n).hom = (d.toBrown l k n).hom ≫
          (P.source.proEtaleEvaluation.evaluation n).map
            (P.source.derived.system.inverse.map (P.brown.right.map ((input l k P).map b)))) :
    d.SystemMap l k b a sd.theta se.theta := by
  have := evaluation_ge l k P r d.tower (fun n ↦ (hdeg n).1)
  have := evaluation_le l k P r d.tower (fun n ↦ (hdeg n).2.1)
  have := evaluation_ge l k P r e.tower (fun n ↦ (hdeg n).2.2.1)
  have := evaluation_le l k P r e.tower (fun n ↦ (hdeg n).2.2.2)
  have : (brownTower l k P e.L).IsGE r :=
    DerivedCategory.TStructure.t.isGE_of_iso se.theta r
  have : (brownTower l k P e.L).IsLE r :=
    DerivedCategory.TStructure.t.isLE_of_iso se.theta r
  apply concentrated_hom_ext r
  apply evaluation_homology_ext l k P r
  intro n
  simpa only [Functor.map_comp, sd.levels n, se.levels n] using hmap n

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] in
private theorem reduction_unit (L : Integral l (Field.{u} l) Y.scheme) :
    IsIso ((P.reduction Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj L.obj)) := by
  exact (purNormalizedReconstructionOfScheme l (Field.{u} l) Y.scheme
    (P.reduction Y.scheme)).2 _
    ((purCoefficientModel_predicates l (Field.{u} l) Y.scheme L.obj).1.mp L.property.1)

/-- Transport ordinary Brown recognition to the supplied strict-system coordinates.
Source: blueprint sk-prop-sp-integral-adjunction, tower reconstruction and final
unit/counit paragraph; parent reconstruction proof Steps 1--3.
(blueprint: lem-pur-condensed-exceptional-system-recognition).

Proof: use uniform integral reduction for the input and tests. Apply the ordinary
etale Brown adjunction and its finite/site comparison. Conjugate the resulting
systems by the supplied exact presentation equivalences; their representative and
mate normalizations identify their evaluations with brownLevel. In the supplied
alternative retain its theta. In the single-degree alternative the compatible
level isomorphisms give an isomorphism of the strict degree-r cohomology systems;
good truncation constructs theta with the prescribed evaluations. Componentwise
cohomology detects the lower bound. The input is an etale-origin integral
reduction, so its reconstruction unit and the bounded Brown site unit are
invertible, as is the proper/open origin comparison on the supplied system.
For two systems in degree r, conjugate their maps by good truncation. Faithfulness
of the shifted-heart embedding and componentwise equality of strict sheaf-system
maps turn the given level squares into the whole-system square. This argument
also applies to a supplied theta, since its evaluations agree with the same
normalization. No faithfulness of evaluation on general derived maps is used. -/
theorem condensed_exceptional_system_recognition : Nonempty (SystemRecognition l k P) := by
  classical
  have identify (d : Datum l k P) (hd : d.Admissible l k) :
      Nonempty (SystemIdentification l k d hd) := by
    obtain ⟨lo, hi, hbounds⟩ := hd.constructible.1
    have hbound : ∃ a : ℤ, ∀ n : ℕ,
        ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE a :=
      ⟨lo, fun n ↦ (hbounds n).1⟩
    obtain ⟨hunit, hsupport⟩ :=
      condensed_exceptional_bounded_origin_comparisons l k P d hbound
    have hbrown : ∃ a : ℤ, (brownTower l k P d.L).IsGE a := by
      refine ⟨lo, evaluation_ge l k P lo _ ?_⟩
      intro n
      have := (hbounds n).1
      exact DerivedCategory.TStructure.t.isGE_of_iso (d.toBrown l k n) lo
    have htheta : ∃ theta : d.tower ≅ brownTower l k P d.L,
        hd.alternative.Uses l k theta ∧
          ∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).map theta.hom =
            (d.toBrown l k n).hom := by
      cases halt : hd.alternative with
      | supplied theta levels =>
        exact ⟨theta, by simp only [Datum.Alternative.Uses], levels⟩
      | single r degrees =>
        obtain ⟨theta, levels⟩ :=
          condensed_exceptional_concentrated_lift l k P d hd.transitions r degrees
        exact ⟨theta, by simpa only [Datum.Alternative.Uses, halt] using levels, levels⟩
    obtain ⟨theta, hsupplied, hlevels⟩ := htheta
    exact ⟨{
      theta := theta
      supplied := hsupplied
      brownBound := hbrown
      levels := hlevels
      reduction := reduction_unit l k P d.L
      originUnit := hunit
      originSupport := hsupport }⟩
  let result (d : Datum l k P) (hd : d.Admissible l k) := (identify d hd).some
  exact ⟨{
    result := result
    singleDegree := fun d e hd he r b a hdeg hmap ↦
      single_degree_maps l k P d e hd he (result d hd) (result e he) r b a hdeg hmap }⟩

end WeilConjectures.CondensedExceptionalReconstruction
