/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalReconstructionComparison
import all WeilConjectures.AlgebraicGeometry.ExceptionalSiteOriginComparisonCore
import all WeilConjectures.AlgebraicGeometry.ExceptionalProperOpenOriginProperties
import all WeilConjectures.CategoryTheory.ExactDerivedAdjunctionBounds
import all WeilConjectures.AlgebraicGeometry.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.ExceptionalFiniteProperMate

/-! # Recognition steps for supplied strict coefficient systems

Source: current blueprint integral-adjunction reconstruction and unit/counit paragraph.
-/

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
open CategoryTheory.Functor
section Bounds
universe a av b bv da db
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]

private theorem reflect_bound
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (fac : DerivedCategory.Q ⋙ FD ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hfaith : ∀ (U V : DerivedCategory A),
      (∃ n : ℤ, U.IsGE n) → (∃ n : ℤ, V.IsGE n) →
      Function.Injective (FD.map : (U ⟶ V) → _))
    (K : DerivedCategory A) (a : ℤ) (hK : (FD.obj K).IsGE a) : K.IsGE a := by
  let sA := DerivedCategory.singleFunctor A 0
  let sB := DerivedCategory.singleFunctor B 0
  let e := CategoryTheory.exactDerivedIso F FD fac
  let c : sA ⋙ FD ≅ F ⋙ sB :=
    isoWhiskerLeft sA e ≪≫ F.mapDerivedCategorySingleFunctor 0
  have : F.Faithful := by
    constructor
    intro U V f g hfg
    apply sA.map_injective
    apply hfaith (sA.obj U) (sA.obj V) ⟨0, inferInstance⟩ ⟨0, inferInstance⟩
    apply (cancel_mono (c.hom.app V)).mp
    change (sA ⋙ FD).map f ≫ c.hom.app V = (sA ⋙ FD).map g ≫ c.hom.app V
    rw [c.hom.naturality, c.hom.naturality]
    simp only [Functor.comp_map, hfg]
  have hk : (F.mapDerivedCategory.obj K).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso (e.app K) a
  exact (DerivedCategory.isGE_iff K a).2 fun q hq ↦
    F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff _ a).1 hk q hq)

private theorem evaluation_reflect_bound
    {B : ℕ → Type b} [∀ n, Category.{bv} (B n)] [∀ n, Abelian (B n)]
    [∀ n, HasDerivedCategory.{db} (B n)]
    (ev : ∀ n, A ⥤ B n) [∀ n, (ev n).Additive]
    (hlim : ∀ n, PreservesFiniteLimits (ev n))
    (hcol : ∀ n, PreservesFiniteColimits (ev n))
    (ED : ∀ n, DerivedCategory A ⥤ DerivedCategory (B n))
    (fac : ∀ n, DerivedCategory.Q ⋙ ED n ≅
      (ev n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (hz : ∀ M : A, (∀ n, IsZero ((ev n).obj M)) → IsZero M)
    (K : DerivedCategory A) (a : ℤ) (hK : ∀ n, ((ED n).obj K).IsGE a) :
    K.IsGE a := by
  apply (DerivedCategory.isGE_iff K a).2
  intro q hq
  apply hz
  intro n
  let e := CategoryTheory.exactDerivedIso (ev n) (ED n) (fac n)
  let h : ED n ⋙ DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ ev n :=
    isoWhiskerRight e (DerivedCategory.homologyFunctor _ q) ≪≫
      ((ev n).mapDerivedCategoryHomologyFunctorIso q).symm
  exact ((DerivedCategory.isGE_iff _ a).1 (hK n) q hq).of_iso ((h.app K).symm)

end Bounds

namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  (P : Context l k X Y f c)

/-- A uniform lower bound on the supplied finite exceptional outputs suffices for
invertibility of the actual Brown site unit and actual proper/open origin comparison.
This asserts neither a system isomorphism nor any reconstruction comparison.
Source: blueprint sk-prop-sp-integral-adjunction, bounded site transport in the Hom
chain; parent recognition proof Steps 1--2
(blueprint: lem-pur-condensed-exceptional-bounded-origin-comparisons).

Proof: exact evaluations jointly detect lower bounds, so the supplied tower is bounded
below. The finite identifications phi exhibit each of its levels as the inverse site
image of the corresponding finite etale Brown output. Finite etale/pro-etale inverse
image is exact and fully faithful on bounded-below objects, hence faithful on sheaves
by the single embedding and conservative on cohomology. It therefore reflects each
lower bound, including for an initially unbounded complex. Transfer the supplied
uniform bound through phi and the inverse-evaluation comparison to all evaluations of
the etale Brown output. Exact conservative etale evaluations detect that same lower
bound on the whole etale Brown output. Its actual site unit is invertible: finite
bounded-below full faithfulness gives the evaluated units, the recorded adjunction
mate equations identify them with evaluations of the system unit, and joint
conservativity detects invertibility. The supplied tower is of bounded-below etale
origin at each level by phi and the reflected bounds. The source site counit is thus
invertible, again by finite comparison and joint conservativity. Proper base change
identifies the prescribed proper derived mate with an isomorphism on these objects;
the open comparison is its normalized exact-adjunction mate. Their paste, preceded
by the actual source site counit, is exactly exceptionalSystemOriginComparison for
P.comparison. Hence that actual component is invertible. All comparisons are taken
in P's supplied coordinates: their ordinary section, localization, and mate equations
transport the canonical finite comparisons and fix their units and counits. No
faithfulness of evaluation on general derived maps is asserted. -/
theorem condensed_exceptional_bounded_origin_comparisons
    (d : Datum l k P)
    (hbound : ∃ a : ℤ, ∀ n : ℕ,
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE a) :
    IsIso (P.source.derived.system.adjunction.unit.app
      (P.brown.right.obj ((input l k P).obj d.L))) ∧
      IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower) := by
  let O := clopenSystemRing l (Field.{u} l)
  let ell := clopenSystemUniformizer l (Field.{u} l)
  let CX : ExceptionalSystemSiteComparison O ell X.scheme P.etale.PX :=
    ⟨P.source.proEtaleEvaluation, P.source.ordinary, P.source.derived⟩
  let CY : ExceptionalSystemSiteComparison O ell Y.scheme P.etale.PY :=
    ⟨P.target.proEtaleEvaluation, P.target.ordinary, P.target.derived⟩
  have hfinite (n : ℕ) : Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)) := by
    let R := Padic.coefficientExtensionIntegers l (Field.{u} l)
    let I := Padic.coefficientExtensionIdeal l (Field.{u} l) (n + 1)
    let e : R ≃+* O := ULift.ringEquiv.symm
    have he : (Ideal.span ({ell} : Set O)) ^ (n + 1) = I.map e.toRingHom := by
      change (Ideal.span ({ell} : Set O)) ^ (n + 1) =
        Ideal.map e.toRingHom
          ((Ideal.span {Padic.coefficientExtensionUniformizer l (Field.{u} l)}) ^ (n + 1))
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
      rfl
    let eqv := Ideal.quotientEquiv I _ e he
    let : Finite (R ⧸ I) :=
      Padic.finite_coefficientExtensionRing l (Field.{u} l) (n + 1) (Nat.succ_pos n)
    exact Finite.of_equiv (R ⧸ I) eqv.toEquiv
  let := hfinite
  have hlim (n : ℕ) : PreservesFiniteLimits (CX.ordinary.lift n).modules :=
    (CX.ordinary.inverseExact n).1
  have hcol (n : ℕ) : PreservesFiniteColimits (CX.ordinary.lift n).modules :=
    (CX.ordinary.inverseExact n).2
  have hfull (n : ℕ) := exceptionalLevel_full O ell X.scheme CX.ordinary n
    (CX.image.level n).inverse (CX.image.level n).inverseFactors
  have levelUnit (n : ℕ) M (hM : ∃ a : ℤ, M.IsGE a) :
      IsIso ((CX.image.level n).adjunction.unit.app M) := by
    have : (CX.image.level n).inverse.ReflectsIsomorphisms :=
      exactDerived_reflectsIso_of_boundedBelow_faithful (CX.ordinary.lift n).modules
        (CX.image.level n).inverse (CX.image.level n).inverseFactors
        (fun U V hU hV ↦ (hfull n U V hU hV).1)
    have : IsIso ((CX.image.level n).adjunction.counit.app
        ((CX.image.level n).inverse.obj M)) :=
      exactDerivedAdjunction_counit_isIso_of_origin (CX.ordinary.lift n).modules
        (CX.image.level n).inverse (CX.image.level n).inverseFactors
        (CX.image.level n).adjunction (hfull n) _ M hM (Iso.refl _)
    have hi : IsIso ((CX.image.level n).inverse.map
        ((CX.image.level n).adjunction.unit.app M) ≫
        (CX.image.level n).adjunction.counit.app ((CX.image.level n).inverse.obj M)) := by
      rw [(CX.image.level n).adjunction.left_triangle_components M]
      exact ⟨𝟙 _, by simp, by simp⟩
    have hm : IsIso ((CX.image.level n).inverse.map
        ((CX.image.level n).adjunction.unit.app M)) :=
      IsIso.of_isIso_comp_right _
        ((CX.image.level n).adjunction.counit.app ((CX.image.level n).inverse.obj M))
    exact isIso_of_reflects_iso _ (CX.image.level n).inverse
  obtain ⟨a, ha⟩ := hbound
  let H := P.brown.right.obj ((input l k P).obj d.L)
  have heval (n : ℕ) : ((P.etale.PX.evaluation n).obj H).IsGE a := by
    let e : (CX.image.level n).inverse.obj ((P.etale.PX.evaluation n).obj H) ≅
        (P.source.proEtaleEvaluation.evaluation n).obj d.tower :=
      ((CX.image.inverseEvaluation n).app H).symm ≪≫ (d.toBrown l k n).symm
    have hb : ((CX.image.level n).inverse.obj
        ((P.etale.PX.evaluation n).obj H)).IsGE a :=
      DerivedCategory.TStructure.t.isGE_of_iso e.symm a
    exact reflect_bound (CX.ordinary.lift n).modules _ (CX.image.level n).inverseFactors
      (fun U V hU hV ↦ (hfull n U V hU hV).1) _ a hb
  have zeroPro (M : SheafOfModules.CoefficientSystem
      (J := Scheme.ProEt.topology X.scheme) O ell)
      (hm : ∀ n, IsZero (M.level n)) : IsZero M := by
    apply (IsZero.iff_id_eq_zero _).2
    apply SheafOfModules.system_hom_ext O ell
    funext n
    exact (hm n).eq_of_src _ _
  have hT : d.tower.IsGE a := evaluation_reflect_bound
    (SheafOfModules.coefficientEvaluation (J := Scheme.ProEt.topology X.scheme)
      (O := O) (ell := ell))
    (fun n ↦ (SheafOfModules.coefficientEvaluation_exact.{u + 1, u, u + 1} n).1)
    (fun n ↦ (SheafOfModules.coefficientEvaluation_exact.{u + 1, u, u + 1} n).2)
    CX.proEvaluation.evaluation CX.proEvaluation.evaluationFactors zeroPro d.tower a ha
  have hunit : IsIso (CX.image.system.adjunction.unit.app H) := by
    apply (SheafOfModules.coefficientEvaluation_detectsIso O ell P.etale.PX _).2
    intro n
    have := levelUnit n ((P.etale.PX.evaluation n).obj H) ⟨a, heval n⟩
    have : IsIso ((P.etale.PX.evaluation n).map (CX.image.system.adjunction.unit.app H) ≫
        (CX.image.directEvaluation n).hom.app (CX.image.system.inverse.obj H) ≫
        (CX.image.level n).direct.map ((CX.image.inverseEvaluation n).hom.app H)) := by
      rw [CX.image.unit n H]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((CX.image.directEvaluation n).hom.app (CX.image.system.inverse.obj H) ≫
        (CX.image.level n).direct.map ((CX.image.inverseEvaluation n).hom.app H))
  have horg : CX.origin d.tower := by
    refine ⟨⟨a, hT⟩, ?_⟩
    intro n
    exact ⟨(P.etale.PX.evaluation n).obj H, ⟨a, heval n⟩,
      ⟨((CX.image.inverseEvaluation n).app H).symm ≪≫ (d.toBrown l k n).symm⟩⟩
  have hcounit := (CX.image.origin hfull d.tower horg.1 horg.2).1
  have hsyslim : PreservesFiniteLimits CX.ordinary.inverse := CX.ordinary.systemExact.1
  have hsyscol : PreservesFiniteColimits CX.ordinary.inverse := CX.ordinary.systemExact.2
  let := hsyslim
  let := hsyscol
  have hD : (CX.image.system.direct.obj d.tower).IsGE a :=
    exactDerivedAdjunction_isGE CX.ordinary.inverse _ CX.image.system.inverseFactors
      CX.image.system.adjunction d.tower a
  have levelComparison (n : ℕ) M (hM : ∃ a : ℤ, M.IsGE a) :
      IsIso ((exceptionalSystemLevelComparison P.comparison n).app M) := by
    obtain ⟨b, hb⟩ := hM
    have := exceptionalFiniteProperMate P.comparison n ((P.etale.levelDerivedOpen n).obj M)
      ⟨b, etale_level_open_bound (S := P.etale) n M b hb⟩
    change IsIso (𝟙 _ ≫
      (mateEquiv (P.etale.properDerived.level n).adjunction
        (P.support.val.properDerived.level n).adjunction
        (.mk _ _ _ _ (P.comparison.properSquare.derivedLevel n).hom)).app
          ((P.etale.levelDerivedOpen n).obj M) ≫
      𝟙 _ ≫ (P.support.val.properDerived.level n).direct.map
        ((P.comparison.levelOpenComparison n).hom.app M) ≫ 𝟙 _)
    infer_instance
  have hcomp : IsIso ((exceptionalSystemComparison P.comparison).app
      (CX.image.system.direct.obj d.tower)) := by
    apply (CY.image.detectsIso _).2
    intro n
    have := levelComparison n
      ((P.etale.PX.evaluation n).obj (CX.image.system.direct.obj d.tower))
      ⟨a, etale_evaluation_bound P.etale.PX n _ a hD⟩
    have : IsIso
        ((CY.proEvaluation.evaluation n).map ((exceptionalSystemComparison P.comparison).app
          (CX.image.system.direct.obj d.tower)) ≫
        (exceptionalProSupportEvaluation P.support n).hom.app
          (CX.image.system.inverse.obj (CX.image.system.direct.obj d.tower)) ≫
        (P.support.val.levelDerivedOpen n ⋙ (P.support.val.properDerived.level n).direct).map
          ((CX.image.inverseEvaluation n).hom.app (CX.image.system.direct.obj d.tower))) := by
      rw [comparison_evaluation CX CY P.middle P.support P.comparison]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((exceptionalProSupportEvaluation P.support n).hom.app
          (CX.image.system.inverse.obj (CX.image.system.direct.obj d.tower)) ≫
        (P.support.val.levelDerivedOpen n ⋙ (P.support.val.properDerived.level n).direct).map
          ((CX.image.inverseEvaluation n).hom.app (CX.image.system.direct.obj d.tower)))
  refine ⟨hunit, ?_⟩
  let e := asIso ((exceptionalSystemComparison P.comparison).app
      (CX.image.system.direct.obj d.tower)) ≪≫
    ((Functor.associator CX.image.system.direct CX.image.system.inverse
      (exceptionalProSupport P.support)).symm.app d.tower) ≪≫
    asIso ((exceptionalProSupport P.support).map (CX.image.system.adjunction.counit.app
      d.tower)) ≪≫ (Functor.leftUnitor (exceptionalProSupport P.support)).app d.tower
  change IsIso e.hom
  infer_instance

end WeilConjectures.CondensedExceptionalReconstruction
