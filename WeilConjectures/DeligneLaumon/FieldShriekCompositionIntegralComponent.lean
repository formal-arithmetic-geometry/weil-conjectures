/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.DeligneLaumon.QcqsCompletedRefinement
import WeilConjectures.DeligneLaumon.CompletedCompositionTowerIsIso
import WeilConjectures.DeligneLaumon.CompletedCompositionTowerIndependence
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.Compactification.Refinement
import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.CompletedCompositionTowerIndependenceLegacy
public import WeilConjectures.SixFunctors.CompletedCompositionTowerIsIsoLegacy

/-! # Normalized components of the integral field shriek compositor

Source: Stacks Project, Tag 0F7J, and Bhatt--Scholze Definition 6.7.6
(blueprint: lem-zl-field-shriek-integral-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The proper/open normalization at one input. Its equation is exactly the
component equation of `SfIntegralCompositionSpec`; it asserts no naturality in the input.
Source: Stacks 0F7J (blueprint: lem-zl-field-shriek-integral-component). -/
def SfIntegralCompositionComponentSpec
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (a : (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K)
      ⟶ (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E).obj K)
    : Prop :=
  ∀ (d : Compactification g) (e : Compactification (f ≫ d.i))
    (rf : e.restrict.Refinement cf) (rg : d.Refinement cg)
    (rfg : (d.comp e).Refinement cfg),
  ∃ hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj)),
  ∃ hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj) hη),
  ∃ (ρf : (image (completed l E) e.restrict).obj K.obj ≅
      (image (completed l E) cf).obj K.obj)
    (ρg : (image (completed l E) d).obj
        ((image (completed l E) e.restrict).obj K.obj) ≅
      (image (completed l E) cg).obj ((image (completed l E) e.restrict).obj K.obj))
    (ρfg : (image (completed l E) (d.comp e)).obj K.obj ≅
      (image (completed l E) cfg).obj K.obj),
    SfCompletedRefinementSpec l E rf K.obj ρf ∧
    SfCompletedRefinementSpec l E rg ((image (completed l E) e.restrict).obj K.obj) ρg ∧
    SfCompletedRefinementSpec l E rfg K.obj ρfg ∧
    a.hom =
      (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cg).inv.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K) ≫
        (image (completed l E) cg).map
          ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cf).inv.app K) ≫
        (image (completed l E) cg).map ρf.inv ≫ ρg.inv ≫
        sfCompletedCompositionOnTower l E d e K.obj hη hLambda ≫ ρfg.hom ≫
        (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cfg).hom.app K

private theorem exists_refining_tower :
    ∃ (d : Compactification g) (e : Compactification (f ≫ d.i)),
      Nonempty (e.restrict.Refinement cf) ∧ Nonempty (d.Refinement cg) ∧
        Nonempty ((d.comp e).Refinement cfg) := by
  have : QuasiCompact cg.i := cg.quasiCompact_openImmersion inferInstance
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace Z := inferInstance
  have : CompactSpace cg.Z := QuasiCompact.compactSpace_of_compactSpace cg.g
  have : QuasiSeparatedSpace cg.Z := quasiSeparatedSpace_of_quasiSeparated cg.g
  obtain ⟨t, ht⟩ := exists_isDense_compactification (cf.g ≫ cg.i)
  have : IsSchemeTheoreticallyDominant t.i := ht
  have : QuasiCompact t.i := t.quasiCompact_openImmersion inferInstance
  let e₀ : Compactification (f ≫ cg.i) :=
    (t.precomp cf.i).copy
      ((congrArg (fun h : X ⟶ Y ↦ h ≫ cg.i) cf.comm).trans (Category.assoc _ _ _))
  let T : Compactification.Triangle f g :=
    { cf := cf, cg := cg, cfg := cg.comp e₀, q := t.i, p := t.g,
      i_q := rfl, p_g := rfl,
      isPullback := t.isPullback_of_isProper_of_isSchemeTheoreticallyDominant }
  obtain ⟨e₁, v, hv, hvi, hvg, _⟩ :=
    (exists_compactifiable_compatible_tower f g cg cfg).1
  let e := Compactification.inf e₀ e₁
  let r₀ := Compactification.infFst e₀ e₁
  let r₁ := Compactification.infSnd e₀ e₁
  let rf : e.restrict.Refinement cf :=
    T.homOfRestrictRf cg (Compactification.Refinement.id cg) e r₀.hom r₀.i_hom
      (by change e.g ≫ 𝟙 cg.Z = r₀.hom ≫ e₀.g
          exact (Category.comp_id _).trans r₀.hom_g.symm)
  let rfg : (cg.comp e).Refinement cfg :=
    { hom := r₁.hom ≫ v,
      i_hom := by
        change e.i ≫ (r₁.hom ≫ v) = cfg.i
        rw [← Category.assoc, r₁.i_hom]
        exact hvi,
      hom_g := by
        change (r₁.hom ≫ v) ≫ cfg.g = e.g ≫ cg.g
        rw [Category.assoc, hvg, ← Category.assoc, r₁.hom_g] }
  exact ⟨cg, e, ⟨rf⟩, ⟨Compactification.Refinement.id cg⟩, ⟨rfg⟩⟩

private theorem completed_image_constructible
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Compactification f) (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E Y ((image (completed l E) c).obj K.obj) := by
  have := sfIntegralConstructible_isClosedUnderIsomorphisms l E Y
  exact ObjectProperty.prop_of_iso _
    ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) c).app K).symm
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (coefficientPrimeUnit l D hl) c E).obj K).property

/-- There is a uniquely normalized isomorphism at each integral constructible input.
Source: Stacks 0F7J, compatible compactifications and independence of choices;
Bhatt--Scholze Definition 6.7.6 and Lemmas 6.7.7, 6.1.13
(blueprint: lem-zl-field-shriek-integral-component).

Proof: choose a compatible tower refining the supplied compactifications. On its
proper/open square construct Lambda from restriction exchange and the inverse open unit.
Its inverse open adjunct Gamma is invertible: its finite reductions are the finite
proper/open isomorphisms, and its cone is complete with zero reductions. Whisker Gamma
by the outer proper and open functors, insert their compositors, and conjugate by the
normalized refinement and Roos isomorphisms. All these factors are actual isomorphisms.
For any second tower, take a common refining tower and equalize its parallel refinement
arrows. Proper/open mate pasting and refinement coherence identify the two conjugates.
This proves the displayed normalization on every tower. Conversely that equation on
one such refining tower fixes the component, since the normalized refinements are
unique by the open adjunction and all conjugating factors are invertible. Faithfulness
of the full-subcategory inclusion and Iso.ext give uniqueness. This statement concerns
one input only and does not assert the naturality needed to assemble a functor iso. -/
theorem sfFieldShriekCompositionIntegral_component
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X) :
    ∃! a : (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K)
      ≅ (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E).obj K,
      SfIntegralCompositionComponentSpec D l hl cf cg cfg E K a.hom := by
  obtain ⟨d, e, ⟨rf⟩, ⟨rg⟩, ⟨rfg⟩⟩ := exists_refining_tower D cf cg cfg
  obtain ⟨hη, hLambda, hcomp⟩ := sfCompletedCompositionOnTower_isIso_legacy l E D.k
    (coefficientPrimeUnit l D hl) d e K
  obtain ⟨ρf, hf⟩ := sfQcqsCompletedRefinement_exists l E D.k
    (coefficientPrimeUnit l D hl) rf K
  let L : sfIntegralConstructibleCategory l E Y :=
    ⟨(image (completed l E) e.restrict).obj K.obj,
      completed_image_constructible D l hl E e.restrict K⟩
  obtain ⟨ρg, hg⟩ := sfQcqsCompletedRefinement_exists l E D.k
    (coefficientPrimeUnit l D hl) rg L
  obtain ⟨ρfg, hfg⟩ := sfQcqsCompletedRefinement_exists l E D.k
    (coefficientPrimeUnit l D hl) rfg K
  let t := sfCompletedCompositionTransport_legacy l E cf cg cfg K.obj d e hη hLambda ρf ρg ρfg
  have : IsIso t := by
    have := hcomp
    dsimp only [t, sfCompletedCompositionTransport_legacy]
    infer_instance
  let sourceIso :=
    (image (completed l E) cg).mapIso
      ((sfQcqsCompactSupportRealization l E D.k
        (coefficientPrimeUnit l D hl) cf).app K) ≪≫
      (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cg).app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (coefficientPrimeUnit l D hl) cf E).obj K)
  let targetIso :=
    (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cfg).app K
  let a := (sfIntegralConstructible l E Z).isoMk
    (sourceIso.symm ≪≫ asIso t ≪≫ targetIso)
  have normalization
      (b : (sfCompactSupportFiniteIntegralFunctor l D.k
          (coefficientPrimeUnit l D hl) cg E).obj
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (coefficientPrimeUnit l D hl) cf E).obj K) ⟶
        (sfCompactSupportFiniteIntegralFunctor l D.k
          (coefficientPrimeUnit l D hl) cfg E).obj K) :
      SfIntegralCompositionComponentSpec D l hl cf cg cfg E K b ↔
        b.hom = sourceIso.inv ≫ t ≫ targetIso.hom := by
    constructor
    · intro hb
      obtain ⟨hη', hLambda', ρf', ρg', ρfg', hf', hg', hfg', hb⟩ := hb d e rf rg rfg
      have h := sfCompletedCompositionTransport_independent_legacy l E D.k
        (coefficientPrimeUnit l D hl) cf cg cfg K
        d e rf rg rfg hη' hLambda' ρf' ρg' ρfg' hf' hg' hfg'
        d e rf rg rfg hη hLambda ρf ρg ρfg hf hg hfg
      calc
        b.hom = sourceIso.inv ≫ sfCompletedCompositionTransport_legacy l E cf cg cfg K.obj
            d e hη' hLambda' ρf' ρg' ρfg' ≫ targetIso.hom := by
          simpa only [sourceIso, targetIso, Iso.trans_inv, Functor.mapIso_inv,
            Iso.app_inv, Iso.app_hom, sfCompletedCompositionTransport_legacy,
            Category.assoc] using hb
        _ = sourceIso.inv ≫ t ≫ targetIso.hom :=
          congrArg (fun z ↦ sourceIso.inv ≫ z ≫ targetIso.hom) h
    · intro hb d' e' rf' rg' rfg'
      obtain ⟨hη', hLambda', _⟩ := sfCompletedCompositionOnTower_isIso_legacy l E D.k
        (coefficientPrimeUnit l D hl) d' e' K
      obtain ⟨ρf', hf'⟩ := sfQcqsCompletedRefinement_exists l E D.k
        (coefficientPrimeUnit l D hl) rf' K
      let L' : sfIntegralConstructibleCategory l E Y :=
        ⟨(image (completed l E) e'.restrict).obj K.obj,
          completed_image_constructible D l hl E e'.restrict K⟩
      obtain ⟨ρg', hg'⟩ := sfQcqsCompletedRefinement_exists l E D.k
        (coefficientPrimeUnit l D hl) rg' L'
      obtain ⟨ρfg', hfg'⟩ := sfQcqsCompletedRefinement_exists l E D.k
        (coefficientPrimeUnit l D hl) rfg' K
      refine ⟨hη', hLambda', ρf', ρg', ρfg', hf', hg', hfg', ?_⟩
      have h := sfCompletedCompositionTransport_independent_legacy l E D.k
        (coefficientPrimeUnit l D hl) cf cg cfg K
        d e rf rg rfg hη hLambda ρf ρg ρfg hf hg hfg
        d' e' rf' rg' rfg' hη' hLambda' ρf' ρg' ρfg' hf' hg' hfg'
      rw [hb, show t = _ from h]
      simp only [sourceIso, targetIso, Iso.trans_inv, Functor.mapIso_inv,
        Iso.app_inv, Iso.app_hom, sfCompletedCompositionTransport_legacy, Category.assoc]
  refine ⟨a, (normalization a.hom).mpr ?_, ?_⟩
  · rfl
  · intro b hb
    apply Iso.ext
    apply (sfIntegralConstructible l E Z).ι.map_injective
    exact (normalization b.hom).mp hb

omit [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))] in
include D in
include D hl in
end WeilConjectures
