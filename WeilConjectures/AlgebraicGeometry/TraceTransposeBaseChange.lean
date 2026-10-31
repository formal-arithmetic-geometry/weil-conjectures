/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.CanonicalFiniteLevelCompactSupportBaseChange
public import WeilConjectures.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Base change of a unit-valued trace transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, comparison of the trace normalizations
(blueprint: lem-pur-trace-transpose-base-change).

The bounded constructible pro-etale input is retained together with every etale-origin
isomorphism. Traces are expressed in the canonical etale coordinates of the relative
exceptional Hom bijection. The transpose is transported back to the original input.
The dualizing base-change map is the specified counit mate, with the canonical pullback
comparison; no inverse of that map, smoothness or Tate identification is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison between comparison followed by derived pullback and
etale derived pullback followed by comparison. Source: the finite-coefficient comparison
coordinates of def-pur-co-smoothness and the trace comparison in the current blueprint
(blueprint: lem-pur-trace-transpose-base-change). -/
def purityTracePullbackComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory :=
  derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} P.Coefficient) a

/-- The actual exceptional adjunction transpose, in comparison coordinates, conjugated
back to the original pro-etale object by its retained origin isomorphism. Source: the
trace transpose in the current blueprint, using the relative Hom bijection of
thm-sf-ambient-adjoint-class (blueprint: lem-pur-trace-transpose-base-change). -/
def purityTraceTranspose (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K ≅ L)
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K ⟶ 𝟙_ _) :
    L ⟶ finiteComparedDualizing P f :=
  e.inv ≫ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
    ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).homEquiv K (𝟙_ _) t)

/-- The origin of the pullback of the original input, using the canonical pullback
comparison and the pullback of the specified origin isomorphism. Source: current
blueprint, trace base-change square (blueprint: lem-pur-trace-transpose-base-change). -/
def purityTracePullbackOrigin (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X' : Scheme.{u}} (a : X' ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (e : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K ≅ L) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.obj
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K) ≅
      (upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj L :=
  ((purityTracePullbackComparison P a).app K).symm ≪≫
    (upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.mapIso e

/-- The dualizing base-change map B: canonical pullback comparison followed by comparison
of the etale counit-defined mate. Its etale factor is the transpose of inverse compact
support exchange followed by pullback of the counit and the coefficient-unit comparison,
exactly as in def-pur-co-smoothness. Source: current blueprint, trace comparison
(blueprint: lem-pur-trace-transpose-base-change). -/
def purityTraceDualizingBaseChange (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f b) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj
        (finiteComparedDualizing P f) ⟶ finiteComparedDualizing P f' :=
  (purityTracePullbackComparison P a).hom.app (Etale.dualizingComplex P.Coefficient f) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
      (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)

/-- Naturality of transposes across a mate, followed by a target morphism.
Source: Mathlib's unit_mateEquiv and the naturality of the mate. Expand both
transposes using the units, move the mapped trace past the mate, and apply the
unit-mate identity. -/
private theorem trace_mate
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (ad₁ : L₁ ⊣ R₁) (ad₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    {K : C} {N : D} {N' : F} (t : L₁.obj K ⟶ N) (v : H.obj N ⟶ N') :
    ad₂.homEquiv _ _ (α.app K ≫ H.map t ≫ v) =
      G.map (ad₁.homEquiv _ _ t) ≫ (mateEquiv ad₁ ad₂ α).app N ≫ R₂.map v := by
  have hn := (mateEquiv ad₁ ad₂ α).naturality t
  dsimp only [Functor.comp_map] at hn
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% unit_mateEquiv ad₁ ad₂ α K]

/-- A compact-support-base-change-compatible trace has transpose B composed with the
pullback of its original transpose. Source: current blueprint, comparison of the two
integration normalizations in lem-pur-projection-purity-agreement.proof.md
(blueprint: lem-pur-trace-transpose-base-change).

Proof: (1) In the retained etale coordinates, the transpose is the actual homEquiv
of the exceptional adjunction; its comparison pullback is conjugated by e.inv.
(2) Finite coefficients make compact-support exchange invertible. Precompose the trace
compatibility equation with its inverse to express t' as inverse exchange, pullback
of t, and the unit comparison (thm-cbc-finite-level-proetale).
(3) Expand the adjunction Hom bijections using their units. Naturality of the mate
at t and the unit-mate identity CategoryTheory.unit_mateEquiv
(lem-pur-mate-unit-compatibility) identify its transpose with pullback of the
original transpose followed by the exceptional base-change mate and the mapped unit
comparison. This composite is Etale.dualizingComplexBaseChangeMap by definition.
(4) Apply comparison pullback. Naturality of purityTracePullbackComparison at the
etale transpose and functoriality of the pulled-back e.inv give the asserted equality
on the original pullback of L. This uses no ambient pro-etale adjunction. -/
theorem purityTraceTranspose_baseChange (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))] [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))] [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback a f' f b) :
    letI := (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
    letI := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
    letI : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    ∀ (L : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (_hL : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) X L)
      (K : _root_.DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K ≅ L)
      (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj K ⟶ 𝟙_ _)
      (t' : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f').obj
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K) ⟶ 𝟙_ _),
      (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq).app K ≫ t' =
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map t ≫
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom →
      purityTraceTranspose P f'
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj K)
          ((upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.obj L)
          (purityTracePullbackOrigin P a K L e) t' =
        (upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
          (purityTraceTranspose P f K L e t) ≫ purityTraceDualizingBaseChange P sq := by
  let := (P.finiteComparedCompactification f (Y ↘ Spec (.of P.field.k))).hasCompactification
  let := ((HasCompactification.compactification f).ofIsPullback sq).hasCompactification
  let : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  intro L _hL K e t t' ht
  let Ex := Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  let := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  have ht' : t' = (inv Ex).app K ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.map t ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom := by
    rw [← ht]
    simp [Ex]
  have hm := trace_mate
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f')
    (TwoSquare.mk _ _ _ _ (inv Ex)) t
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) b).hom
  rw [← ht'] at hm
  change (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f').homEquiv _ _ t' =
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
      ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).homEquiv _ _ t) ≫
        Etale.dualizingComplexBaseChangeMap P.Coefficient sq at hm
  simp only [purityTraceTranspose, purityTraceDualizingBaseChange,
    purityTracePullbackOrigin, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.map_comp, hm, Category.assoc, Iso.app_hom]
  unfold finiteComparedDualizing
  have hn := (purityTracePullbackComparison P a).hom.naturality
    ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).homEquiv _ _ t)
  simpa only [finiteComparedDualizing, Etale.dualizingComplex, Functor.comp_map,
    Category.assoc] using congrArg
    (fun m ↦ (upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map e.inv ≫
      m ≫ (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
        (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)) hn.symm

end AlgebraicGeometry.ProEtale
