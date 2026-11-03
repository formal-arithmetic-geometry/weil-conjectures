/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs

import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.UnboundedBaseChangeExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import WeilConjectures.Compactification.CommonDenseRefinement

/-!
# Base change for `Rf_!` on the localizing category

Source: the blueprint of the Weil conjectures, chapter `sec-six-functors-basics`, unit
`sk-thm-sf-comp-composition` (blueprint: det-sf-comp-composition-base-change); Stacks Project,
Tag 09AH.

The statement uses the published module-object definitions of derived pullback and derived
lower shriek, the literal compactification base-change construction, and the localizing closure
of bounded constructible finite-Tor objects. The coefficient parameter is a commutative
condensed ring satisfying the published `IsLocalizingAdmissibleCoefficient ℓ Λ` predicate.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open AlgebraicGeometry Scheme

attribute [local irreducible] derivedOpenImmersionLowerShriekUpperStarAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStarLowerStarAdjunction condensedAmbientPullbackComparison
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory condensedAmbientExchange
  upperStar lowerStar openImmersionLowerShriek
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private theorem comparison_cancel
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₁ A₂ A₀ : C} {B₁ B₂ B₀ : D}
    (φ : A₁ ⟶ A₂) (ρ₁ : A₁ ⟶ A₀) (ρ₂ : A₂ ⟶ A₀)
    (ψ : B₁ ⟶ B₂) (σ₁ : B₁ ⟶ B₀) (σ₂ : B₂ ⟶ B₀)
    (β₁ : F.obj A₁ ⟶ B₁) (β₂ : F.obj A₂ ⟶ B₂) (δ : F.obj A₀ ⟶ B₀)
    [Mono σ₂] (hφ : φ ≫ ρ₂ = ρ₁) (hψ : ψ ≫ σ₂ = σ₁)
    (h₁ : F.map ρ₁ ≫ δ = β₁ ≫ σ₁) (h₂ : F.map ρ₂ ≫ δ = β₂ ≫ σ₂) :
    F.map φ ≫ β₂ = β₁ ≫ ψ := by
  apply (cancel_mono σ₂).1
  rw [Category.assoc, ← h₂, ← Category.assoc, ← F.map_comp, hφ, h₁,
    Category.assoc, hψ]

private theorem openExchange_isIso
    {C A B E : Type*} [Category C] [Category A] [Category B] [Category E]
    (F : C ⥤ A) (G : A ⥤ C) (R : A ⥤ E) (P : C ⥤ B)
    (J : B ⥤ E) (H : E ⥤ B) (a : F ⊣ G) (b : J ⊣ H)
    (θ : G ⋙ P ≅ R ⋙ H) [IsIso a.unit]
    (hc : ∀ K, IsIso (b.counit.app (R.obj (F.obj K)))) :
    IsIso ((Functor.leftUnitor (P ⋙ J)).inv ≫
      Functor.whiskerRight a.unit (P ⋙ J) ≫
      (Functor.squareTransport F J θ).hom ≫
      Functor.whiskerLeft (F ⋙ R) b.counit ≫ (Functor.rightUnitor (F ⋙ R)).hom) := by
  have : IsIso (Functor.whiskerLeft (F ⋙ R) b.counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hc
  infer_instance

private theorem detSfOpenBaseChangeMap_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) (c : Compactification f) :
    IsIso (detSfOpenBaseChangeMap Λ f v c) := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).unit :=
    refinementOpenUnit_isIso Λ c.i
  apply openExchange_isIso
  intro K
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst c.g v)).app
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek Λ c.i) (upperStar Λ (pullback.fst c.g v))).symm.app K
  have hc := cartesianDerivedCounit Λ
    (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f v)) K
  exact (NatTrans.isIso_app_iff_of_iso _ e).mpr hc

private def commonDenseData
    {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) :
    Σ d : Compactification.DenseBoundaryCompactification f,
      (d.obj ⟶ detSfBoundaryCompactification c₁) ×
        (d.obj ⟶ detSfBoundaryCompactification c₂) := by
  obtain ⟨_, _, hqc, hd, _, _, _, _, _, _, _, h₁, h₂, _⟩ :=
    Compactification.exists_common_dense_refinement.{u, 0} f c₁ c₂
  let d : Compactification.DenseBoundaryCompactification f :=
    ⟨⟨⟨Compactification.inf c₁ c₂, hqc⟩⟩, hd⟩
  exact ⟨d, ⟨ObjectProperty.homMk
    ⟨(Compactification.infFst c₁ c₂).hom,
      (Compactification.infFst c₁ c₂).i_hom,
      (Compactification.infFst c₁ c₂).hom_g⟩, h₁⟩,
    ⟨ObjectProperty.homMk
      ⟨(Compactification.infSnd c₁ c₂).hom,
        (Compactification.infSnd c₁ c₂).i_hom,
        (Compactification.infSnd c₁ c₂).hom_g⟩, h₂⟩⟩

set_option backward.isDefEq.respectTransparency false in
local instance baseChangeOpen {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (v : Y' ⟶ Y) : IsOpenImmersion (c.baseChange v).i :=
  (c.baseChange v).isOpenImmersion

attribute [local irreducible] Compactification.inf Compactification.infFst
  Compactification.infSnd

private theorem ambientExchange_of_preservation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C D : Scheme.{u}} {g' : A ⟶ B} {p' : A ⟶ C} {p : B ⟶ D} {g : C ⟶ D}
    (sq : ChosenCartesianSquare g' p' p g)
    (hp : ProperLocalizingHypotheses Λ p) (hp' : ProperLocalizingHypotheses Λ p')
    (hg : UnboundedLocalizingPullback Λ g) (hg' : UnboundedLocalizingPullback Λ g')
    (hgen : ∀ M, (constantModelBoundedConstructible Λ B M ∧
      DerivedCategory.finiteTorAmplitude _ M) → IsIso ((condensedAmbientExchange Λ sq).app M))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B)))
    (hK : localizingClosureProEtale Λ B K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  let := condensedAmbientExchange_isoLocus_triangulated Λ sq
  exact extend_iso _
    (localizingClosure_exists Λ B
      (constantModelBoundedConstructible Λ B ⊓ fun M ↦
        DerivedCategory.finiteTorAmplitude _ M)).2.2.2.1
    _ _ (condensedAmbientExchange Λ sq) (composite_sums Λ hp hp' hg hg') hgen K hK

private theorem properExchange_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (hp' : ProperLocalizingHypotheses Λ q')
    (hv : UnboundedLocalizingPullback Λ v) (ha : UnboundedLocalizingPullback Λ a)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (hK : localizingClosureProEtale Λ Z K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  exact ambientExchange_of_preservation Λ sq
    (properLocalizingHypotheses_admissible ℓ Λ hΛ k q) hp' hv ha
    (fun M hM ↦ properBaseChange_admissible_generators ℓ Λ hΛ k q v sq M hM) K hK

private theorem admissibleProperExchange_isIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare (pullback.fst q v) (pullback.snd q v) q v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (hK : localizingClosureProEtale Λ Z K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  let : (pullback q v).Over (Spec (.of k)) :=
    ⟨pullback.snd q v ≫ (Y' ↘ Spec (.of k))⟩
  have : (pullback.snd q v).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated ((pullback q v) ↘ Spec (.of k)) := by
    change IsSeparated (pullback.snd q v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : LocallyOfFiniteType ((pullback q v) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.snd q v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact ((pullback q v) ↘ Spec (.of k)) := by
    change QuasiCompact (pullback.snd q v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have hqc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [QuasiCompact (T ↘ Spec (.of k))] : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  have hqs (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] : QuasiSeparatedSpace T :=
    quasiSeparatedSpace_of_quasiSeparated (T ↘ Spec (.of k))
  have := hqc Z
  have := hqc Y
  have := hqc Y'
  have := hqc (pullback q v)
  have := hqs Z
  have := hqs Y
  have := hqs Y'
  have := hqs (pullback q v)
  exact properExchange_admissible ℓ Λ hΛ k q v sq
    (by as_aux_lemma =>
      exact properLocalizingHypotheses_admissible ℓ Λ hΛ k (pullback.snd q v))
    (by as_aux_lemma =>
      exact (pullback_of_constructible Λ v (pullback_constructible Λ v)).some)
    (by as_aux_lemma =>
      exact (pullback_of_constructible Λ (pullback.fst q v)
        (pullback_constructible Λ (pullback.fst q v))).some) K hK

private theorem compactSupport_exchange_isIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] (_hkp : ringChar k = p) [Fact (p ≠ ℓ)]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (c : Compactification f)
    (o : D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
      detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧))
    (K : (localizingClosureProEtale Λ X).FullSubcategory) :
        localizingClosureProEtale Λ Y'
            ((detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ v).obj K.obj) ∧
          localizingClosureProEtale Λ Y'
            ((detSfDerivedPullback Λ (pullback.fst f v) ⋙
              detSfCompactSupport Λ (c.baseChange v)).obj K.obj) ∧
          IsIso ((detSfCompactSupportBaseChangeComposite Λ f v c o).app K.obj) := by
  classical
  have : Fact (ringChar k).Prime := ⟨by simpa [_hkp] using (Fact.out : p.Prime)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa [_hkp] using (Fact.out : p ≠ ℓ)⟩
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : CompactSpace Y' :=
    QuasiCompact.compactSpace_of_compactSpace (Y' ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y' :=
    quasiSeparatedSpace_of_quasiSeparated (Y' ↘ Spec (.of k))
  let : (pullback f v).Over (Spec (.of k)) :=
    ⟨pullback.snd f v ≫ (Y' ↘ Spec (.of k))⟩
  have : (pullback.snd f v).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated ((pullback f v) ↘ Spec (.of k)) := by
    change IsSeparated (pullback.snd f v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : LocallyOfFiniteType ((pullback f v) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.snd f v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact ((pullback f v) ↘ Spec (.of k)) := by
    change QuasiCompact (pullback.snd f v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : CompactSpace ↥(pullback f v : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace ((pullback f v) ↘ Spec (.of k))
  have : QuasiSeparatedSpace ↥(pullback f v : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated ((pullback f v) ↘ Spec (.of k))
  have hv := (pullback_of_constructible Λ v (pullback_constructible Λ v)).some
  have hu := (pullback_of_constructible Λ (pullback.fst f v)
    (pullback_constructible Λ (pullback.fst f v))).some
  have hc := by as_aux_lemma =>
    exact (compactification_localizing Λ ℓ k f
      (detSfBoundaryCompactification c) hΛ).1 K.obj K.property
  have hc' := by as_aux_lemma =>
    exact (compactification_localizing Λ ℓ k (pullback.snd f v)
      (detSfBoundaryCompactification (c.baseChange v)) hΛ).1 _ (hu.localizing K)
  refine ⟨hv.localizing ⟨_, hc⟩, hc', ?_⟩
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ (Y ↘ Spec (.of k))⟩
  have : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated (c.Z ↘ Spec (.of k)) := by
    change IsSeparated (c.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (c.Z ↘ Spec (.of k)) := by
    change QuasiCompact (c.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : c.i.IsOver (Spec (.of k)) := ⟨by
    change c.i ≫ c.g ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
    rw [← Category.assoc, ← c.comm]
    exact comp_over f (Spec (.of k))⟩
  have hopen := openImmersionLowerShriek_localizing ℓ k (ringChar k)
    (Nat.Prime.pos Fact.out) (Fact.out : ringChar k ≠ ℓ) Λ hΛ c.i
  obtain ⟨_, _, hi, _, _⟩ := hopen.2.2
  have hJ := by as_aux_lemma => exact hi K
  have hproper := by as_aux_lemma =>
    exact admissibleProperExchange_isIso ℓ Λ hΛ k c.g v
      (detSfProperBaseChangeSquare c.g v)
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) hJ
  exact detSfCompactSupportBaseChangeComposite_isIso_app Λ f v c o K.obj hproper

/-- Base change for compactly supported direct image on the localizing category.
Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
node det-sf-comp-composition-base-change, clauses (1)--(3)
(blueprint: det-sf-comp-composition-base-change).

The family o is normalized by the canonical open exchange arrow. For every compactification
and every object of Loc(Dctf), both values of the specified composite belong to Loc(Dctf),
and that component is invertible. These are precisely an isomorphism of the restricted
functors, since both subcategories are full. The last equation uses only the published
refinement-normalized comparisons, evaluated at K and its pullback.

Proof, following the eight DAG steps:
1. In the cartesian open square the right adjoints of v'^* j! and j'! u^* agree on sections:
V ×_X X' = V ×_Z Z', with the same coefficient action. Use open-site localization and the
module pushforward/pullback adjunctions.
2. Conjugate that identification by the open and pullback adjunctions. The resulting
isomorphism is the inverse of detSfOpenBaseChangeMap, and restricts to the identity on X'.
Exactness of pullback and extension by zero descends the construction termwise.
3. Pullback preserves Dctf, sums and its localizing closure. Open extension preserves the
closure, and compactification proper image preserves it on both bases, by
 det-sf-comp-coherence-single. Proper base change on finite, integral and rational
constructible coefficients, followed by det-proper-base-change-unbounded-extension,
makes the mate invertible on j!K. Its composite with Rp'_* of the open comparison is β.
4. Normalize derived composition by the underived compositors on K-injective resolutions.
The derived adjunction normalization and mate-pasting lemmas identify the mate for a
composite with the pasted mates used here.
5. Choose a common dense refinement of two compactifications on Y. After arbitrary base
change choose a further common dense refinement on Y'; density of the first pullback is
not assumed. Uniqueness of refinement morphisms identifies the two paths to each target.
6. The refinement/open maps and the precise base-change mate restrict to the identity on
the distinguished open (lem-sfb-base-change-identity-open-restriction). Uniqueness in
 det-sf-comp-composition-interchange equates the two maps to the further dense refinement.
7. Apply proper pushforward, precompose with the proper mate, and use naturality and
mate-pasting. This gives ρ_kₐ β_cₐ = ρ_k β_d v^*(ρ_hₐ) for each projection.
8. Cancel the invertible refinement maps and use the common-refinement formulas of
 det-sf-comp-coherence-cocycle. The resulting equation is the final displayed equality. -/
theorem det_sf_comp_composition_base_change
    (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] (_hkp : ringChar k = p) [Fact (p ≠ ℓ)]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y Y' : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))]
    [QuasiCompact (Y' ↘ Spec (.of k))] [IsSeparated (Y' ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ o : ∀ c : Compactification f,
        D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
          detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧),
      (∀ c : Compactification f, (o c).inv = detSfOpenBaseChangeMap Λ f v c) ∧
      (∀ (c : Compactification f) (K : (localizingClosureProEtale Λ X).FullSubcategory),
        localizingClosureProEtale Λ Y'
            ((detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ v).obj K.obj) ∧
          localizingClosureProEtale Λ Y'
            ((detSfDerivedPullback Λ (pullback.fst f v) ⋙
              detSfCompactSupport Λ (c.baseChange v)).obj K.obj) ∧
          IsIso ((detSfCompactSupportBaseChangeComposite Λ f v c (o c)).app K.obj)) ∧
      ∃ hU : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
          localizingClosureProEtale Λ (pullback f v)
            ((detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj),
        ∀ (c₁ c₂ : Compactification f)
          (K : (localizingClosureProEtale Λ X).FullSubcategory),
          (detSfDerivedPullback Λ v).map
              ((detSfCanonicalCompactificationComparison Λ ℓ hΛ k f c₁ c₂).hom.app K) ≫
                (detSfCompactSupportBaseChangeComposite Λ f v c₂ (o c₂)).app K.obj =
            (detSfCompactSupportBaseChangeComposite Λ f v c₁ (o c₁)).app K.obj ≫
              (detSfCanonicalCompactificationComparison Λ ℓ hΛ k (pullback.snd f v)
                (c₁.baseChange v) (c₂.baseChange v)).hom.app
                  ⟨(detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj, hU K⟩ := by
  classical
  have : Fact (ringChar k).Prime := ⟨by simpa [_hkp] using (Fact.out : p.Prime)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa [_hkp] using (Fact.out : p ≠ ℓ)⟩
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : CompactSpace Y' :=
    QuasiCompact.compactSpace_of_compactSpace (Y' ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y' :=
    quasiSeparatedSpace_of_quasiSeparated (Y' ↘ Spec (.of k))
  let : (pullback f v).Over (Spec (.of k)) :=
    ⟨pullback.snd f v ≫ (Y' ↘ Spec (.of k))⟩
  have : (pullback.snd f v).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsSeparated ((pullback f v) ↘ Spec (.of k)) := by
    change IsSeparated (pullback.snd f v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : LocallyOfFiniteType ((pullback f v) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.snd f v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact ((pullback f v) ↘ Spec (.of k)) := by
    change QuasiCompact (pullback.snd f v ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : CompactSpace ↥(pullback f v : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace ((pullback f v) ↘ Spec (.of k))
  have : QuasiSeparatedSpace ↥(pullback f v : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated ((pullback f v) ↘ Spec (.of k))
  have hv := (pullback_of_constructible Λ v (pullback_constructible Λ v)).some
  have hu := (pullback_of_constructible Λ (pullback.fst f v)
    (pullback_constructible Λ (pullback.fst f v))).some
  let o : ∀ c : Compactification f,
      D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g v) ≅
        detSfDerivedPullback Λ (pullback.fst f v) ⋙ D(((c.baseChange v).i)_!open⟦Λ⟧) :=
    fun c ↦
    @asIso _ _ _ _ (detSfOpenBaseChangeMap Λ f v c)
      (detSfOpenBaseChangeMap_isIso Λ f v c) |>.symm
  refine ⟨o, fun c ↦ rfl, ?_, hu.localizing, ?_⟩
  · intro c K
    exact compactSupport_exchange_isIso ℓ p k _hkp Λ f v hΛ c (o c) K
  · intro c₁ c₂ K
    let r := commonDenseData f c₁ c₂
    let d := r.1
    let h₁ := r.2.1
    let h₂ := r.2.2
    let s := commonDenseData (pullback.snd f v) (c₁.baseChange v) (c₂.baseChange v)
    let e := s.1
    let e₁ := s.2.1
    let e₂ := s.2.2
    let z := commonDenseData (pullback.snd f v) e.obj.obj.obj (d.obj.obj.obj.baseChange v)
    let w := z.1
    let t := z.2.1
    let hd := z.2.2
    let k₁ : w.obj ⟶ detSfBoundaryCompactification (c₁.baseChange v) := t ≫ e₁
    let k₂ : w.obj ⟶ detSfBoundaryCompactification (c₂.baseChange v) := t ≫ e₂
    have hφ := detSfCanonicalCompactificationComparison_refinement Λ ℓ hΛ k f
      c₁ c₂ d h₁ h₂ K
    have hφ' := detSfCanonicalCompactificationComparison_refinement Λ ℓ hΛ k
      (pullback.snd f v) (c₁.baseChange v) (c₂.baseChange v) w k₁ k₂
      ⟨_, hu.localizing K⟩
    have hiso := detSfCompactificationRefinement_isIso Λ ℓ hΛ k (pullback.snd f v)
      (c₂.baseChange v) w k₂ ⟨_, hu.localizing K⟩
    have : IsIso (compactificationRefinementComponent Λ k₂
        ((detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj)) := hiso
    have b₁ := compactSupportRefinement_baseChange Λ f v o (fun c ↦ rfl)
      c₁ d h₁ w hd k₁ K.obj
    have b₂ := compactSupportRefinement_baseChange Λ f v o (fun c ↦ rfl)
      c₂ d h₂ w hd k₂ K.obj
    exact comparison_cancel (detSfDerivedPullback Λ v)
      ((detSfCanonicalCompactificationComparison Λ ℓ hΛ k f c₁ c₂).hom.app K)
      (compactificationRefinementComponent Λ h₁ K.obj)
      (compactificationRefinementComponent Λ h₂ K.obj)
      ((detSfCanonicalCompactificationComparison Λ ℓ hΛ k (pullback.snd f v)
        (c₁.baseChange v) (c₂.baseChange v)).hom.app ⟨_, hu.localizing K⟩)
      (compactificationRefinementComponent Λ k₁
        ((detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj))
      (compactificationRefinementComponent Λ k₂
        ((detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj))
      ((detSfCompactSupportBaseChangeComposite Λ f v c₁ (o c₁)).app K.obj)
      ((detSfCompactSupportBaseChangeComposite Λ f v c₂ (o c₂)).app K.obj)
      ((detSfCompactSupportBaseChangeComposite Λ f v d.obj.obj.obj
          (o d.obj.obj.obj)).app K.obj ≫
        compactificationRefinementComponent Λ hd
          ((detSfDerivedPullback Λ (pullback.fst f v)).obj K.obj)) hφ hφ'
      (by simpa only [Category.assoc] using b₁)
      (by simpa only [Category.assoc] using b₂)

attribute [local irreducible] detSfCompactSupportBaseChangeComposite
  detSfCanonicalCompactificationComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.ProEtale.CondensedRing
