/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import all WeilConjectures.SixFunctors.Integral.IntegralProperOperationProjection
import all WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionReduction
import all WeilConjectures.SixFunctors.Integral.IntegralOrdinaryTensorPullbackNormalization
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorNaturality
import WeilConjectures.SixFunctors.Integral.IntegralOrdinaryProjectionArrowComparison

/-! # The integral proper counit projection

Source: BS 6.8.14--6.8.15 and the integral projection reconstruction.
(blueprint: lem-sf-integral-finite-tor-proper-projection-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem fieldDimension (k : Type u) [Field k] (W : Scheme.{u})
    [W.Over (Spec (.of k))] [LocallyOfFiniteType (W ↘ Spec (.of k))]
    [QuasiCompact (W ↘ Spec (.of k))] :
    ∃ n : ℕ, topologicalKrullDim W ≤ n := by
  have hd := topologicalKrullDim_lt_top_of_finiteType (W ↘ Spec (.of k))
  obtain h | h := eq_or_ne (topologicalKrullDim W) ⊥
  · exact ⟨0, by simp only [h, bot_le]⟩
  · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h
    rw [← ha] at hd ⊢
    change (a : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) at hd
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (WithBot.coe_lt_coe.mp hd).ne
    exact ⟨n, by rw [← hn]; exact le_rfl⟩

private theorem fieldUnit (l : ℕ) (k : Type u) [Field k] (hl : IsUnit (l : k))
    (W : Scheme.{u}) [W.Over (Spec (.of k))] : IsUnit (l : Γ(W, ⊤)) := by
  let ρ := (Scheme.ΓSpecIso (.of k)).inv ≫ (W ↘ Spec (.of k)).appTop
  simpa only [map_natCast] using hl.map ρ.hom

private theorem finiteTorReductions
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (aX : SfProEtaleProjection.TensorModel l E X)
    (aZ : SfProEtaleProjection.TensorModel l E c.Z)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y)
    (hL : finiteTorConstructibleIntegral l E Y L.obj) (n : ℕ) :
    IsIso ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E)
        c aX aZ aY (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app
          L.obj)) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨e⟩ := integralOrdinaryProjection_reduction_arrowComparison l E c aX aZ aY
    K.obj L.obj n
  obtain ⟨a, b, _, ht⟩ := hL.2
  exact isIso_of_arrow_iso e (fixed_projection (Padic.coefficientExtensionRing l E (n + 1))
    c _ _ (integral_origin l E X K n) (integral_origin l E Y L n) a b
      (fixed_tor (Padic.coefficientExtensionRing l E (n + 1)) Y _ a b (ht n)))

private theorem finiteTorCompactProjection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aZ : SfProEtaleProjection.TensorModel l E c.Z)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y)
    (hL : finiteTorConstructibleIntegral l E Y L.obj) :
    IsIso (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E)
      c aX aZ aY (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app L.obj) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  have hp := SfProEtaleProjection.pull_domains l E f
    (fieldDimension k X) (fieldDimension k Y)
    (fieldUnit l k hl X)
    (fieldUnit l k hl Y) L.obj L.property
  have hi := SfProEtaleProjection.tensor_domains l E X
    (fieldUnit l k hl X) aX K.obj _ K.property hp
  have support (A : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj A.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E k
        hl c).app A).symm
      ((sfCompactSupportFiniteIntegralFunctor l k
        hl c E).obj A).property
  have hs := SfProEtaleProjection.tensor_domains l E Y
    (fieldUnit l k hl Y) aY _ _ (support K) L.property
  exact sfIntegralReduction_conservative l E Y _ hs.1 (support ⟨_, hi.1⟩)
    (finiteTorReductions l E c aX aZ aY K L hL)

private theorem finiteTorOrdinaryProperProjection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (M : sfIntegralConstructibleCategory l E X)
    (N : sfIntegralConstructibleCategory l E Y)
    (hN : finiteTorConstructibleIntegral l E Y N.obj) :
    IsIso ((((proEtaleRingDerivedAdjunction p
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull p)).rightAdjointProjectionMap
        (ordinaryCurriedTensorPullback (PurCompactSupport.completed l E) p aX aY).hom
      ).app M.obj).app N.obj) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let R := PurCompactSupport.completed l E
  let c := Compactification.ofIsProper p
  let J := (PurCompactSupport.openExtension R (𝟙 X)).mapDerivedCategory
  let F := PurCompactSupport.pull R (𝟙 X)
  let adjJ := PurCompactSupport.openDerivedAdjunction R (𝟙 X)
  let : J.IsEquivalence := identityOpenEquivalence X (R.ring X) (R.pull (𝟙 X))
  let e : J.obj (F.obj M.obj) ≅ M.obj :=
    J.mapIso ((adjJ.rightAdjointUniq (Functor.adjunction J)).app M.obj) ≪≫
      J.asEquivalence.counitIso.app M.obj
  have hK : sfIntegralConstructible l E X (F.obj M.obj) :=
    SfProEtaleProjection.pull_domains l E (𝟙 X)
      (fieldDimension k X) (fieldDimension k X)
      (fieldUnit l k hl X)
      (fieldUnit l k hl X) M.obj M.property
  let K : sfIntegralConstructibleCategory l E X := ⟨_, hK⟩
  have hc := finiteTorCompactProjection l E k hl p c aX aX aY K N hN
  let d := (PurCompactSupport.projectionComparisons_existsUnique R c aX aX aY
    (PurCompactSupport.completedPull_comp l E c.i c.g)).exists.choose
  let adj := proEtaleRingDerivedAdjunction p (R.ring Y) (R.ring X) (R.pull p)
  let phi := (ordinaryCurriedTensorPullback R p aX aY).hom
  have hd : d.tensorPullback.hom = phi := by
    ext A B
    exact d.tensorPullback_eq A B
  have hp : IsIso (((adj.rightAdjointProjectionMap d.tensorPullback.hom).app
      (J.obj K.obj)).app N.obj) := by
    let g := (PurCompactSupport.push R p).mapIso ((d.openProjection.app K.obj).app N.obj)
    change IsIso ((((adj.rightAdjointProjectionMap d.tensorPullback.hom).app
      (J.obj K.obj)).app N.obj) ≫ g.hom) at hc
    let := hc
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ g.hom g.isIso_hom hc
  rw [hd] at hp
  exact (NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight (adj.rightAdjointProjectionMap phi)
      ((CategoryTheory.evaluation _ _).obj N.obj)) e).mp hp

private theorem ordinaryProperConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (M : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E Y
      ((PurCompactSupport.push (PurCompactSupport.completed l E) f).obj M.obj) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let R := PurCompactSupport.completed l E
  let c := Compactification.ofIsProper f
  let J := (PurCompactSupport.openExtension R (𝟙 X)).mapDerivedCategory
  let F := PurCompactSupport.pull R (𝟙 X)
  let adjJ := PurCompactSupport.openDerivedAdjunction R (𝟙 X)
  let : J.IsEquivalence := identityOpenEquivalence X (R.ring X) (R.pull (𝟙 X))
  let e : J.obj (F.obj M.obj) ≅ M.obj :=
    J.mapIso ((adjJ.rightAdjointUniq (Functor.adjunction J)).app M.obj) ≪≫
      J.asEquivalence.counitIso.app M.obj
  have hM : sfIntegralConstructible l E X (F.obj M.obj) :=
    SfProEtaleProjection.pull_domains l E (𝟙 X)
      (fieldDimension k X) (fieldDimension k X)
      (fieldUnit l k hl X) (fieldUnit l k hl X) M.obj M.property
  let N : sfIntegralConstructibleCategory l E X := ⟨_, hM⟩
  have hs : sfIntegralConstructible l E Y ((PurCompactSupport.image R c).obj N.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E k hl c).app N).symm
      ((sfCompactSupportFiniteIntegralFunctor l k hl c E).obj N).property
  exact (sfIntegralConstructible l E Y).prop_of_iso
    ((PurCompactSupport.push R f).mapIso e) hs

/-- Invertibility of the proper counit factor before scalar localization.
Source: thm-sf-pf-adic.proof.md, finite-level projection and reconstruction;
BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-integral-finite-tor-proper-projection-invertible).

Proof: the finite-Tor hypotheses provide uniform Tor intervals for the positive
coefficient quotients, and integral constructibility supplies uniform cohomology
bounds and constructibility of every reduction. Realize those
reductions by bounded constructible etale complexes and apply the finite proper
projection formula. The canonical reduction comparison carries the completed
integral counit projection to these finite projections, because quotient tensor,
pullback, and direct image comparisons preserve the adjunction counit and the
pullback/tensor comparison. The two integral endpoints are derived complete and
constructible. Conservativity of finite reduction on complete complexes therefore
makes the integral projection invertible. For the compact-support formulation use
the compactification (identity,f); identity open extension is an equivalence and
its projection cancels. Finally the unique right-adjoint comparison identifies
any supplied adjunction with this constructed direct-image adjunction, intertwines
their counits, and conjugates their projection arrows through isomorphisms.
The finite-Tor hypotheses are used only for the finite projection theorem.
This uses finite type over the given field only; no finite-field or algebraic
closure hypothesis is needed. Empty schemes and zero complexes obey the same
reduction and cancellation argument. -/
theorem integralFiniteTorProperProjection_isIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (G : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (a : constructibleIntegralPullback l E f ⊣ G)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y)
    (hK : finiteTorConstructibleIntegral l E X K.obj)
    (hL : finiteTorConstructibleIntegral l E Y L.obj) :
    IsIso (a.homEquiv _ _ ((canonicalIntegralPullbackTensor l E f (G.obj K) L).hom ≫
      (constructibleIntegralTensor l E X).map (Prod.mkHom (a.counit.app K) (𝟙 _)))) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  let F := constructibleIntegralPullback l E f
  let TX := Functor.currying.inverse.obj (constructibleIntegralTensor l E X)
  let TY := Functor.currying.inverse.obj (constructibleIntegralTensor l E Y)
  let e := integralComparisonIso l E f
  let φ : (Functor.postcompose₂.obj F).obj TY ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TX :=
    by
      let e' := Functor.currying.inverse.mapIso e
      change Functor.curry.obj (constructibleIntegralTensor l E Y ⋙ F) ≅
        Functor.curry.obj (F.prod F ⋙ constructibleIntegralTensor l E X) at e'
      have es : Functor.curry.obj (constructibleIntegralTensor l E Y ⋙ F) =
          (Functor.postcompose₂.obj F).obj (Functor.curry.obj
            (constructibleIntegralTensor l E Y)) := by
        refine CategoryTheory.Functor.ext (fun A => ?_) (fun A B g => ?_)
        · refine CategoryTheory.Functor.ext (fun B => rfl) (fun B C g => ?_)
          dsimp [Functor.curryObj, Functor.comp_map]
          simp only [Category.id_comp, Category.comp_id]
        · dsimp [Functor.curryObj, Functor.postcompose₂, Functor.whiskeringRight,
            Functor.whiskerRight]
          ext C
          simp only [Category.id_comp, Category.comp_id]
          rfl
      exact eqToIso es ≪≫ e' ≪≫
        (Functor.curryObjProdComp F F (constructibleIntegralTensor l E X))
  have hφ (M N : sfIntegralConstructibleCategory l E Y) :
      (φ.hom.app M).app N = (canonicalIntegralPullbackTensor l E f M N).hom := by
    simpa [φ, Functor.curryObjProdComp, Functor.currying, Functor.postcompose₂,
      Functor.whiskeringRight, Functor.whiskeringLeft, Functor.whiskeringLeft₂,
      Functor.whiskerRight, Functor.whiskerLeft, Functor.curry_obj_obj_obj,
      Functor.comp_obj, Functor.curry_obj_map_app, Functor.curry_obj_obj_map,
      Functor.comp_map, Functor.prod_map, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Iso.trans_hom, Iso.refl_hom,
      NatIso.ofComponents_hom_app] using
      congrArg Iso.hom (integralComparisonIso_app l E f M N)
  obtain ⟨c, m, n, hc⟩ := canonicalCoordinates l E f
    (fieldDimension k X) (fieldDimension k Y) (fieldUnit l k hl X) (fieldUnit l k hl Y)
    F TX TY φ rfl rfl rfl (fun M N ↦ heq_of_eq (hφ M N))
  let I := (sfIntegralConstructible l E Y).ι
  let J := (sfIntegralConstructible l E X).ι
  let R := PurCompactSupport.completed l E
  let adj := proEtaleRingDerivedAdjunction f (R.ring Y) (R.ring X) (R.pull f)
  let G₀ := (sfIntegralConstructible l E Y).lift (J ⋙ PurCompactSupport.push R f)
    (fun M ↦ ordinaryProperConstructible l E k hl f M)
  let b₀ : J ⋙ PurCompactSupport.push R f ≅ G₀ ⋙ I := Iso.refl _
  let adj₀ : F ⊣ G₀ := adj.restrictFullyFaithful
    (sfIntegralConstructible l E Y).fullyFaithfulι
    (sfIntegralConstructible l E X).fullyFaithfulι c b₀
  let b : J ⋙ PurCompactSupport.push R f ≅ G ⋙ I :=
    b₀ ≪≫ Functor.isoWhiskerRight (a.rightAdjointUniq adj₀).symm I
  have hp := finiteTorOrdinaryProperProjection l E k hl f
    (IntegralOrdinary.tensorModel l E X) (IntegralOrdinary.tensorModel l E Y) K L hL
  have h := projectionIsoOfRestriction a adj
    (sfIntegralConstructible l E Y).fullyFaithfulι
    (sfIntegralConstructible l E X).fullyFaithfulι c b φ.hom _ m n hc K L hp
  rw [Adjunction.rightAdjointProjectionMap_app_app] at h
  rw [hφ] at h
  simpa only [F, TX, TY, Functor.currying, Functor.postcompose₂,
    Functor.whiskeringRight, Functor.whiskeringLeft, Functor.whiskeringLeft₂,
    Functor.whiskerRight, Functor.whiskerLeft, Functor.curry_obj_obj_obj, Functor.comp_obj,
    Functor.curry_obj_map_app, Functor.curry_obj_obj_map, ← Functor.map_comp,
    Functor.comp_map, Functor.prod_map, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, CategoryTheory.prod_comp, Category.comp_id, Category.id_comp,
    Category.assoc] using h

end WeilConjectures
