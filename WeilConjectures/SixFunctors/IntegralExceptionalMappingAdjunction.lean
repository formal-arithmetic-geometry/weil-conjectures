/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.IntegralExceptionalLimitConstructible
import WeilConjectures.SixFunctors.IntegralSupportRealizationComparison
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.CoefficientEnrichedGlobalShift

/-! # The specified integral mapping-complex adjunction

Source: prop-coef-integral-exceptional-adjoint, proof paragraphs 1--2, and its
accepted DAG proof (blueprint: def-coef-specified-integral-mapping-adjunction).

This defines the specified adjunction on completed pro-etale coefficient sheaves.
It does not replace the full exceptional-adjoint proposition. All indices n mean exponent n+1.
The left and right functors are literal reduction/system-operation/limit composites.
The Hom normalization fixes the adjunction uniquely before any finite projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralExceptionalMapping
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SZ : CoefficientDerivedSystemCalculus l E c.Z)
  (SY : CoefficientDerivedSystemCalculus l E Y)
  (r : Realization l E D hl f c SX SZ SY)

/-- The membership and reconstruction facts needed to restrict the actual functors.
These are propositions, with no choice of functor, arrow or lift.
Source: the constructibility assertion and proof paragraphs 1--2
(blueprint: def-coef-specified-integral-mapping-adjunction). -/
structure Domains : Prop where
  reductionX : ∀ K : sfIntegralConstructibleCategory l E X,
    domain l E X (SX.reduction.obj K.obj)
  reductionY : ∀ M : sfIntegralConstructibleCategory l E Y,
    domain l E Y (SY.reduction.obj M.obj)
  left : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((coefficientSequenceLimit l E Y).obj
      (r.F.obj ⟨SX.reduction.obj K.obj, reductionX K⟩).obj)
  right : ∀ M : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l E X ((coefficientSequenceLimit l E X).obj
      (r.G.obj ⟨SY.reduction.obj M.obj, reductionY M⟩).obj)
  unitX : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (SX.adjunction.unit.app K.obj)
  unitY : ∀ M : sfIntegralConstructibleCategory l E Y,
    IsIso (SY.adjunction.unit.app M.obj)
  counitX : ∀ N : (domain l E X).FullSubcategory,
    IsIso (SX.adjunction.counit.app N.obj)
  counitY : ∀ N : (domain l E Y).FullSubcategory,
    IsIso (SY.adjunction.counit.app N.obj)
  lambdaX : ∀ P Q : sfIntegralConstructibleCategory l E X,
    IsIso ((coefficientIntegralGlobalHom l E X).map
      (Prod.mkHom (𝟙 (op P.obj)) (SX.adjunction.unit.app Q.obj)) ≫
      (SX.gamma l E X P.obj (SX.reduction.obj Q.obj)
        (SX.reduction_normalized Q.obj)).hom)
  lambdaY : ∀ P Q : sfIntegralConstructibleCategory l E Y,
    IsIso ((coefficientIntegralGlobalHom l E Y).map
      (Prod.mkHom (𝟙 (op P.obj)) (SY.adjunction.unit.app Q.obj)) ≫
      (SY.gamma l E Y P.obj (SY.reduction.obj Q.obj)
        (SY.reduction_normalized Q.obj)).hom)

variable {l E D hl f c SX SZ SY}

/-- Actual reduction on the source constructible category.
Source: proof paragraph 2 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def reductionX (h : Domains l E D hl f c SX SZ SY r) :=
  reducedConstructible X SX h.reductionX

/-- Actual reduction on the target constructible category.
Source: proof paragraph 2 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def reductionY (h : Domains l E D hl f c SX SZ SY r) :=
  reducedConstructible Y SY h.reductionY

/-- Integral compact support as the specified literal system composite.
Source: proof paragraph 2 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def left (h : Domains l E D hl f c SX SZ SY r) :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    (reductionX r h ⋙ r.F ⋙ (domain l E Y).ι ⋙ coefficientSequenceLimit l E Y) h.left

/-- Integral exceptional inverse image as the specified literal system composite.
Source: proof paragraph 1 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def right (h : Domains l E D hl f c SX SZ SY r) :
    sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X :=
  (sfIntegralConstructible l E X).lift
    (reductionY r h ⋙ r.G ⋙ (domain l E X).ι ⋙ coefficientSequenceLimit l E X) h.right

/-- The specified global mapping-complex map, lambda inverse after Rlim(Psi) after lambda.
Lambda is written directly as RHom(1,u) followed by gamma. Psi is the actual
three-factor system composite, using the inverse reconstruction counits.
Source: proof paragraph 2 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def mappingMap (h : Domains l E D hl f c SX SZ SY r)
    (a : r.mappingSource ≅ r.mappingTarget)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) :=
  letI := h.lambdaX K ((right r h).obj M)
  letI := h.counitY (r.F.obj ((reductionX r h).obj K))
  letI := h.counitX (r.G.obj ((reductionY r h).obj M))
  (coefficientIntegralGlobalHom l E Y).map
      (Prod.mkHom (𝟙 (op ((left r h).obj K).obj)) (SY.adjunction.unit.app M.obj)) ≫
    (SY.gamma l E Y ((left r h).obj K).obj (SY.reduction.obj M.obj)
      (SY.reduction_normalized M.obj)).hom ≫
    coefficientMappingLimit.{u+1}.map
      ((coefficientSequenceGlobalHom l E Y).map
          (Prod.mkHom (inv (SY.adjunction.counit.app
            (r.F.obj ((reductionX r h).obj K)).obj)).op (𝟙 _)) ≫
        a.hom.app (op ((reductionX r h).obj K), (reductionY r h).obj M) ≫
        (coefficientSequenceGlobalHom l E X).map
          (Prod.mkHom (𝟙 _) (inv (SX.adjunction.counit.app
            (r.G.obj ((reductionY r h).obj M)).obj)))) ≫
    inv ((coefficientIntegralGlobalHom l E X).map
      (Prod.mkHom (𝟙 (op K.obj)) (SX.adjunction.unit.app ((right r h).obj M).obj)) ≫
      (SX.gamma l E X K.obj (SX.reduction.obj ((right r h).obj M).obj)
        (SX.reduction_normalized ((right r h).obj M).obj)).hom)

/-- H-zero of the specified total mapping-complex map, using the recorded Hom identifications.
Source: proof paragraph 2 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def homMap (h : Domains l E D hl f c SX SZ SY r)
    (a : r.mappingSource ≅ r.mappingTarget)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) (v : (left r h).obj K ⟶ M) :
    K ⟶ (right r h).obj M :=
  ObjectProperty.homMk (coefficientIntegralHomEquiv l E X _ _
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map (mappingMap r h a K M))
      ((coefficientIntegralHomEquiv l E Y _ _).symm v.hom)))

/-- The precise normalization of the specified adjunction. It fixes every integral
Hom bijection by the actual total mapping-complex construction.
Source: proof paragraphs 2--3 (blueprint: def-coef-specified-integral-mapping-adjunction). -/
def IsSpecified (h : Domains l E D hl f c SX SZ SY r)
    (a : r.mappingSource ≅ r.mappingTarget) (adj : left r h ⊣ right r h) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) (v : (left r h).obj K ⟶ M),
    adj.homEquiv K M v = homMap r h a K M v

private theorem reconstructionUnit (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    (P : sfIntegralConstructibleCategory l E W) :
    IsIso (S.adjunction.unit.app P.obj) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p, a := 1, q := p, prime := hprime, exponent_pos := le_refl 1,
      cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
      card_base := by simp [Nat.card_eq_fintype_card], k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
  exact (purNormalizedReconstructionOfScheme l E W S).2 P.obj
    ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E W D₀ hl₀ P.obj).mp P.property.1⟩

private theorem domains : Domains l E D hl f c SX SZ SY r := by
  have hx := reconstructionUnit (l := l) (E := E) X SX
  have hy := reconstructionUnit (l := l) (E := E) Y SY
  refine ⟨reduction_domain l E D hl X SX, reduction_domain l E D hl Y SY,
    (support_and_counits r).1, exceptional_limit_constructible r, hx, hy,
    ?_, ?_, ?_, ?_⟩
  · intro N
    exact ((purNormalizedReconstructionOfScheme l E X SX).1 N.obj N.property.1).2
  · intro N
    exact ((purNormalizedReconstructionOfScheme l E Y SY).1 N.obj N.property.1).2
  · intro P Q
    have := hx Q
    have : IsIso (Prod.mkHom (𝟙 (op P.obj)) (SX.adjunction.unit.app Q.obj)) :=
      (inferInstance : IsIso ((Iso.refl (op P.obj)).prod
        (asIso (SX.adjunction.unit.app Q.obj))).hom)
    infer_instance
  · intro P Q
    have := hy Q
    have : IsIso (Prod.mkHom (𝟙 (op P.obj)) (SY.adjunction.unit.app Q.obj)) :=
      (inferInstance : IsIso ((Iso.refl (op P.obj)).prod
        (asIso (SY.adjunction.unit.app Q.obj))).hom)
    infer_instance

private def lambdaIso (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W)
    (C : CoefficientDerivedSystemCoherence l E W S)
    (hu : ∀ Q : sfIntegralConstructibleCategory l E W,
      IsIso (S.adjunction.unit.app Q.obj)) :
    (sfIntegralConstructible l E W).ι.op.prod (sfIntegralConstructible l E W).ι ⋙
        coefficientIntegralGlobalHom l E W ≅
      ((sfIntegralConstructible l E W).ι ⋙ S.reduction).op.prod
          ((sfIntegralConstructible l E W).ι ⋙ S.reduction) ⋙
        coefficientSequenceGlobalHom l E W ⋙ coefficientMappingLimit.{u+1} := by
  have hi (P Q : sfIntegralConstructibleCategory l E W) :
      IsIso (integralMappingLimitMap l E W S P.obj Q.obj) := by
    have := hu Q
    have : IsIso (Prod.mkHom (𝟙 (op P.obj)) (S.adjunction.unit.app Q.obj)) :=
      (inferInstance : IsIso ((Iso.refl (op P.obj)).prod
        (asIso (S.adjunction.unit.app Q.obj))).hom)
    unfold integralMappingLimitMap
    infer_instance
  exact NatIso.ofComponents
    (fun P ↦ asIso (integralMappingLimitMap l E W S P.1.unop.obj P.2.obj)) (by
      intro P Q v
      change (coefficientIntegralGlobalHom l E W).map
          (Prod.mkHom v.1.unop.hom.op v.2.hom) ≫ _ = _
      dsimp only [asIso_hom]
      unfold integralMappingLimitMap
      rw [← Category.assoc, ← Functor.map_comp]
      have hf : Prod.mkHom v.1.unop.hom.op v.2.hom ≫
          Prod.mkHom (𝟙 (op Q.1.unop.obj)) (S.adjunction.unit.app Q.2.obj) =
        Prod.mkHom (𝟙 (op P.1.unop.obj)) (S.adjunction.unit.app P.2.obj) ≫
          Prod.mkHom v.1.unop.hom.op ((coefficientSequenceLimit l E W).map
            (S.reduction.map v.2.hom)) := by
        ext
        · simp
        · exact S.adjunction.unit.naturality v.2.hom
      rw [hf, Functor.map_comp, Category.assoc]
      rw [C.gamma_naturality _ _ _ _ (S.reduction_normalized P.2.obj)
        (S.reduction_normalized Q.2.obj)]
      simp only [Functor.comp_map, Category.assoc]
      rfl)

private def totalMappingIso (h : Domains l E D hl f c SX SZ SY r)
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    {g : Geometry l E f SX SY} {s : SectionsPush g}
    {βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal}
    {βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal}
    (a : Enriched r g s βX βY) :
    (left r h ⋙ (sfIntegralConstructible l E Y).ι).op.prod
        (sfIntegralConstructible l E Y).ι ⋙ coefficientIntegralGlobalHom l E Y ≅
      (sfIntegralConstructible l E X).ι.op.prod
        (right r h ⋙ (sfIntegralConstructible l E X).ι) ⋙
          coefficientIntegralGlobalHom l E X :=
  Functor.isoWhiskerLeft ((left r h).op.prod (𝟭 _))
      (lambdaIso Y SY CY h.unitY) ≪≫
    Functor.isoWhiskerRight (psi r a) coefficientMappingLimit.{u+1} ≪≫
    (Functor.isoWhiskerLeft ((𝟭 _).op.prod (right r h))
      (lambdaIso X SX CX h.unitX)).symm

private theorem totalMappingIso_hom (h : Domains l E D hl f c SX SZ SY r)
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    {g : Geometry l E f SX SY} {s : SectionsPush g}
    {βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal}
    {βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal}
    (a : Enriched r g s βX βY)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) :
    (totalMappingIso r h CX CY a).hom.app (op K, M) = mappingMap r h a.iso K M := by
  simp only [totalMappingIso, lambdaIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, asIso_hom, asIso_inv, psi, NatIso.prod_hom, NatIso.op_hom,
    NatIso.isIso_inv_app, NatTrans.op_app,
    NatTrans.prod, supportIso, exceptionalIso, supportCounit, exceptionalCounit,
    integralMappingLimitMap, Functor.map_comp, mappingMap, Category.assoc]
  rfl

private def mappingHomEquiv (h : Domains l E D hl f c SX SZ SY r)
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    {g : Geometry l E f SX SY} {s : SectionsPush g}
    {βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal}
    {βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal}
    (a : Enriched r g s βX βY)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) :
    ((left r h).obj K ⟶ M) ≃ (K ⟶ (right r h).obj M) :=
  (sfIntegralConstructible l E Y).fullyFaithfulι.homEquiv.trans
    ((coefficientIntegralHomEquiv l E Y _ _).toEquiv.symm.trans
      ((((forget AddCommGrpCat.{u+1}).mapIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).mapIso
          ((totalMappingIso r h CX CY a).app (op K, M)))).toEquiv).trans
        ((coefficientIntegralHomEquiv l E X _ _).toEquiv.trans
          (sfIntegralConstructible l E X).fullyFaithfulι.homEquiv.symm)))

private theorem mappingHomEquiv_apply (h : Domains l E D hl f c SX SZ SY r)
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    {g : Geometry l E f SX SY} {s : SectionsPush g}
    {βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal}
    {βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal}
    (a : Enriched r g s βX βY)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) (v : (left r h).obj K ⟶ M) :
    mappingHomEquiv r h CX CY a K M v = homMap r h a.iso K M v := by
  apply ObjectProperty.hom_ext
  change coefficientIntegralHomEquiv l E X _ _
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
        ((totalMappingIso r h CX CY a).hom.app (op K, M)))
          ((coefficientIntegralHomEquiv l E Y _ _).symm v.hom)) = _
  rw [totalMappingIso_hom]
  rfl

private theorem mappingHomEquiv_natural (h : Domains l E D hl f c SX SZ SY r)
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    {g : Geometry l E f SX SY} {s : SectionsPush g}
    {βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal}
    {βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal}
    (a : Enriched r g s βX βY)
    {K K' : sfIntegralConstructibleCategory l E X}
    {M M' : sfIntegralConstructibleCategory l E Y}
    (v : K' ⟶ K) (w : M ⟶ M') (z : (left r h).obj K ⟶ M) :
    mappingHomEquiv r h CX CY a K' M' ((left r h).map v ≫ z ≫ w) =
      v ≫ mappingHomEquiv r h CX CY a K M z ≫ (right r h).map w := by
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0
  let θ := totalMappingIso r h CX CY a
  let x := (coefficientIntegralHomEquiv l E Y _ _).symm z.hom
  have hy := (coefficientHomZeroEquiv_exists.{u, u+1, u}
    (Scheme.ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).choose_spec.1.1
  have hx := (coefficientHomZeroEquiv_exists.{u, u+1, u}
    (Scheme.ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X)).choose_spec.1.1
  have hn := θ.hom.naturality (Prod.mkHom v.op w)
  change (coefficientIntegralGlobalHom l E Y).map
      (Prod.mkHom ((left r h).map v).hom.op w.hom) ≫ θ.hom.app (op K', M') =
    θ.hom.app (op K, M) ≫ (coefficientIntegralGlobalHom l E X).map
      (Prod.mkHom v.hom.op ((right r h).map w).hom) at hn
  have hpre := hy _ _ _ _ ((left r h).map v).hom w.hom x
  change coefficientIntegralHomEquiv l E Y _ _
      ((H.map ((coefficientIntegralGlobalHom l E Y).map
        (Prod.mkHom ((left r h).map v).hom.op w.hom))) x) =
    ((left r h).map v).hom ≫ coefficientIntegralHomEquiv l E Y _ _ x ≫ w.hom at hpre
  have harg : (coefficientIntegralHomEquiv l E Y _ _).symm
      (((left r h).map v).hom ≫ z.hom ≫ w.hom) =
    (H.map ((coefficientIntegralGlobalHom l E Y).map
      (Prod.mkHom ((left r h).map v).hom.op w.hom))) x := by
    apply (coefficientIntegralHomEquiv l E Y _ _).injective
    rw [AddEquiv.apply_symm_apply, hpre]
    simp only [x, AddEquiv.apply_symm_apply]
  apply ObjectProperty.hom_ext
  change coefficientIntegralHomEquiv l E X _ _
      ((H.map (θ.hom.app (op K', M')))
        ((coefficientIntegralHomEquiv l E Y _ _).symm
          (((left r h).map v).hom ≫ z.hom ≫ w.hom))) =
    v.hom ≫ coefficientIntegralHomEquiv l E X _ _
      ((H.map (θ.hom.app (op K, M))) x) ≫ ((right r h).map w).hom
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj, Prod.fst, Prod.snd,
    Opposite.unop_op]
  erw [harg, ← AddCommGrpCat.comp_apply, ← H.map_comp, hn, H.map_comp,
    AddCommGrpCat.comp_apply]
  exact hx _ _ _ _ v.hom ((right r h).map w).hom _

/-- The completed pro-etale mapping adjunction, uniquely fixed by its Hom normalization.
The preservation and invertibility facts are conclusions. The comparison identifies
its literal left composite with the already recorded compact-support functor.
Source: prop-coef-integral-exceptional-adjoint, proof paragraphs 1--3
(blueprint: def-coef-specified-integral-mapping-adjunction).

Proof: the integral dual-exceptional-system comparison gives a constructible dual
formula and its common Tor bound. Reconstruction identifies its actual reduction
with E_f R_Y and its limit with G_f, proving right preservation. Integral compact
support and the realization's IntegralSupport identify the left functor. Residue
Tor gives finite-Tor reductions without a bound common to all systems. Actual
reconstruction gives the unit and counit isomorphisms. The integral mapping-limit
comparison gives invertible lambda. Compose those maps with the actual enriched
system map a to obtain inverse natural Hom bijections. Their values on identities
give units and counits and naturality proves the triangles. The Hom bijections
uniquely determine the adjunction, so no arbitrary adjunction is selected. -/
theorem exists_unique
    (_CX : CoefficientDerivedSystemCoherence l E X SX)
    (_CY : CoefficientDerivedSystemCoherence l E Y SY)
    (g : Geometry l E f SX SY) (s : SectionsPush g)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (a : Enriched r g s βX βY) :
    ∃ h : Domains l E D hl f c SX SZ SY r,
      Nonempty (left r h ≅
        sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E) ∧
      ∃! adj : left r h ⊣ right r h, IsSpecified r h a.iso adj := by
  classical
  let h := domains r
  obtain ⟨e⟩ := support_realization_comparison r
  have he : Nonempty (left r h ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E) :=
    ⟨Functor.fullyFaithfulCancelRight (sfIntegralConstructible l E Y).ι e⟩
  let core : Adjunction.CoreHomEquiv (left r h) (right r h) := {
    homEquiv := mappingHomEquiv r h _CX _CY a
    homEquiv_naturality_left_symm := by
      intro K' K M v z
      apply (mappingHomEquiv r h _CX _CY a K' M).injective
      rw [Equiv.apply_symm_apply]
      have hn := mappingHomEquiv_natural r h _CX _CY a v (𝟙 M)
        ((mappingHomEquiv r h _CX _CY a K M).symm z)
      simpa only [Category.comp_id, CategoryTheory.Functor.map_id,
        Equiv.apply_symm_apply] using hn.symm
    homEquiv_naturality_right := by
      intro K M M' v w
      have hn := mappingHomEquiv_natural r h _CX _CY a (𝟙 K) w v
      simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hn }
  let adj := Adjunction.mkOfHomEquiv core
  have hadj : IsSpecified r h a.iso adj := by
    intro K M v
    rw [show adj.homEquiv = core.homEquiv from Adjunction.mkOfHomEquiv_homEquiv core]
    exact mappingHomEquiv_apply r h _CX _CY a K M v
  refine ⟨h, he, adj, hadj, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  apply NatTrans.ext
  funext K
  have hsame := (hadj' K ((left r h).obj K) (𝟙 _)).trans
    (hadj K ((left r h).obj K) (𝟙 _)).symm
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at hsame
  exact (Category.comp_id _).symm.trans (hsame.trans (Category.comp_id _))

end WeilConjectures.IntegralExceptionalMapping
