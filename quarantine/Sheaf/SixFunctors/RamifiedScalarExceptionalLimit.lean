module

public import Sheaf.SixFunctors.FiniteScalarMateData
public import Sheaf.Paper.RamifiedScalarSystemTranspose
public import Sheaf.Paper.CartesianSectionAdjointMates
import Sheaf.SixFunctors.RamifiedScalarPreparation
import Sheaf.SixFunctors.RamifiedScalarSupportCompatibility

/-! # Cofinal realization of scalar exceptional and compact-support systems

Source: blueprint finite scalar-extension paragraph of lem-coef-rational-operations;
current scalar-six exceptional and compact-support proofs
(blueprint: lem-coef-ramified-scalar-exceptional-limit).

We use the published sequence-site presentation and its full upper tower. Applying
`retainedLimit` first retains exactly the exponents e(n+1), including their composite
quotient transitions. All comparisons below are natural isomorphisms of functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RamifiedScalarExceptionalLimit
open FiniteScalarMate

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)


variable {l E L i D hl f c}

/-- The five specified realizations and their unit/counit and cofinal normalizations.
This packages the clauses of the node, without making any of them hypotheses.
Source: the five displays and projection clauses of the node
(blueprint: lem-coef-ramified-scalar-exceptional-limit). -/
structure Realization (a : Context l E L i D hl f c) (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) where
  finiteX : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory),
    FiniteExceptional.domain l L X (retainedIndex e n)
      ((finiteTensor l E L i e he hp X n).obj K.obj)
  finiteY : ∀ (n : ℕ) (K : (FiniteExceptional.domain l E Y n).FullSubcategory),
    FiniteExceptional.domain l L Y (retainedIndex e n)
      ((finiteTensor l E L i e he hp Y n).obj K.obj)
  scalarEvaluationX : ∀ n : ℕ,
    a.TX ⋙ FiniteAdjunctionDiagram.evaluation l L X (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E X n ⋙
        finiteTensorRestricted l E L i e he hp X n (finiteX n)
  scalarEvaluationY : ∀ n : ℕ,
    a.TY ⋙ FiniteAdjunctionDiagram.evaluation l L Y (retainedIndex e n) ≅
      FiniteAdjunctionDiagram.evaluation l E Y n ⋙
        finiteTensorRestricted l E L i e he hp Y n (finiteY n)
  scalarTransitionX : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory),
    (FiniteExceptional.reduction l L X (retainedIndex_mono e hnm)).map
        (((scalarEvaluationX m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp X hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E X m).obj N).obj ≫
      (finiteTensor l E L i e he hp X n).map
        (FiniteAdjunctionDiagram.transition l E X a.r.quotientRestrictionX hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L X a.s.quotientRestrictionX
      (retainedIndex_mono e hnm) (a.TX.obj N)).hom ≫ ((scalarEvaluationX n).hom.app N).hom
  scalarTransitionY : ∀ (m n : ℕ) (hnm : n ≤ m)
      (N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory),
    (FiniteExceptional.reduction l L Y (retainedIndex_mono e hnm)).map
        (((scalarEvaluationY m).hom.app N).hom) ≫
      (quotientTensorSquare l E L i e he hp Y hnm).hom.app
        ((FiniteAdjunctionDiagram.evaluation l E Y m).obj N).obj ≫
      (finiteTensor l E L i e he hp Y n).map
        (FiniteAdjunctionDiagram.transition l E Y a.r.quotientRestrictionY hnm N).hom =
    (FiniteAdjunctionDiagram.transition l L Y a.s.quotientRestrictionY
      (retainedIndex_mono e hnm) (a.TY.obj N)).hom ≫ ((scalarEvaluationY n).hom.app N).hom
  adjunctionR : SemilinearSections.AdjunctionEvaluation a.RX a.RY a.adjR a.r.adjunction
  adjunctionS : SemilinearSections.AdjunctionEvaluation a.SXred a.SYred a.adjS a.s.adjunction
  completeRX : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (a.SX.adjunction.unit.app K.obj)
  completeRY : ∀ K : sfIntegralConstructibleCategory l E Y,
    IsIso (a.SY.adjunction.unit.app K.obj)
  completeSX : ∀ K : sfIntegralConstructibleCategory l L X,
    IsIso (a.UX.adjunction.unit.app K.obj)
  completeSY : ∀ K : sfIntegralConstructibleCategory l L Y,
    IsIso (a.UY.adjunction.unit.app K.obj)
  scalarReductionX : a.TIX ⋙ a.SXred ≅ a.RX ⋙ a.TX
  scalarReductionY : a.TIY ⋙ a.SYred ≅ a.RY ⋙ a.TY
  scalarReductionX_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (scalarReductionX.hom.app K).hom =
      (integralComparisonScalarCounit l E L i X a.SX a.UX
        ((FrobeniusExchange.models l L).roos X) a.scalarModelX).app K.obj
  scalarReductionY_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    (scalarReductionY.hom.app K).hom =
      (integralComparisonScalarCounit l E L i Y a.SY a.UY
        ((FrobeniusExchange.models l L).roos Y) a.scalarModelY).app K.obj
  cofinalX : retainedLimit l L X e ≅ coefficientSequenceLimit l L X
  cofinalY : retainedLimit l L Y e ≅ coefficientSequenceLimit l L Y
  cofinalX_normalization : ∀ C : CochainComplex (coefficientSequenceModules l L X) ℤ,
    ∃ ρ : integralOperationsRoos
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ⟶
      integralOperationsRoos (PurCompactSupport.retainedTower e
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor),
      PurCompactSupport.IsCofinalRoosMap e
        (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ρ ∧
      cofinalX.inv.app (DerivedCategory.Q.obj C) ≫ retainedRoosComparison l L X e C =
        fullRoosComparison l L X C ≫ DerivedCategory.Q.map ρ
  cofinalY_normalization : ∀ C : CochainComplex (coefficientSequenceModules l L Y) ℤ,
    ∃ ρ : integralOperationsRoos
        (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ⟶
      integralOperationsRoos (PurCompactSupport.retainedTower e
        (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj C).asFunctor),
      PurCompactSupport.IsCofinalRoosMap e
        (((coefficientSequenceRestriction l L Y).mapHomologicalComplex (.up ℤ)).obj C).asFunctor ρ ∧
      cofinalY.inv.app (DerivedCategory.Q.obj C) ≫ retainedRoosComparison l L Y e C =
        fullRoosComparison l L Y C ≫ DerivedCategory.Q.map ρ
  supportR_normalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (coefficientSequenceLimit l E Y).map ((adjunctionR.left.hom.app K).hom) ≫
        a.supportR.iso.hom.app K =
      (@asIso _ _ _ _ (a.SY.adjunction.unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj K).obj) (completeRY _)).inv
  supportS_normalization : ∀ K : sfIntegralConstructibleCategory l L X,
    (coefficientSequenceLimit l L Y).map ((adjunctionS.left.hom.app K).hom) ≫
        a.supportS.iso.hom.app K =
      (@asIso _ _ _ _ (a.UY.adjunction.unit.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c L).obj K).obj) (completeSY _)).inv
  uniformReduction : ∀ M : sfIntegralConstructibleCategory l E Y,
    ∃ a₀ b₀ : ℤ, a₀ ≤ b₀ ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E Y n).obj (a.RY.obj M).obj) a₀ b₀
  uniformExceptional : ∀ M : sfIntegralConstructibleCategory l E Y,
    ∃ a₀ b₀ : ℤ, a₀ ≤ b₀ ∧ ∀ n : ℕ,
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((coefficientSequenceDerivedEvaluation l E X n).obj (a.r.G.obj (a.RY.obj M)).obj) a₀ b₀
  source : a.RY ⋙ a.r.G ⋙ a.TX ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙
      retainedLimit l L X e ≅ a.GR ⋙ a.TIX ⋙ (sfIntegralConstructible l L X).ι
  target : a.RY ⋙ a.TY ⋙ a.s.G ⋙ (FiniteAdjunctionDiagram.domain l L X).ι ⋙
      retainedLimit l L X e ≅ a.TIY ⋙ a.GS ⋙ (sfIntegralConstructible l L X).ι
  scalarY : a.RY ⋙ a.TY ⋙ (FiniteAdjunctionDiagram.domain l L Y).ι ⋙
      retainedLimit l L Y e ≅ a.TIY ⋙ (sfIntegralConstructible l L Y).ι
  supportSource : a.RY ⋙ a.r.G ⋙ a.TX ⋙ a.s.F ⋙
      (FiniteAdjunctionDiagram.domain l L Y).ι ⋙ retainedLimit l L Y e ≅
    a.GR ⋙ a.TIX ⋙
      sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c L ⋙
        (sfIntegralConstructible l L Y).ι
  supportTarget : a.RY ⋙ a.r.G ⋙ a.r.F ⋙ a.TY ⋙
      (FiniteAdjunctionDiagram.domain l L Y).ι ⋙ retainedLimit l L Y e ≅
    a.GR ⋙ sfCompactSupportFiniteIntegralFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c E ⋙ a.TIY ⋙ (sfIntegralConstructible l L Y).ι
  source_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    source.hom.app M = cofinalX.hom.app ((a.TX.obj (a.r.G.obj (a.RY.obj M))).obj) ≫
      (coefficientSequenceLimit l L X).map
        ((integralComparisonDerivedSequenceScalar l E L i X).map
          ((adjunctionR.right.inv.app M).hom)) ≫
      a.scalarModelX.realization.inv.app (a.GR.obj M).obj
  target_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    target.hom.app M = cofinalX.hom.app ((a.s.G.obj (a.TY.obj (a.RY.obj M))).obj) ≫
      (coefficientSequenceLimit l L X).map ((a.s.G.map (scalarReductionY.inv.app M)).hom) ≫
      (coefficientSequenceLimit l L X).map
        ((adjunctionS.right.inv.app (a.TIY.obj M)).hom) ≫
      (@asIso _ _ _ _ (a.UX.adjunction.unit.app (a.GS.obj (a.TIY.obj M)).obj)
        (completeSX _)).inv
  scalarY_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    scalarY.hom.app M = cofinalY.hom.app (a.TY.obj (a.RY.obj M)).obj ≫
      a.scalarModelY.realization.inv.app M.obj
  supportSource_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    supportSource.hom.app M =
      cofinalY.hom.app (a.s.F.obj (a.TX.obj (a.r.G.obj (a.RY.obj M)))).obj ≫
      (coefficientSequenceLimit l L Y).map
        ((a.s.F.map (a.TX.map (adjunctionR.right.inv.app M) ≫
          scalarReductionX.inv.app (a.GR.obj M))).hom) ≫
      a.supportS.iso.hom.app (a.TIX.obj (a.GR.obj M))
  supportTarget_normalization : ∀ M : sfIntegralConstructibleCategory l E Y,
    supportTarget.hom.app M =
      cofinalY.hom.app (a.TY.obj (a.r.F.obj (a.r.G.obj (a.RY.obj M)))).obj ≫
      (coefficientSequenceLimit l L Y).map
        ((a.TY.map (a.r.F.map (adjunctionR.right.inv.app M) ≫
          adjunctionR.left.inv.app (a.GR.obj M))).hom) ≫
      a.scalarModelY.realization.inv.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj (a.GR.obj M)).obj
  comparison : ∀ M : sfIntegralConstructibleCategory l E Y,
    (retainedLimit l L Y e).map ((a.alpha.app (a.r.G.obj (a.RY.obj M))).hom) ≫
        supportSource.hom.app M =
      supportTarget.hom.app M ≫ a.integralAlphaComponent (a.GR.obj M)

variable (l E L i D hl f c)

/-- Cofinal scalar realization of the specified exceptional and compact-support functors.
All five natural identifications, domain assertions and normalization equations are
conclusions. Source: blueprint finite scalar-extension paragraph, extracted steps 5--6
(blueprint: lem-coef-ramified-scalar-exceptional-limit).

Proof: choose a common Tor interval for the first reduction of M. Residue Tor gives
that interval at every reduction. The integral exceptional adjoint gives G_R M and
its uniform output interval, using dimension bound zero for an empty scheme.
Normalized effectivity makes the actual reduction/limit counit at E_R R_Y M
invertible, with evaluations the projection adjoints. Finite-free scalar extension
preserves constructibility and the interval also at S-levels not divisible by e.
On a flat-term K-flat representative reassociate (Q tensor S) tensor B_n with
(Q tensor A_n) tensor B_n by the pure-tensor formulas, using chi to identify the
ordinary completed-sheaf tensor with the strict scalar model. The quotient maps
commute before localization. Arithmetic restriction gives the cofinal comparison
with p_n rho_e = p_en and preserves the unit cone. Compose these with the actual
counits to get source, target and scalarY. Apply the specified support functors,
their realization and the same counits to get supportSource and supportTarget.
The proper coefficient projection followed by open tensor balancing is exactly
the ordered finite-free comparison defining integralAlphaComponent. Equality
already on strict representatives gives comparison after total limit. All maps
are functorial in chain maps and roofs, so these are natural isomorphisms on
morphisms; no detection of equality by finite evaluation is used. -/
theorem ramifiedScalarExceptionalLimit (e : ℕ)
    (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e) :
    ∃ a : Context l E L i D hl f c, IsIso a.alpha ∧ Nonempty (Realization a e he hp) := by
  obtain ⟨a, h, ⟨P⟩⟩ :=
    RamifiedScalarPreparation.existsPreparation l E L i D hl f c e he hp
  refine ⟨a, h, ⟨{
    finiteX := P.finiteX
    finiteY := P.finiteY
    scalarEvaluationX := P.scalarEvaluationX
    scalarEvaluationY := P.scalarEvaluationY
    scalarTransitionX := P.scalarTransitionX
    scalarTransitionY := P.scalarTransitionY
    adjunctionR := P.adjunctionR
    adjunctionS := P.adjunctionS
    completeRX := P.completeRX
    completeRY := P.completeRY
    completeSX := P.completeSX
    completeSY := P.completeSY
    scalarReductionX := P.scalarReductionX
    scalarReductionY := P.scalarReductionY
    scalarReductionX_normalization := P.scalarReductionX_normalization
    scalarReductionY_normalization := P.scalarReductionY_normalization
    cofinalX := P.cofinalX
    cofinalY := P.cofinalY
    cofinalX_normalization := P.cofinalX_normalization
    cofinalY_normalization := P.cofinalY_normalization
    supportR_normalization := P.supportR_normalization
    supportS_normalization := P.supportS_normalization
    uniformReduction := P.uniformReduction
    uniformExceptional := P.uniformExceptional
    source := P.source
    target := P.target
    scalarY := P.scalarY
    supportSource := P.supportSource
    supportTarget := P.supportTarget
    source_normalization := ?_
    target_normalization := ?_
    scalarY_normalization := ?_
    supportSource_normalization := ?_
    supportTarget_normalization := ?_
    comparison := RamifiedScalarSupportCompatibility.supportComparison
      l E L i D hl f c e he hp a P }⟩⟩
  · intro M
    rfl
  · intro M
    rfl
  · intro M
    rfl
  · intro M
    let A := P.cofinalY.hom.app (a.s.F.obj (a.TX.obj (a.r.G.obj (a.RY.obj M)))).obj
    let B := (coefficientSequenceLimit l L Y).map
      (a.s.F.map (a.TX.map (P.adjunctionR.right.inv.app M))).hom
    let C := (coefficientSequenceLimit l L Y).map
      (a.s.F.map (P.scalarReductionX.inv.app (a.GR.obj M))).hom
    let Z := a.supportS.iso.hom.app (a.TIX.obj (a.GR.obj M))
    dsimp only [RamifiedScalarPreparation.Preparation.supportSource,
      RamifiedScalarPreparation.Preparation.supportAssembly,
      RamifiedScalarPreparation.Preparation.supportSystem]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_map, Functor.map_comp, Category.id_comp,
      Category.comp_id, Category.assoc]
    change A ≫ B ≫ C ≫ Z = _
    conv_rhs => rw [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
    change A ≫ B ≫ C ≫ Z = A ≫ (B ≫ C) ≫ Z
    exact congrArg (fun q => A ≫ q) (Category.assoc B C Z).symm
  · intro M
    change P.cofinalY.hom.app
        (a.TY.obj (a.r.F.obj (a.r.G.obj (a.RY.obj M)))).obj ≫
      (coefficientSequenceLimit l L Y).map
        (a.TY.map (a.r.F.map (P.adjunctionR.right.inv.app M) ≫
          P.adjunctionR.left.inv.app (a.GR.obj M))).hom ≫
      a.scalarModelY.realization.inv.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (finiteFieldDatumPrimeUnit D l hl) c E).obj (a.GR.obj M)).obj = _
    rfl

end WeilConjectures.RamifiedScalarExceptionalLimit
