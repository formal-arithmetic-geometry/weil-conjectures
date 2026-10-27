module

public import Sheaf.Paper.ClopenSystemFiniteRealization
public import Sheaf.Paper.AdicPurityObjects
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.OpenCompletedRestrictionIdentification
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Site transport and integral realization on a clopen component

Source: blueprint def-pur-section-invariant, finite-clopen expansion, retained steps 8--9;
Zheng, Lemmas 4.10 and 5.22; Stacks Tags 0941 and 08BJ
(blueprint: lem-pur-clopen-system-integral-realization).

All systems below are actual strict systems. Their scalar forgetting and inverse limit
are the published functors on the derived category of strict towers. The result records
normalization equations for maps, as well as natural isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local irreducible] HasDerivedCategory.standard
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring WeilConjectures.IntegralOnSlice.finite
  WeilConjectures.IntegralOnSlice.projection
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] clopenCompletedOrdinaryAdditive
  clopenCompletedOrdinaryLimits clopenCompletedOrdinaryColimits
  clopenCompletedTowerAdditive clopenCompletedTowerLimits clopenCompletedTowerColimits

set_option maxHeartbeats 40000 in
-- Normalize the canonical functor comparisons at the fixed coefficient level.
/-- The complete canonical transport assertion data, before integral realization.
Source: retained finite-clopen step 8
(blueprint: lem-pur-clopen-system-integral-realization). -/
structure ClopenSystemIntegralTransport (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g] where
  core : ClopenSystemTransportCore P c j
  maps : ClopenSystemTransportMaps P c j core
  finite : ClopenSystemTransportFinite P c j core maps

set_option maxHeartbeats 500000 in
-- Normalize exact restriction against the actual total derived limit.
/-- Total-limit transport of the strict system comparison.
Source: Stacks 0941 and 08BJ
(blueprint: lem-pur-clopen-system-integral-realization). -/
structure ClopenSystemIntegralLimit (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g]
    (T : ClopenSystemIntegralTransport P c j) where
  ordinaryScalarRestriction :
    T.core.site.ordinary.inverse ⋙ T.core.Ci.sequence.ordinary.functor ⋙
        coefficientSequenceRestriction.{u, u} P.coefficients.l P.extension Xi ≅
      T.core.CX.sequence.ordinary.functor ⋙
        coefficientSequenceRestriction.{u, u} P.coefficients.l P.extension X ⋙
        clopenCompletedTowerOrdinary P.coefficients.l P.extension j
  ordinaryScalarRestriction_sections : ∀
      (M : ClopenProEtaleSystem P.coefficients.l P.extension X) (n : ℕ) (V : Xi.ProEt)
      (x : (M.level n).val.obj (op ((OpenCompletedRestriction.inclusion j).obj V)))
      (a : (((T.core.CX.sequence.ordinary.functor ⋙
        coefficientSequenceRestriction.{u, u} P.coefficients.l P.extension X ⋙
        clopenCompletedTowerOrdinary P.coefficients.l P.extension j).obj M).obj
          (op n)).val.obj (op V))
      (b : ((coefficientSequenceEvaluation.{u, u} P.coefficients.l P.extension X n).obj
        (T.core.CX.sequence.ordinary.functor.obj M)).val.obj
          (op ((OpenCompletedRestriction.inclusion j).obj V)))
      (d : ((coefficientSequenceEvaluation.{u, u} P.coefficients.l P.extension Xi n).obj
        (T.core.Ci.sequence.ordinary.functor.obj
          (T.core.site.ordinary.inverse.obj M))).val.obj (op V))
      (z : ((T.core.site.ordinary.inverse.obj M).level n).val.obj (op V)),
    HEq a b →
    HEq (((T.core.CX.sequence.evaluation n).hom.app M).val.app
      (op ((OpenCompletedRestriction.inclusion j).obj V)) b) x →
    HEq (((ordinaryScalarRestriction.inv.app M).app (op n)).val.app (op V) a) d →
    HEq (((T.core.Ci.sequence.evaluation n).hom.app
      (T.core.site.ordinary.inverse.obj M)).val.app (op V) d) z →
    ((T.core.setRestriction.sheafIso).hom.app
        ((SheafOfModules.coefficientUnderlying (J := Scheme.ProEt.topology X)
          (clopenSystemRing P.coefficients.l P.extension)
          (clopenSystemUniformizer P.coefficients.l P.extension) n).obj (M.level n))).hom.app
            (op V)
      (((T.core.site.ordinary.lift n).moduleUnderlying.hom.app (M.level n)).hom.app (op V)
        (((T.core.site.ordinary.inverseEvaluation n).hom.app M).val.app (op V) z)) = x
  scalarRestriction : T.core.site.sequenceRestriction ⋙
      coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension Xi ≅
    coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension X ⋙
      clopenCompletedTowerRestriction P.coefficients.l P.extension j
  scalarRestriction_normalized : ∀ H : CochainComplex
      (ClopenProEtaleSystem P.coefficients.l P.extension X) ℤ,
    scalarRestriction.hom.app (T.core.CX.sequence.derived.functor.obj
        (DerivedCategory.Q.obj H)) ≫
      (clopenCompletedTowerRestriction P.coefficients.l P.extension j).map
        ((coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension X).map
          (T.core.CX.sequence.factors.hom.app H)) ≫
      (clopenCompletedTowerRestriction P.coefficients.l P.extension j).map
        ((coefficientSequenceRestriction.{u, u} P.coefficients.l P.extension
          X).mapDerivedCategoryFactors.hom.app
            ((T.core.CX.sequence.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj H)) ≫
      (clopenCompletedTowerOrdinary P.coefficients.l P.extension
        j).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceRestriction.{u, u} P.coefficients.l P.extension
            X).mapHomologicalComplex (.up ℤ)).obj
              ((T.core.CX.sequence.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj H)) =
    (coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension Xi).map
      (T.core.Ci.sequence.derived.functor.map
        (T.core.site.derived.system.inverse.map
          (T.core.CX.sequence.derived.unitIso.inv.app (DerivedCategory.Q.obj H)))) ≫
    (coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension Xi).map
      (T.core.Ci.sequence.derived.functor.map
        (T.core.site.derived.system.inverseFactors.hom.app H)) ≫
    (coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension Xi).map
      (T.core.Ci.sequence.factors.hom.app
        ((T.core.site.ordinary.inverse.mapHomologicalComplex (.up ℤ)).obj H)) ≫
    (coefficientSequenceRestriction.{u, u} P.coefficients.l P.extension
      Xi).mapDerivedCategoryFactors.hom.app
        ((T.core.Ci.sequence.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj
          ((T.core.site.ordinary.inverse.mapHomologicalComplex (.up ℤ)).obj H)) ≫
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex ordinaryScalarRestriction (.up ℤ)).hom.app H)
  ordinaryLimitRestriction :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} P.coefficients.l P.extension X) ⥤
      scalarReductionSource.{u, u} P.coefficients.l P.extension X) ⋙
        clopenCompletedOrdinary P.coefficients.l P.extension j ≅
      clopenCompletedTowerOrdinary P.coefficients.l P.extension j ⋙ lim
  ordinaryLimitRestriction_projections : ∀ N (n : ℕᵒᵖ),
    ordinaryLimitRestriction.hom.app N ≫
        limit.π ((clopenCompletedTowerOrdinary P.coefficients.l P.extension j).obj N) n =
      (clopenCompletedOrdinary P.coefficients.l P.extension j).map (limit.π N n)
  totalLimitRestriction :
    coefficientConstantTowerLimit.{u, u} P.coefficients.l P.extension X ⋙
      OpenCompletedRestriction.derivedRestriction.{u, u} P.coefficients.l P.extension j ≅
    clopenCompletedTowerRestriction P.coefficients.l P.extension j ⋙
      coefficientConstantTowerLimit.{u, u} P.coefficients.l P.extension Xi
  totalLimitRestriction_normalized : ∀ J : CochainComplex
      (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} P.coefficients.l P.extension X) ℤ,
    (OpenCompletedRestriction.derivedRestriction.{u, u} P.coefficients.l P.extension j).map
        (Functor.rightDerivedFunctorUnitQ
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} P.coefficients.l P.extension X) ⥤
      scalarReductionSource.{u, u} P.coefficients.l P.extension X) J) ≫
      totalLimitRestriction.hom.app (DerivedCategory.Q.obj J) =
    (Functor.mapDerivedCategoryFactors
        (clopenCompletedOrdinary P.coefficients.l P.extension j)).hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u}
            P.coefficients.l P.extension X) ⥤
      scalarReductionSource.{u, u} P.coefficients.l P.extension
            X).mapHomologicalComplex
            (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex
          ordinaryLimitRestriction (.up ℤ)).hom.app J) ≫
      Functor.rightDerivedFunctorUnitQ
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} P.coefficients.l P.extension Xi) ⥤
          scalarReductionSource.{u, u} P.coefficients.l P.extension Xi)
          (((clopenCompletedTowerOrdinary P.coefficients.l P.extension j).mapHomologicalComplex
            (.up ℤ)).obj J) ≫
      (coefficientConstantTowerLimit.{u, u} P.coefficients.l P.extension Xi).map
        ((Functor.mapDerivedCategoryFactors
          (clopenCompletedTowerOrdinary P.coefficients.l P.extension j)).inv.app J)
  limitRestriction : coefficientSequenceLimit.{u, u} P.coefficients.l P.extension X ⋙
      OpenCompletedRestriction.derivedRestriction.{u, u} P.coefficients.l P.extension j ≅
    T.core.site.sequenceRestriction ⋙
      coefficientSequenceLimit.{u, u} P.coefficients.l P.extension Xi
  limitRestriction_map : ∀ N,
    limitRestriction.hom.app N =
      totalLimitRestriction.hom.app
          ((coefficientSequenceDerivedRestriction.{u, u} P.coefficients.l P.extension X).obj N) ≫
        (coefficientConstantTowerLimit.{u, u} P.coefficients.l P.extension Xi).map
          (scalarRestriction.inv.app N)

set_option maxHeartbeats 500000 in
-- Normalize exact restriction against the actual total derived limit.
/-- Integral realization of the preceding actual strict-system arrow.
Source: retained step 9 of the section-invariant finite-clopen expansion
(blueprint: lem-pur-clopen-system-integral-realization). -/
structure ClopenSystemIntegralRealization (P : PurityFiniteSetting.{u})
    {X Y Xi : Scheme.{u}} {g : X ⟶ Y} (c : Compactification g)
    (j : Xi ⟶ X) [IsOpenImmersion j] [IsClosedImmersion j] [QuasiCompact g] where
  transport : ClopenSystemIntegralTransport P c j
  limits : ClopenSystemIntegralLimit P c j transport
  integral : sfIntegralConstructibleCategory P.coefficients.l P.extension Y ⥤
    sfIntegralConstructibleCategory P.coefficients.l P.extension X
  integralI : sfIntegralConstructibleCategory P.coefficients.l P.extension Y ⥤
    sfIntegralConstructibleCategory P.coefficients.l P.extension Xi
  integralFormula : integral ⋙ (sfIntegralConstructible P.coefficients.l P.extension X).ι ≅
    clopenExceptionalSystem P.coefficients.l P.extension
      transport.core.S transport.core.G transport.core.CX transport.core.CY ⋙
      coefficientSequenceLimit.{u, u} P.coefficients.l P.extension X
  integralFormulaI : integralI ⋙ (sfIntegralConstructible P.coefficients.l P.extension Xi).ι ≅
    clopenExceptionalSystem P.coefficients.l P.extension
      transport.core.Si transport.core.Gi transport.core.Ci transport.core.CYi ⋙
      coefficientSequenceLimit.{u, u} P.coefficients.l P.extension Xi
  restrictionComparison : integral ⋙
      (sfIntegralConstructible P.coefficients.l P.extension X).ι ⋙
      OpenCompletedRestriction.derivedRestriction.{u, u} P.coefficients.l P.extension j ≅
    integralI ⋙ (sfIntegralConstructible P.coefficients.l P.extension Xi).ι
  restrictionComparison_map : ∀ L,
    restrictionComparison.hom.app L =
      (OpenCompletedRestriction.derivedRestriction.{u, u} P.coefficients.l P.extension j).map
          (integralFormula.hom.app L) ≫
        limits.limitRestriction.hom.app
          ((clopenExceptionalSystem P.coefficients.l P.extension
            transport.core.S transport.core.G transport.core.CX transport.core.CY).obj L) ≫
        (coefficientSequenceLimit.{u, u} P.coefficients.l P.extension Xi).map
          (transport.maps.system.hom.app L) ≫ integralFormulaI.inv.app L
  completedComparison : OpenCompletedRestriction.Comparison.{u, u} P.coefficients.l P.extension j
  reductionRestriction : ∀ n,
    (sfIntegralConstructible P.coefficients.l P.extension X).ι ⋙
        OpenCompletedRestriction.derivedRestriction.{u, u} P.coefficients.l P.extension j ⋙
        scalarReductionDerivedExtension P.coefficients.l P.extension Xi n ≅
      (sfIntegralConstructible P.coefficients.l P.extension X).ι ⋙
        scalarReductionDerivedExtension P.coefficients.l P.extension X n ⋙
        finiteDerivedPullback P.coefficients.l P.extension n j
  reductionRestriction_normalized : ∀ n
      (K : sfIntegralConstructibleCategory P.coefficients.l P.extension X),
    (reductionRestriction n).hom.app K =
      (scalarReductionDerivedExtension P.coefficients.l P.extension Xi n).map
        ((OpenCompletedRestriction.kappa.{u, u} P.coefficients.l P.extension j
          completedComparison).app K.obj) ≫
      purAdicPullbackReduction P.coefficients.l P.extension j K.obj n
  completed_isIso : ∀ K : sfIntegralConstructibleCategory P.coefficients.l P.extension X,
    IsIso ((OpenCompletedRestriction.kappa.{u, u} P.coefficients.l P.extension j
      completedComparison).app K.obj)
  integralComparison : integral ⋙
      (sfIntegralConstructible P.coefficients.l P.extension X).ι ⋙
      integralDerivedPullback P.coefficients.l P.extension j ≅
    integralI ⋙ (sfIntegralConstructible P.coefficients.l P.extension Xi).ι
  integralComparison_map : ∀ L,
    integralComparison.hom.app L =
      @inv _ _ _ _ ((OpenCompletedRestriction.kappa.{u, u} P.coefficients.l P.extension j
        completedComparison).app (integral.obj L).obj) (completed_isIso (integral.obj L)) ≫
          restrictionComparison.hom.app L

/-- The canonical site square, finite counit-normalized evaluations and actual integral
realization exist for every finite clopen partition, including empty factors.
Source: blueprint def-pur-section-invariant, finite-clopen expansion, steps 8--9;
Zheng Lemmas 4.10 and 5.22; Stacks Tags 0941 and 08BJ
(blueprint: lem-pur-clopen-system-integral-realization).

Proof plan:
1. Use the inverse of the canonical underlying comparison-pullback square. Its naturality
in scalar multiplication and quotient transitions makes it a square of strict systems.
Exactness descends that same square and its inverse through localization.
2. Whisker the unique counit-normalized strict étale comparison with R nu_* and nu^*.
Compose it with the site square. Its inverse is the composite of the inverse factors.
3. Evaluate the already constructed system arrow. The coefficient-system comparison
identifies evaluated units and counits. The unit-normalized open site comparison sends
zero insertion and its counit to the same maps: identity on this component and zero
elsewhere. Its compositor uses the identical proper factor of c and c.precomp j.
4. Transpose on bounded constructible finite inputs through the transported étale-origin
adjunction. The resulting finite counit equation is exactly the prescribed one; uniqueness
of transpose identifies the evaluation with the finite pro-étale comparison.
5. Precompose with the actual single-representative derived reduction. Restriction and
scalar forgetting have the same underlying sheaves and transitions, and their completed
actions agree on every quotient projection. Localize this strict equality, retaining maps.
6. Zero insertion is an exact left adjoint to component restriction, so restriction
preserves K-injective tower resolutions. Ordinary compatible-family limits commute with
restriction, with the displayed projection normalization. Apply this to resolutions and
descend: the unit equation identifies the comparison for the total derived limit.
7. Apply DU and the total limit to the system isomorphism. The two formula comparisons
identify these values with the integral exceptional functors on constructible inputs.
Use the canonical open completed-restriction comparison: its finite quotient-tower,
projection, augmentation and signed Roos equations identify restriction with completed
pullback on complete objects. The resulting arrow is kappa inverse followed by the
realized comparison, precisely the displayed integralComparison_map.
8. Functors carry both inverse equations and the naturality square to the corresponding
integral equations. An empty component is a zero category, and an empty index type
has no component assertions. At no point is an arbitrary derived diagram lifted.
-/
theorem clopenSystemIntegralRealization
    (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (g : X ⟶ Y) [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left]
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (_hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (_hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (c : Compactification g.left) :
    ∀ i : I, Nonempty (ClopenSystemIntegralRealization P c (j i).left) := by
  sorry

end WeilConjectures.PurityFiniteSetting
