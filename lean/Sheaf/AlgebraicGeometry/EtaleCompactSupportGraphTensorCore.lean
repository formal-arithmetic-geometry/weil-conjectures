module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase
import all Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import all Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition

/-! Core mate equation for compact-support graph tensor evaluation.
(blueprint: lem-pur-compact-support-graph-tensor-evaluation-core).

Proof: evaluate the normalized graph comparison on local tensor generators, where the unit
equation determines the sum-extension tensor mate. The graph and complementary restrictions
agree sectionwise. Pass to flat-term K-flat representatives, totalize degreewise, and use the
canonical tensor, open projection, and compactification comparisons. Derived localization
descent then gives the unbounded mate equation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  etaleLowerShriek upperStar lowerStar openImmersionLowerShriek derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

private theorem graphComparison_eq_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e] [IsSeparated e]
    (c : Compactification e) :
    GraphExchange.compactificationEtaleComparison (ModuleCat.{u + 1} A) e c =
      compactificationEtaleComparison A e c := by
  have hb : GraphExchange.clopenUpperStarLowerShriekAdjunction
      (ModuleCat.{u + 1} A) c.graphExchangeSection =
        clopenUpperStarLowerShriekAdjunction A c.selfGraph := by
    apply Adjunction.ext_counit
    ext J
    rw [GraphExchange.clopenUpperStarLowerShriekAdjunction_counit_app,
      clopenUpperStarLowerShriekAdjunction_counit_app]
    rfl
  have hG : GraphExchange.compactificationEtaleGraphIso (ModuleCat.{u + 1} A) e c =
      compactificationEtaleGraphIso A e c := by
    unfold GraphExchange.compactificationEtaleGraphIso graph_iso_from_units
      compactificationEtaleGraphIso
    rfl
  have hg : GraphExchange.compactificationEtaleGraphMap (ModuleCat.{u + 1} A) e c =
      compactificationEtaleGraphMap A e c := by
    ext J
    rw [GraphExchange.compactificationEtaleGraphMap_app]
    dsimp only [GraphExchange.clopenTransfer, compactificationEtaleGraphMap, clopenTransfer]
    rw [hb, hG]
    rfl
  have hu : GraphExchange.compactificationEtaleUnit (ModuleCat.{u + 1} A) e c =
      compactificationEtaleUnit A e c := by
    unfold GraphExchange.compactificationEtaleUnit graph_unit_from_exchange
      compactificationEtaleUnit
    rw [hg]
  unfold GraphExchange.compactificationEtaleComparison transpose_natTrans
    compactificationEtaleComparison
  rw [hu]

private theorem normalizedComparison_eq_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    (N.comparison e c).inv = compactificationEtaleComparison A e c := by
  have ha : N.sheafComparison e c = etaleCompactificationGraphMap A e c := by
    apply NatTrans.ext
    funext J
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app J) := open_compare_mono A c.i J
    have : Mono ((compactificationSheafToDirectImage A c).app J) := by
      dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
        Functor.whiskerRight_app]
      have : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app J)) :=
          Functor.map_mono _ _
      exact mono_comp
        ((lowerStar (ModuleCat.{u + 1} A) c.g).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app J))
        ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) c.i c.g e c.comm).app J).hom
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app J)).1
    exact (N.sheaf_normalization e c J).trans
      (compactSupportGraphSheafComparison_normalization A e c J).symm
  calc
    _ = compactSupportDerivedComparison A e c (N.sheafComparison e c) := by
      apply Localization.natTrans_ext DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
          (.up ℤ))
      intro H
      exact (N.derived_normalization e c H).trans
        (compactSupportDerivedComparison_app A e c (N.sheafComparison e c) H).symm
    _ = _ := by rw [ha, GraphExchange.graph_comparison_eq, graphComparison_eq_source]

private theorem tensorComparison_eq
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (e : V ⟶ T)
    (B K : DerivedCategoryModule A T) :
    (etaleSumExtensionTensorPullbackIso A e B K).hom =
      (sfEtaleExactPullbackTensorIso A e B K).inv := by
  simp only [etaleSumExtensionTensorPullbackIso, sfEtaleExactPullbackTensorIso,
    supportExactPullbackTensorIso, supportDerivedTensorIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [NatTrans.naturality_assoc]

-- Keep the statement's original unused `adj` let binding verbatim.
set_option linter.unusedVariables false in
/-- The normalized comparison satisfies the mate equation before transposing through the
compactification adjunction. This is the core tensor calculation; the graph evaluation theorem
is obtained by applying the adjunction hom-equivalence. Source: Stacks Tags 0GKF and 0GL5.
(blueprint: lem-pur-compact-support-graph-tensor-evaluation-core).

Proof: evaluate the normalized graph comparison on local tensor generators, where the unit
equation determines the sum-extension tensor mate. The graph and complementary restrictions
agree sectionwise. Pass to flat-term K-flat representatives, totalize degreewise, and use the
canonical tensor, open projection, and compactification comparisons. Derived localization
descent then gives the unbounded mate equation. -/
theorem compactSupportGraph_tensor_evaluation_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let S : DerivedCategoryModule A V ⥤ DerivedCategoryModule A T :=
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    let E : DerivedCategoryModule A T ⥤ DerivedCategoryModule A V :=
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    let T₀ := derivedTensor (ModuleCat.{u + 1} A) T
    let V₀ := derivedTensor (ModuleCat.{u + 1} A) V
    let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g
    ∀ q : S.obj ((V₀.obj M).obj (E.obj K)) ⟶ (T₀.obj (S.obj M)).obj K,
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
        inferInstance).mapDerivedCategoryAdjunction).unit.app _ ≫ E.map q =
        (V₀.map ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
          inferInstance).mapDerivedCategoryAdjunction.unit.app M)).app (E.obj K) ≫
          (etaleSumExtensionTensorPullbackIso A e (S.obj M) K).hom →
      q ≫ (T₀.map ((N.comparison e c).inv.app M)).app K ≫
          ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            ((V₀.obj M).map
              ((leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) e).hom.app K)) =
        (N.comparison e c).inv.app ((V₀.obj M).obj (E.obj K)) := by
  dsimp only
  intro q hq
  -- The normalization fixes the sheaf map, then its unique derived descent.
  have ht := normalizedComparison_eq_source A N e c
  have hq' : q = sfEtaleSumExactTensorMap A e M K := by
    apply ((derivedEtaleLowerShriekMapAdjunction
      (ModuleCat.{u + 1} A) e).homEquiv _ _).injective
    simpa only [sfEtaleSumExactTensorMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_unit, derivedEtaleLowerShriekMapAdjunction,
      tensorComparison_eq] using hq
  rw [ht, hq']
  -- The existing graph theorem gives the inverse-projection form of the same square.
  have h := (sfEtaleGraphProjectionArbitraryBase A e c).2 M K
  change sfEtaleSumExactTensorMap A e M K ≫
    ((derivedTensor (ModuleCat.{u + 1} A) T).map
      ((compactificationEtaleComparison A e c).app M)).app K ≫
    (sfEtaleExactProjectionIso A c M K).hom = _
  rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
end AlgebraicGeometry.Etale
