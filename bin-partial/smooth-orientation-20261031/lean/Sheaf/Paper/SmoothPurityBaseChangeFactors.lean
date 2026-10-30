/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.CohomologicalSmoothnessTheorem
public import Sheaf.Paper.SmoothPurityBaseChangeData
public import Sheaf.Paper.VectorPurityNormalization
import Sheaf.Paper.TowerFactorOrientation
import Sheaf.Paper.TowerFactorTensor
import Sheaf.Paper.FiniteSmoothOrientationBaseChange
import all Sheaf.Paper.CohomologicalSmoothnessTheorem
import all Sheaf.AlgebraicGeometry.SmoothTensorDuality

/-! # Base change of the two smooth-purity factors

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.md
(blueprint: det-sp-purity-bc-factors).

Finite coefficients are written in the canonical etale-origin coordinates of
`finiteComparedTensorClause`. Tower coefficients use the section-preserving realization
of the ordinary derived category of strict towers. No input tower is normalized.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

/-- The finite tensor/counit factor, before applying site comparison.
Reuse the dualizing-tensor calculation and commute its maps through symmetry. -/
private theorem tensor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f v) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.ordinaryFinitePullback A a).map
        (Etale.smoothTensorDualityMap A f
          (Etale.isIso_projectionMap_of_finite A f) K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
        ((Etale.ordinaryFinitePullback A f).obj K)
        (Etale.dualizingComplex A f)).hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').map
        (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq K)).app _ ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((Etale.ordinaryFinitePullback A f').obj
          ((Etale.ordinaryFinitePullback A v).obj K))).map
        (Etale.dualizingComplexBaseChangeMap A sq) ≫
      Etale.smoothTensorDualityMap A f'
        (Etale.isIso_projectionMap_of_finite A f')
        ((Etale.ordinaryFinitePullback A v).obj K) := by
  let := Etale.derivedBraidedCategory A X
  let := Etale.derivedBraidedCategory A X'
  rw [Etale.smoothTensorDualityMap_eq, Etale.smoothTensorDualityMap_eq]
  have ht := Etale.CanonicalSmoothBaseChange.dualizing_tensor_base_change A sq K
  dsimp only [Etale.dualizingComplexTensorMap] at ht
  dsimp only [Etale.ordinaryFinitePullback, Etale.dualizingComplexTensorMap]
  rw [Functor.map_comp, Category.assoc, ht]
  have hb := Etale.leftDerivedUpperStar_map_braiding_hom_δ
    (ModuleCat.{u + 1} A) a ((Etale.ordinaryFinitePullback A f).obj K)
    (Etale.dualizingComplex A f)
  simp only [Etale.leftDerivedUpperStar_δ_eq,
    ← Etale.leftDerivedUpperStarTensorIso_hom] at hb
  dsimp only [Etale.ordinaryFinitePullback] at hb
  rw [reassoc_of% hb]
  simp only [Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map]
  rw [← BraidedCategory.braiding_naturality_right_assoc,
    ← BraidedCategory.braiding_naturality_left_assoc]
  rw [whisker_exchange_assoc]

/-- Compose the ordinary orientation and tensor factors to obtain gamma.
Only monoidal pullback naturality and functoriality of tensor are used here. -/
private theorem gamma_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback a f' f v) (K : Etale.DerivedCategoryModule A Y)
    (L : Etale.DerivedCategoryModule A X) (L' : Etale.DerivedCategoryModule A X')
    (alpha : Etale.dualizingComplex A f ≅ L)
    (alpha' : Etale.dualizingComplex A f' ≅ L')
    (t : (Etale.ordinaryFinitePullback A a).obj L ≅ L')
    (ho : (Etale.ordinaryFinitePullback A a).map alpha.inv ≫
      Etale.dualizingComplexBaseChangeMap A sq = t.hom ≫ alpha'.inv)
    (ht : (Etale.ordinaryFinitePullback A a).map
        (Etale.smoothTensorDualityMap A f
          (Etale.isIso_projectionMap_of_finite A f) K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
        ((Etale.ordinaryFinitePullback A f).obj K)
        (Etale.dualizingComplex A f)).hom ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').map
        (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq K)).app _ ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((Etale.ordinaryFinitePullback A f').obj
          ((Etale.ordinaryFinitePullback A v).obj K))).map
        (Etale.dualizingComplexBaseChangeMap A sq) ≫
      Etale.smoothTensorDualityMap A f'
        (Etale.isIso_projectionMap_of_finite A f')
        ((Etale.ordinaryFinitePullback A v).obj K)) :
    (Etale.ordinaryFinitePullback A a).map
        (Etale.FiniteSmoothPurity.gamma A f L alpha K) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
    (Etale.ordinaryFiniteTwistedPullbackComparison A f f' v a L L' K
      ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K)
      t).hom ≫ Etale.FiniteSmoothPurity.gamma A f' L' alpha'
        ((Etale.ordinaryFinitePullback A v).obj K) := by
  dsimp only [Etale.FiniteSmoothPurity.gamma, Etale.FiniteSmoothPurity.puritySource,
    Functor.comp_obj, Functor.flip_obj_obj]
  dsimp only [Etale.ordinaryFinitePullback] at *
  rw [Functor.map_comp, Category.assoc, ht]
  rw [Etale.leftDerivedUpperStarTensorIso_hom_naturality_right_assoc]
  have hn := ((Etale.derivedTensor (ModuleCat.{u + 1} A) X').map
    (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A) sq.toCommSq K)).naturality
      ((Etale.ordinaryFinitePullback A a).map alpha.inv)
  dsimp only [Etale.ordinaryFinitePullback] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, ho, Functor.map_comp]
  simp only [Etale.ordinaryFiniteTwistedPullbackComparison,
    Etale.ordinaryFiniteTensorPullback, Etale.ordinaryFiniteTensorRightMapIso,
    Etale.derivedTensorRightCompLeftDerivedUpperStarIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rfl

/-- Finite-ring orientation, tensor-mate, and purity-map base-change equations.
The two orientations are the ones with the dependency's actual diagonal/Rees/integration
normalization. Applying comparison gives precisely the pro-etale equations on all
constructible finite-Tor representatives, as in finiteComparedTensorClause.
Source: latest blueprint base-change factors, (1), (2), and the consequence
(blueprint: det-sp-purity-bc-factors).

Proof:
1. Apply finite_orientation_base_change to obtain the ordinary orientation identity.
2. Reuse the proved dualizing-tensor base-change calculation. Express the smooth tensor
map as symmetry followed by that map, and commute the exchanges through symmetry.
3. Expand gamma. Naturality of monoidal pullback and of the tensor square comparison
moves the pulled-back orientation next to the unit exchange. Substitute step 1 and use
functoriality of tensor. Apply the comparison functor to all three ordinary equations. -/
theorem finite_factors
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (X Y Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [SmoothOfRelativeDimension d f.left]
    [IsNoetherian (pullback f.left v.left)]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f.left f.left) (pullback.diagonal f.left))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f.left v.left, ⊤)))
    (alpha : Etale.dualizingComplex A f.left ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
    (alpha' : Etale.dualizingComplex A
        (pullback.snd f.left v.left) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f.left v.left)
      d g' hX' alpha') :
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
        ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.inv ≫
          Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f.left v.left)) =
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
        ((Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
          (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
            (pow_pos (Fact.out : ell.Prime).pos n) hA)
          (pullback.fst f.left v.left) hX d).hom ≫ alpha'.inv) ∧
    ∀ K : Etale.DerivedCategoryModule A Y.left,
      Etale.FiniteSmoothPurity.IsCtf A Y.left
        ((Etale.FiniteSmoothPurity.comparison A Y.left).obj K) →
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map
              (Etale.smoothTensorDualityMap A f.left
                (Etale.isIso_projectionMap_of_finite A f.left) K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f.left v.left)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
              (pullback.fst f.left v.left)
              ((Etale.ordinaryFinitePullback A f.left).obj K)
              (Etale.dualizingComplex A f.left)).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f.left v.left)).map
              (Etale.derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f.left v.left).toCommSq K)).app _ ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f.left v.left)).obj
              ((Etale.ordinaryFinitePullback A (pullback.snd f.left v.left)).obj
                ((Etale.ordinaryFinitePullback A v.left).obj K))).map
                  (Etale.dualizingComplexBaseChangeMap A
            (IsPullback.of_hasPullback f.left v.left)) ≫
            Etale.smoothTensorDualityMap A
              (pullback.snd f.left v.left)
              (Etale.isIso_projectionMap_of_finite A (pullback.snd f.left v.left))
              ((Etale.ordinaryFinitePullback A v.left).obj K)) ∧
      (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map
              (Etale.FiniteSmoothPurity.gamma A f.left _ alpha K) ≫
            (Etale.rightDerivedUpperShriekBaseChangeMap A
              (IsPullback.of_hasPullback f.left v.left)).app K) =
        (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map
          ((Etale.ordinaryFiniteTwistedPullbackComparison A f.left
              (pullback.snd f.left v.left) v.left (pullback.fst f.left v.left)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
              (Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d) K
              ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
                (IsPullback.of_hasPullback f.left v.left).toCommSq).symm.app K)
              (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
                (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
                  (pow_pos (Fact.out : ell.Prime).pos n) hA)
                (pullback.fst f.left v.left) hX d)).hom ≫
            Etale.FiniteSmoothPurity.gamma A (pullback.snd f.left v.left) _ alpha'
              ((Etale.ordinaryFinitePullback A v.left).obj K)) := by
  have ho := finite_orientation_base_change D ell _hne X Y Y' f v d n hn A hA
    g g' hX hX' alpha alpha' _ha _ha'
  refine ⟨congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map z) ho, ?_⟩
  intro K _hK
  have ht := tensor_base_change A (IsPullback.of_hasPullback f.left v.left) K
  refine ⟨congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map z) ht, ?_⟩
  apply congrArg (fun z ↦
    (Etale.FiniteSmoothPurity.comparison A (pullback f.left v.left)).map z)
  exact gamma_base_change A (IsPullback.of_hasPullback f.left v.left) K
    _ _ alpha alpha' _ ho ht


/-- Extend an orientation witness by an additional factor calculation.
The generic eliminator keeps the large tower predicates out of case-split motives. -/
private theorem extend_factor_pair
    {S T : Type*} {HS : S → Prop} {HT : T → Prop}
    {HO HF : S → T → Prop}
    (h : ∃ s t, HS s ∧ HT t ∧ HO s t)
    (k : ∀ s t, HS s → HT t → HO s t → HF s t) :
    ∃ s t, HS s ∧ HT t ∧ HO s t ∧ HF s t := by
  obtain ⟨s, t, hs, ht, ho⟩ := h
  exact ⟨s, t, hs, ht, ho, k s t hs ht ho⟩

/-- Compose orientation and tensor-factor squares using only bifunctoriality.
Keeping this argument generic avoids repeated reduction of the tower realizations. -/
private theorem tensor_factors_compose
    {C C' : Type*} [Category C] [Category C']
    (U : C ⥤ C') (T : C × C ⥤ C) (T' : C' × C' ⥤ C')
    {A L W N : C} {A' L' W' N' : C'}
    {a : L ⟶ W} {a' : L' ⟶ W'}
    {e : U.obj W ⟶ W'} {t : U.obj L ⟶ L'}
    {g : T.obj (A, W) ⟶ N} {g' : T'.obj (A', W') ⟶ N'}
    {b : U.obj N ⟶ N'}
    {cL : U.obj (T.obj (A, L)) ⟶ T'.obj (A', U.obj L)}
    {cW : U.obj (T.obj (A, W)) ⟶ T'.obj (A', U.obj W)}
    (hn : U.map (T.map (Prod.mkHom (𝟙 A) a)) ≫ cW =
      cL ≫ T'.map (Prod.mkHom (𝟙 A') (U.map a)))
    (ho : U.map a ≫ e = t ≫ a')
    (ht : U.map g ≫ b = cW ≫ T'.map (Prod.mkHom (𝟙 A') e) ≫ g') :
    U.map (T.map (Prod.mkHom (𝟙 A) a) ≫ g) ≫ b =
      cL ≫ T'.map (Prod.mkHom (𝟙 A') t) ≫
        (T'.map (Prod.mkHom (𝟙 A') a') ≫ g') := by
  rw [U.map_comp, Category.assoc, ht]
  rw [← Category.assoc _ cW, hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc, prod_comp,
    Category.id_comp, ho]

section TowerStatement
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

/-- The tower orientation, tensor-mate, and purity-map identities in the ordinary
derived category of strict towers. The two comparison isomorphisms in the conclusion
are fixed by the coefficient-unit and finite Kummer pullback equations. Their endpoints
are shifted heart objects, where those equations determine the actual maps; they are
not arbitrary isomorphisms. All K range over the full uniform ctf category.
Source: latest blueprint base-change factors, (1), (2), and consequence
(blueprint: det-sp-purity-bc-factors).

Proof:
1. The diagonal cube and section DNC/integration square give the prime-power
orientation identity (lem-sp-diagonal-exchange-cube, lem-sp-section-dnc-integration-square).
2. The mixed coefficient square and finiteGeneralRingSmoothPurity transport it to
all finite quotients. lem-sp-orientation-scalar-tower-transport gives the actual
strict-heart orientation identity, using det-sp-tower-gamma and det-sp-tower-exceptional-bc.
3. lem-sp-proetale-ctf-pullback-domains gives the required uniform transpose domains.
lem-sp-compact-projection-base-change identifies the inverse projection arrows.
4. Apply lem-sp-tensor-counit-exchange-calculus to the specified beta and its counit
mate. This gives the tensor identity in the ambient tower derived category itself.
5. Compose the two identities with the tensor-pullback comparison and twist
reassociation of lem-weil-pbc-ringed-topoi-derived-tensor-pullback. This is the
purity-map identity, with no normalization assumption on the input. -/
theorem tower_factors
    (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (X Y X' Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsNoetherian X'.left] [IsNoetherian Y'.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u'.left f'.left f.left v.left)
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [QuasiCompact f'.left] [HasCompactification f'.left]
    (c : Compactification f.left) (a : SpTowerMate.Data ell E b o q sq c)
    (x : SpTowerShriek.OpenExchange ell E b o)
    (hb : IsIso (SpTowerMate.beta ell E b o q a x))
    (w : SpChartAdmissibility.Twists ell E X.left)
    (w' : SpChartAdmissibility.Twists ell E X'.left)
    (P : TowerPurityAt ell E b o q c d w a.support_closed a.right
      a.adjunction a.levels)
    (P' : TowerPurityAt ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
      a.right' a.adjunction' a.levels')
    (gu : ∀ n : ℕ, SpTowerP1.GeometricCoordinates ell E n u'.left)
    (gv : ∀ n : ℕ, SpTowerP1.GeometricCoordinates ell E n v.left) :
    ∃ (s : (SpTowerShriek.pull ell E b (o.geometry v.left)).obj
        (SpTowerGamma.unit ell E Y.left) ≅ SpTowerGamma.unit ell E Y'.left)
      (t : (SpTowerShriek.pull ell E b (o.geometry u'.left)).obj
        (SpTowerGamma.orderedLine ell E b X.left w d) ≅
          SpTowerGamma.orderedLine ell E b X'.left w' d),
      (∀ n : ℕ, SpTowerP1.WordComparison ell E n
        (SpTowerP1.pullWord ell E n b (o.geometry v.left) (gv n)
          (SpTowerP1.unitWord ell E n Y.left (P.coefficientsY n)))
        (SpTowerP1.unitWord ell E n Y'.left (P'.coefficientsY n)) s.hom
        (((Etale.ordinaryFinitePullback (SpTowerP1.levelRing ell E n) v.left).mapIso
          (Etale.singleFunctorObjUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y.left) ≪≫
          Etale.leftDerivedUpperStarUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) v.left ≪≫
          (Etale.singleFunctorObjUnitIso
            (ModuleCat.{u + 1} (SpTowerP1.levelRing ell E n)) Y'.left).symm).hom)) ∧
      (∀ n : ℕ, SpTowerP1.WordComparison ell E n
        (SpTowerP1.pullWord ell E n b (o.geometry u'.left) (gu n)
          (SpTowerGamma.coefficientWord ell E b X.left w P.roots n
            (P.unitsX n) (P.coefficientsX n) (P.tensors n) d))
        (SpTowerGamma.coefficientWord ell E b X'.left w' P'.roots n
          (P'.unitsX n) (P'.coefficientsX n) (P'.tensors n) d) t.hom
        ((Etale.vectorIntegrationBaseCoefficientPullback (SpTowerP1.levelRing ell E n)
          (ell ^ (n + 1)) (SpTowerP1.levelAnnihilates ell E n)
          (PurityFiniteSetting.purityTwistTransport (SpTowerP1.levelRing ell E n)
            (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
            (SpTowerP1.levelAnnihilates ell E n)) u'.left (P.unitsX n) d).hom)) ∧
      (SpTowerShriek.pull ell E b (o.geometry u'.left)).map P.orientation.hom ≫
          towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s =
        t.hom ≫ P'.orientation.hom ∧
      ∀ K : SpTowerCalculus.C ell E b q Y.left,
        (SpTowerShriek.pull ell E b (o.geometry u'.left)).map
            (towerTensorMap ell E b o q c d w a.support_closed a.right
              a.adjunction a.levels P K) ≫ towerExchange ell E b o q a x hb K =
          (towerTensorComparison ell E b o q a K _).hom ≫
            (SpTowerShriek.tensor ell E b X'.left).map
              (Prod.mkHom (𝟙 _)
                (towerUnitExchange ell E b o q a x hb P.unit_mem P'.unit_mem s)) ≫
            towerTensorMap ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
              a.right' a.adjunction' a.levels' P' ((SpTowerMate.V ell E b o q a).obj K) ∧
        (SpTowerShriek.pull ell E b (o.geometry u'.left)).map
            (towerGamma ell E b o q c d w a.support_closed a.right
              a.adjunction a.levels P K) ≫ towerExchange ell E b o q a x hb K =
          (towerTensorComparison ell E b o q a K _).hom ≫
            (SpTowerShriek.tensor ell E b X'.left).map (Prod.mkHom (𝟙 _) t.hom) ≫
            towerGamma ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
              a.right' a.adjunction' a.levels' P' ((SpTowerMate.V ell E b o q a).obj K) := by
  refine extend_factor_pair (tower_factor_orientation ell E b o q D _hne
    X Y X' Y' f v u' f' sq d c a x hb w w' P P' gu gv) ?_
  intro s t hs _ht ho
  have hten := tower_factor_tensor ell E b o q D _hne
    X Y X' Y' f v u' f' sq d c a x hb w w' P P' gv s hs
  intro K
  refine ⟨hten K, ?_⟩
  let U := SpTowerShriek.pull ell E b (o.geometry u'.left)
  let T := SpTowerShriek.tensor ell E b X.left
  let T' := SpTowerShriek.tensor ell E b X'.left
  let eK := towerExchange ell E b o q a x hb K
  let C := (towerTensorComparison ell E b o q a K
    (SpTowerGamma.orderedLine ell E b X.left w d)).hom
  let tm := towerTensorMap ell E b o q c d w a.support_closed a.right
    a.adjunction a.levels P K
  let tm' := towerTensorMap ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
    a.right' a.adjunction' a.levels' P' ((SpTowerMate.V ell E b o q a).obj K)
  calc
    U.map (towerGamma ell E b o q c d w a.support_closed a.right
        a.adjunction a.levels P K) ≫ eK =
        U.map (T.map (Prod.mkHom (𝟙 _) P.orientation.hom) ≫ tm) ≫ eK :=
      congrArg (fun z ↦ U.map z ≫ eK)
        (towerGamma_eq ell E b o q c d w a.support_closed a.right
          a.adjunction a.levels P K)
    _ = C ≫ T'.map (Prod.mkHom (𝟙 _) t.hom) ≫
        (T'.map (Prod.mkHom (𝟙 _) P'.orientation.hom) ≫ tm') :=
      tensor_factors_compose U T T'
        (towerTensorComparison_naturality ell E b o q a K P.orientation.hom) ho (hten K)
    _ = C ≫ T'.map (Prod.mkHom (𝟙 _) t.hom) ≫
        towerGamma ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
          a.right' a.adjunction' a.levels' P' ((SpTowerMate.V ell E b o q a).obj K) :=
      congrArg (fun z ↦ C ≫ T'.map (Prod.mkHom (𝟙 _) t.hom) ≫ z)
        (towerGamma_eq ell E b o q (c.ofIsPullback sq) d w' a.support_closed'
          a.right' a.adjunction' a.levels' P' ((SpTowerMate.V ell E b o q a).obj K)).symm

end TowerStatement
end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
