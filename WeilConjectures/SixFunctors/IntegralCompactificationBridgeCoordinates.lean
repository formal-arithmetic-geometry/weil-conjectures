/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates
public import WeilConjectures.SixFunctors.ConstantSemilinearGeneratorComparison
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Integral compactification comparison bridge

Source: blueprint main-20261015, fix-lem-exchanges, proof Step 5; the additional
constant/semilinear comparison obligation
(blueprint: def-sf-integral-compactification-site-transport).

The helpers fix the small-site coordinate transports by sections and adjunction mates.
The two composition maps are constructed independently, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- On a cochain representative, the two exact-localization factorizations coincide.
private theorem factor_h_inv
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P : A ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (K : CochainComplex A ℤ) :
    P.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      P.mapDerivedCategoryFactors.inv.app K := by
  have h : P.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      P.mapDerivedCategoryFactors.hom.app K := by
    rw [mapDerivedCategoryFactorsh_hom_app]
    change P.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  apply (cancel_epi (P.mapDerivedCategoryFactorsh.hom.app _)).mp
  rw [Iso.hom_inv_id_app, h, Iso.hom_inv_id_app]
  rfl

private theorem cochain_unit_app
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) : directCochainUnit F K =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) := by
  change (𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _)) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

-- Compare two universal right derived pairs and express their unit equation on complexes.
private theorem normalizedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) [F.Additive] (G : C ⥤ D) [G.Additive]
    (P : A ⥤ C) [P.Additive] [P.IsEquivalence]
    (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (b : F ⋙ Q ≅ P ⋙ G) :
    ∃! d : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
        P.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      DirectSquareNormalization F G P Q F.rightDerivedFunctor G.rightDerivedFunctor
        (directCochainUnit F) (directCochainUnit G) b d := by
  let a := rightDerivedFunctorCompMapDerivedCategoryUnit F Q
  let c := mapDerivedCategoryCompRightDerivedFunctorUnit P G
  let bH : (F ⋙ Q).mapHomotopyCategory (.up ℤ) ≅
      (P ⋙ G).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory b.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory b.inv (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, b.hom_inv_id]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, b.inv_hom_id]; simp }
  let τ := isoWhiskerRight bH DerivedCategory.Qh
  let d : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
    rightDerivedNatIso (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory)
      (P.mapDerivedCategory ⋙ G.rightDerivedFunctor) a c
      (HomotopyCategory.quasiIso A (.up ℤ)) τ
  have hd := rightDerivedNatTrans_fac (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory)
    (P.mapDerivedCategory ⋙ G.rightDerivedFunctor) a c
    (HomotopyCategory.quasiIso A (.up ℤ)) τ.hom
  have a_app (K : CochainComplex A ℤ) :
      a.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
        Q.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          Q.mapDerivedCategory.map (directCochainUnit F K) := by
    simp only [a, rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    change DerivedCategory.Qh.map (𝟙 _) ≫
      Q.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      Q.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj K)) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, factor_h_inv, cochain_unit_app]
  have c_app (K : CochainComplex A ℤ) :
      c.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
        directCochainUnit G ((P.mapHomologicalComplex (.up ℤ)).obj K) ≫
          G.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.inv.app K) := by
    rw [cochain_unit_app, mapDerivedCategoryCompRightDerivedFunctorUnit_app]
    change DerivedCategory.Qh.map (𝟙 _) ≫
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      G.rightDerivedFunctor.map (P.mapDerivedCategoryFactorsh.inv.app _) = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun z ↦ G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫ G.rightDerivedFunctor.map z)
      (factor_h_inv P K)
  have t_app (K : CochainComplex A ℤ) :
      τ.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app K) := by
    rfl
  have translate (e : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ G.rightDerivedFunctor) :
      DirectSquareNormalization F G P Q F.rightDerivedFunctor G.rightDerivedFunctor
        (directCochainUnit F) (directCochainUnit G) b e ↔
        a ≫ whiskerLeft DerivedCategory.Qh e.hom = τ.hom ≫ c := by
    have atK (K : CochainComplex A ℤ) :
        (a ≫ whiskerLeft DerivedCategory.Qh e.hom).app
            ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
          (τ.hom ≫ c).app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ↔
        Q.mapDerivedCategory.map (directCochainUnit F K) ≫
            e.hom.app (DerivedCategory.Q.obj K) ≫
            G.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app K) =
          Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app K) ≫
            directCochainUnit G ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
      rw [NatTrans.comp_app, whiskerLeft_app, NatTrans.comp_app, a_app, c_app, t_app]
      rw [← cancel_epi (Q.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))]
      rw [← cancel_mono (G.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.hom.app K))]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
        ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      erw [G.rightDerivedFunctor.map_id]
      simp only [Category.comp_id]
      rfl
    constructor
    · intro h
      ext X
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      exact (atK K).mpr (h K)
    · intro h K
      exact (atK K).mp (NatTrans.congr_app h _)
  refine ⟨d, (translate d).mpr hd, ?_⟩
  intro e he
  apply Iso.ext
  exact rightDerived_ext (F.rightDerivedFunctor ⋙ Q.mapDerivedCategory) a
    (HomotopyCategory.quasiIso A (.up ℤ)) _ _ _
    ((translate e).mp he |>.trans hd.symm)

-- Apply the equivalence-mate theorem to opposite categories for the inverse direction.
private theorem inverseMate_isIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : D ⥤ E} {V : E ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} [G.IsEquivalence] [H.IsEquivalence]
    (adj : L ⊣ U) (adj' : F ⊣ V) (β : U ⋙ G ≅ H ⋙ V) :
    IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans) := by
  let α := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  let βop : TwoSquare H.op U.op V.op G.op := TwoSquare.mk _ _ _ _ (NatTrans.op β.hom)
  have hi := isIso_mateEquiv_of_isEquivalence adj.op adj'.op βop
  have he : (NatTrans.op α) = (mateEquiv adj.op adj'.op βop).natTrans := by
    ext X
    simp [α, βop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have hX : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

/-- The ordinary termwise direct-image square with explicit whiskering compositors.
Source: Stacks 0941 (blueprint: def-sf-integral-compactification-site-transport). -/
def towerDirectModel {V T : Scheme.{u}} (f : V ⟶ T) :
    ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f ⋙
      towerModel l E T ≅ towerModel l E V ⋙
        (sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E)) :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (ordinaryDirectModel l E f) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

/-- The localization factorization of the exact model transport.
Source: Stacks 05RU (blueprint: def-sf-integral-compactification-site-transport). -/
def modelFactors (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ derivedTowerModel l E T ≅
      (towerModel l E T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (towerModel l E T).mapDerivedCategoryFactors

/-- The universal-unit normalization of a derived direct-image transport: the published
DirectSquareNormalization predicate for the termwise square towerDirectModel, with the
universal derived units and the exact-localization factorizations of the model transports.
Source: Stacks 0D6E, 0941
(blueprint: def-sf-integral-compactification-site-transport). -/
def DirectModelNormalization {V T : Scheme.{u}} (f : V ⟶ T)
    (d : ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f ⋙
        derivedTowerModel l E T ≅
      derivedTowerModel l E V ⋙
        (sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E))) : Prop :=
  DirectSquareNormalization
    (ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E)))
    (towerModel l E V) (towerModel l E T)
    (ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E)))
    (directCochainUnit
      (ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f))
    (directCochainUnit
      ((sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E))))
    (towerDirectModel l E f) d

/-- Universal-unit normalization fixes the derived direct-image transport.
Source: Stacks 0D6E, 0941
(blueprint: def-sf-integral-compactification-site-transport).
Proof: apply universal right derivation to towerDirectModel. Its universal units
satisfy the displayed cochain factorization. Uniqueness of right derivation fixes
this comparison on all complexes, and inverse exact site transport makes it invertible.
The published DirectSquareNormalization predicate, named DirectModelNormalization
here, expresses this equality using the explicit localization-factorization endpoints. -/
theorem directModel_existsUnique {V T : Scheme.{u}} (f : V ⟶ T) :
    ∃! d : ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f ⋙
        derivedTowerModel l E T ≅
      derivedTowerModel l E V ⋙
        (sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E)),
      DirectModelNormalization l E f d := by
  exact normalizedSquare
    (ProEtale.StrictTower.towerDirectImage (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerModulePush (ULift.{u + 1} (constantRing l E)))
    (towerModel l E V) (towerModel l E T) (towerDirectModel l E f)

/-- The unique universal-unit-normalized derived direct-image comparison.
Source: Stacks 0D6E (blueprint: def-sf-integral-compactification-site-transport). -/
def directModel {V T : Scheme.{u}} (f : V ⟶ T) :
    ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) f ⋙
        derivedTowerModel l E T ≅
      derivedTowerModel l E V ⋙
        (sfCbcMorphism f).towerPush (ULift.{u + 1} (constantRing l E)) :=
  (directModel_existsUnique l E f).exists.choose

/-- Pullback transport is the adjunction mate of the normalized derived direct square.
Source: Stacks 07A4 (blueprint: def-sf-integral-compactification-site-transport). -/
def pullModelMap {V T : Scheme.{u}} (f : V ⟶ T) :=
  ((mateEquiv (ProEtale.StrictTower.adj (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerAdjunction (ULift.{u + 1} (constantRing l E)))).symm
      (TwoSquare.mk _ _ _ _ (directModel l E f).hom)).natTrans

/-- Exact site equivalence makes the pullback mate invertible.
Source: Stacks 00VC, 07A4
(blueprint: def-sf-integral-compactification-site-transport).
Proof: transport the original derived adjunction through the exact site equivalences.
The normalized right comparison identifies its right adjoint. Uniqueness of left
adjoints identifies the mate with the resulting invertible pullback comparison. -/
theorem pullModelMap_isIso {V T : Scheme.{u}} (f : V ⟶ T) :
    IsIso (pullModelMap l E f) := by
  exact inverseMate_isIso
    (ProEtale.StrictTower.adj (ULift.{u + 1} (constantRing l E)) f)
    ((sfCbcMorphism f).towerAdjunction (ULift.{u + 1} (constantRing l E)))
    (directModel l E f)

/-- The canonical pullback transport with its derived adjunction normalization.
Source: Stacks 07A4 (blueprint: def-sf-integral-compactification-site-transport). -/
def pullModel {V T : Scheme.{u}} (f : V ⟶ T) :=
  @asIso _ _ _ _ (pullModelMap l E f) (pullModelMap_isIso l E f)

/-- The inverse-direction open transport is the mate of pullModel.
Source: Stacks 03DI, 07A7
(blueprint: def-sf-integral-compactification-site-transport). -/
def openModelMap {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :=
  ((mateEquiv (ProEtale.StrictTower.jAdj (ULift.{u + 1} (constantRing l E)) j)
    (constantTowerOpenAdj l E j a)).symm
      (TwoSquare.mk _ _ _ _ (pullModel l E j).inv)).natTrans

/-- The unit-normalized open mate is invertible, including the empty open.
Source: Stacks 03DI, 03DJ
(blueprint: def-sf-integral-compactification-site-transport).
Proof: the exact small-site equivalences carry the original open adjunction to the
small-model open adjunction. Their inverse images agree by pullModel; uniqueness of
left adjoints identifies this mate with the canonical invertible comparison. -/
theorem openModelMap_isIso {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :
    IsIso (openModelMap l E j a) := by
  exact inverseMate_isIso
    (ProEtale.StrictTower.jAdj (ULift.{u + 1} (constantRing l E)) j)
    (constantTowerOpenAdj l E j a) (pullModel l E j).symm

/-- Open transport in the forward direction, with the same adjunction normalization.
Source: Stacks 03DI (blueprint: def-sf-integral-compactification-site-transport). -/
def openModel {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j]
    (a : sfCbcModelExtension j (constantRing l E) ⊣
      (sfCbcMorphism j).modulePull (ULift.{u + 1} (constantRing l E))) :=
  (@asIso _ _ _ _ (openModelMap l E j a) (openModelMap_isIso l E j a)).symm



end WeilConjectures.IntegralCompactificationBridge
