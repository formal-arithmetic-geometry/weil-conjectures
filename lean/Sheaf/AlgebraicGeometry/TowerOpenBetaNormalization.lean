/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import all Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import all Sheaf.AlgebraicGeometry.TowerSquareUnitSections
import Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
import Sheaf.CategoryTheory.DerivedExactCube

/-!
# Open-unit normalization of base change on strict constant towers

Source: Stacks Project, Tags 09AE and 04J0; the final coherence sentence of
`thm-cbc-complete-proetale.proof.md`, main-20261015
(blueprint: lem-cbc-tower-open-beta-normalization).

All derived categories are ordinary unbounded derived categories of strict diagrams.
The natural transformations are compared before any derived evaluation is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The specified module inverse-image/direct-image adjunction, without new choices.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modulePullback B f ⊣ moduleDirectImage B f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)

/-- The canonical restriction of a section to an object over the open: apply the
module adjunction unit and restrict along the unit of composition/base change of sites.
Source: Stacks, Tags 09AE and 04J0
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaSection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : Modules B X) (V : U.ProEt) :
    M.val.obj (op ((MorphismProperty.Over.map (f := j) ⊤
      (inferInstance : WeaklyEtale j)).obj V)) →
        ((modulePullback B j).obj M).val.obj (op V) :=
  fun x ↦ ((modulePullback B j).obj M).val.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial).unit.app V).op
        (((openBetaModuleAdj B j).unit.app M).val.app
          (op ((MorphismProperty.Over.map (f := j) ⊤
            (inferInstance : WeaklyEtale j)).obj V)) x)

/-- The map from the pulled-back object over the upper open to the same test object
pulled back over the ambient scheme. Both projections are the specified ones.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaSectionObjectMap {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g) (V : U.ProEt) :
    (MorphismProperty.Over.map (f := j') ⊤ (inferInstance : WeaklyEtale j')).obj
        ((Scheme.proEtaleBaseChange a).obj V) ⟶
      (Scheme.proEtaleBaseChange g).obj
        ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst V.hom a) (pullback.snd V.hom a ≫ j')
      (by
        change pullback.fst V.hom a ≫ (V.hom ≫ j) =
          (pullback.snd V.hom a ≫ j') ≫ g
        rw [Category.assoc, ← w, ← Category.assoc, pullback.condition, Category.assoc]))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd _ g = pullback.snd V.hom a ≫ j'
      simp)

/-- The restriction/direct-image exchange transformation is the mate of the canonical
inverse-image compositor square; its section normalization is asserted below.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaRestriction {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) :
    moduleDirectImage B g ⋙ modulePullback B j ⟶
      modulePullback B j' ⋙ moduleDirectImage B a :=
  (mateEquiv (openBetaModuleAdj B g) (openBetaModuleAdj B a)
    (TwoSquare.mk _ _ _ _ (moduleSquareG B a j' j g w).inv)).natTrans

set_option backward.isDefEq.respectTransparency false in
private theorem openBetaModuleJUnit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (moduleJAdj B j).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A j).unit :=
    (openImmersionAdjunctionTriple A j).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A j)
  let ff := (openImmersionLowerShriekAdjunction A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact unit_iso_of_comparison (L := moduleJ B j) (R := modulePullback B j)
    (moduleJAdj B j) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A j) (fixedOpen B j)

/-- The specified inverse open-unit transpose is invertible for arbitrary constant B.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: conjugate the section-normalized right-adjoint comparison under the composite
adjunctions (def-weil-pbc-composite-adjunction,
lem-weil-pbc-conjugate-iso-unit-equation). The iterated-mate formula
lem-trf-iterated-square-mates identifies its inverse with `singleBetaInv`.
The transpose formula lem-pur-adjunction-mate-transpose gives precisely the pulled-back
open unit, so injectivity of the Hom equivalence proves the identification. -/
theorem openBetaModule_isIso {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) : IsIso (singleBetaInv B a j' j g w) := by
  have := openBetaModuleJUnit B j
  have := openBetaModuleJUnit B j'
  let fm := (moduleJAdj B j').fullyFaithfulLOfIsIsoUnit
  have := fm.full
  have := fm.faithful
  have hi (M : Modules B U) : IsIso ((singleBetaInv B a j' j g w).app M) := by
    have : IsIso ((moduleJAdj B j').counit.app
        ((modulePullback B g).obj ((moduleJ B j).obj M))) :=
      (moduleJAdj B j').isIso_counit_app_of_iso ((moduleOpenSquare B a j' j g sq).app M)
    change IsIso (singleBetaInvApp B a j' j g w M)
    unfold singleBetaInvApp
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The sheaf comparison is the inverse of the prescribed open-unit transpose.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModule {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    moduleJ B j ⋙ modulePullback B g ≅ modulePullback B a ⋙ moduleJ B j' :=
  (@asIso _ _ _ _ (singleBetaInv B a j' j g w)
    (openBetaModule_isIso B a j' j g w sq)).symm

/-- The left-adjoint comparison of the section-normalized restriction is exactly the
open-unit-normalized sheaf comparison, including the specified direction.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: apply conjugate-iso uniqueness to the two composite adjunctions. The iterated
mate identity identifies the resulting inverse with the left open mate of the square
compositor. Apply the mate-transpose identity to the identity of j_!M; its transpose
is the open unit. This proves the formula and its uniqueness. -/
theorem openBetaModule_normalized {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    (conjugateEquiv ((moduleJAdj B j).comp (openBetaModuleAdj B g))
      ((openBetaModuleAdj B a).comp (moduleJAdj B j'))
      (openBetaModule B a j' j g w sq).inv) = openBetaRestriction B a j' j g w ∧
    (∀ M : Modules B U,
      (moduleJAdj B j').homEquiv _ _ ((openBetaModule B a j' j g w sq).inv.app M) =
        (modulePullback B a).map ((moduleJAdj B j).unit.app M) ≫
          (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj M)) := by
  have hm : mateEquiv (moduleJAdj B j) (moduleJAdj B j')
      (TwoSquare.mk _ _ _ _ (singleBetaInv B a j' j g w)) =
        TwoSquare.mk _ _ _ _ (moduleSquareG B a j' j g w).inv := by
    apply mateEquiv_eq_of_unit
    intro M
    symm
    exact ((moduleJAdj B j').homEquiv _ _).apply_symm_apply _
  constructor
  · change conjugateEquiv _ _ (singleBetaInv B a j' j g w) = _
    rw [← iterated_mateEquiv_conjugateEquiv (moduleJAdj B j) (moduleJAdj B j')
      (openBetaModuleAdj B a) (openBetaModuleAdj B g), hm]
    rfl
  · intro M
    exact ((moduleJAdj B j').homEquiv _ _).apply_symm_apply _

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] moduleGComp moduleRComp moduleSquareG modulePullback
attribute [local irreducible] constantRingIso

attribute [local irreducible] gComp gId adj jAdj G R J alpha

private theorem moduleGComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (modulePullback B j) (moduleGId B U).hom =
      (eqToIso (congrArg (modulePullback B) (Category.id_comp j))).hom := by
  apply NatTrans.ext
  funext N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_epi ((eqToIso
    (congrArg (modulePullback B) (Category.id_comp j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using ordinary_left_unit j B N

private theorem moduleGComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (moduleGComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (moduleGId B X).hom (modulePullback B j) =
      (eqToIso (congrArg (modulePullback B) (Category.comp_id j))).hom := by
  apply NatTrans.ext
  funext N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  apply (cancel_epi ((eqToIso
    (congrArg (modulePullback B) (Category.comp_id j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using ordinary_right_unit j B N

private theorem gComp_id_left {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp B (𝟙 U) j).hom ≫
        Functor.whiskerLeft (G B j) (gId B U).hom =
      (eqToIso (congrArg (G B) (Category.id_comp j))).hom := by
  apply NatTrans.ext
  funext N
  have h := NatTrans.congr_app (congrArg Iso.hom (gCompEq_left_unit j B)) N
  simp only [gCompEq, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Iso.refl_hom,
    NatTrans.id_app] at h
  erw [Category.comp_id] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_epi ((eqToIso
    (congrArg (G B) (Category.id_comp j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id, NatTrans.id_app] using h

private theorem gComp_id_right {U X : Scheme.{u}} (j : U ⟶ X) :
    (gComp B j (𝟙 X)).hom ≫
        Functor.whiskerRight (gId B X).hom (G B j) =
      (eqToIso (congrArg (G B) (Category.comp_id j))).hom := by
  apply NatTrans.ext
  funext N
  have h := NatTrans.congr_app (congrArg Iso.hom (gCompEq_right_unit j B)) N
  simp only [gCompEq, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Iso.refl_hom,
    NatTrans.id_app] at h
  erw [Category.comp_id ((G B j).map ((gId B X).hom.app N))] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  apply (cancel_epi ((eqToIso
    (congrArg (G B) (Category.comp_id j).symm)).hom.app N)).1
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id, NatTrans.id_app] using h

private theorem squareG_id {U X : Scheme.{u}} (j : U ⟶ X)
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (N : Derived B X) :
    (squareG B (𝟙 U) j j (𝟙 X) h).inv.app N ≫
        (G B j).map ((gId B X).hom.app N) =
      (gId B U).hom.app ((G B j).obj N) := by
  have hl := congr_app (gComp_id_left B j) N
  have hr := congr_app (gComp_id_right B j) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hl hr
  have ht : (eqToIso (congrArg (G B) h)).hom ≫
      (eqToIso (congrArg (G B) (Category.comp_id j))).hom =
        (eqToIso (congrArg (G B) (Category.id_comp j))).hom := by
    simp only [eqToIso.hom, eqToHom_trans]
  have htN := congr_app ht N
  simp only [NatTrans.comp_app] at htN
  simp only [squareG, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.inv, Category.assoc]
  change (gComp B (𝟙 U) j).inv.app N ≫
      (eqToIso (congrArg (G B) h)).hom.app N ≫
      (gComp B j (𝟙 X)).hom.app N ≫
      (G B j).map ((gId B X).hom.app N) = _
  rw [hr, htN, ← hl]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem betaInv_id_aux
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {G₀ : D ⥤ C} (a : L ⊣ G₀)
    {I : C ⥤ C} {H : D ⥤ D} (eI : I ≅ 𝟭 C) (eH : H ≅ 𝟭 D)
    (s : H ⋙ G₀ ≅ G₀ ⋙ I)
    (hs : ∀ N, s.inv.app N ≫ G₀.map (eH.hom.app N) = eI.hom.app (G₀.obj N))
    (M : C) :
    (a.homEquiv _ _).symm (I.map (a.unit.app M) ≫ s.inv.app (L.obj M)) ≫
        eH.hom.app (L.obj M) = L.map (eI.hom.app M) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Category.assoc, hs, Adjunction.homEquiv_unit]
  exact (eI.hom.naturality (a.unit.app M)).trans (a.unit.naturality (eI.hom.app M))

private theorem squareG_flip {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    squareG B r k i p h.symm = (squareG B k r p i h).symm := by
  simp only [squareG, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

private theorem leftAdjointIdIso_transpose
    {C : Type*} [Category* C] {L G₀ : C ⥤ C} (a : L ⊣ G₀)
    (e : G₀ ≅ 𝟭 C) (N : C) :
    a.unit.app N ≫ G₀.map ((Adjunction.leftAdjointIdIso a e).hom.app N) =
      e.inv.app N := by
  have h := unit_conjugateEquiv Adjunction.id a (Adjunction.leftAdjointIdIso a e).hom N
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  simpa only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp]
    using h.symm

private theorem jId_transpose (X : Scheme.{u}) (N : Derived B X) :
    (jAdj B (𝟙 X)).unit.app N ≫
        (G B (𝟙 X)).map ((jId B X).hom.app N) = (gId B X).inv.app N := by
  exact leftAdjointIdIso_transpose (jAdj B (𝟙 X)) (gId B X) N

private theorem squareG_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Derived B X) :
    (squareG B p (𝟙 U) (𝟙 X) p h).inv.app N ≫
        (gId B U).hom.app ((G B p).obj N) =
      (G B p).map ((gId B X).hom.app N) := by
  rw [squareG_flip B (𝟙 U) p p (𝟙 X) h.symm, Iso.symm_inv]
  apply (cancel_epi ((squareG B (𝟙 U) p p (𝟙 X) h.symm).inv.app N)).1
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact (squareG_id B p h.symm N).symm

private theorem betaInv_id_open_aux
    {C D : Type*} [Category* C] [Category* D]
    {J₀ G₀ : C ⥤ C} {J₁ G₁ : D ⥤ D} (a₀ : J₀ ⊣ G₀) (a₁ : J₁ ⊣ G₁)
    (F : C ⥤ D) (e₀ : G₀ ≅ 𝟭 C) (e₁ : G₁ ≅ 𝟭 D)
    (j₀ : J₀ ≅ 𝟭 C) (j₁ : J₁ ≅ 𝟭 D) (s : F ⋙ G₁ ≅ G₀ ⋙ F)
    (h₀ : ∀ N, a₀.unit.app N ≫ G₀.map (j₀.hom.app N) = e₀.inv.app N)
    (h₁ : ∀ N, a₁.unit.app N ≫ G₁.map (j₁.hom.app N) = e₁.inv.app N)
    (hs : ∀ N, s.inv.app N ≫ e₁.hom.app (F.obj N) = F.map (e₀.hom.app N))
    (N : C) :
    (a₁.homEquiv _ _).symm (F.map (a₀.unit.app N) ≫ s.inv.app (J₀.obj N)) ≫
        F.map (j₀.hom.app N) = j₁.hom.app (F.obj N) := by
  apply (a₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  dsimp only [Functor.id_obj]
  rw [h₁]
  have hn := s.inv.naturality (j₀.hom.app N)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, h₀]
  apply (cancel_mono (e₁.hom.app (F.obj N))).1
  rw [Category.assoc, hs, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (F.map_id _).trans (Iso.inv_hom_id_app e₁ _).symm

private theorem betaInv_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Derived B X) :
    (betaInv B p (𝟙 U) (𝟙 X) p h).app N ≫
        (G B p).map ((jId B X).hom.app N) =
      (jId B U).hom.app ((G B p).obj N) := by
  exact betaInv_id_open_aux (jAdj B (𝟙 X)) (jAdj B (𝟙 U)) (G B p)
    (gId B X) (gId B U) (jId B X) (jId B U)
    (squareG B p (𝟙 U) (𝟙 X) p h) (jId_transpose B X) (jId_transpose B U)
    (squareG_id_open B p h) N

private theorem iso_unit_cancel {C : Type*} [Category* C] {X Y Z : C}
    (e : X ≅ Y) (a : X ⟶ Z) (b : Y ⟶ Z) (h : e.inv ≫ a = b) : e.hom ≫ b = a := by
  rw [← h, ← Category.assoc, e.hom_inv_id, Category.id_comp]

private theorem beta_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (hsq : IsPullback p (𝟙 U) (𝟙 X) p)
    (N : Derived B X) :
    (beta B p (𝟙 U) (𝟙 X) p h hsq).hom.app N ≫
        (jId B U).hom.app ((G B p).obj N) =
      (G B p).map ((jId B X).hom.app N) := by
  exact iso_unit_cancel ((beta B p (𝟙 U) (𝟙 X) p h hsq).app N) _ _
    (betaInv_id_open B p h N)

private theorem transposed_pasting
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {A : C₀ ⥤ C₁} {B : C₁ ⥤ C₂} {C : C₀ ⥤ C₂}
    {F : D₀ ⥤ D₁} {H : D₁ ⥤ D₂} {K : D₀ ⥤ D₂}
    (c : C ⟶ A ⋙ B) (d : K ⟶ F ⋙ H)
    (t₁ : R₀ ⋙ A ⟶ F ⋙ R₁) (t₂ : R₁ ⋙ B ⟶ H ⋙ R₂)
    (t : R₀ ⋙ C ⟶ K ⋙ R₂)
    (v₁ : A ⋙ L₁ ⟶ L₀ ⋙ F) (v₂ : B ⋙ L₂ ⟶ L₁ ⋙ H)
    (v : C ⋙ L₂ ⟶ L₀ ⋙ K)
    (h₁ : ∀ M, a₁.unit.app (A.obj M) ≫ R₁.map (v₁.app M) =
      A.map (a₀.unit.app M) ≫ t₁.app (L₀.obj M))
    (h₂ : ∀ M, a₂.unit.app (B.obj M) ≫ R₂.map (v₂.app M) =
      B.map (a₁.unit.app M) ≫ t₂.app (L₁.obj M))
    (hv : ∀ M, a₂.unit.app (C.obj M) ≫ R₂.map (v.app M) =
      C.map (a₀.unit.app M) ≫ t.app (L₀.obj M))
    (ht : ∀ N, c.app (R₀.obj N) ≫ B.map (t₁.app N) ≫ t₂.app (F.obj N) =
      t.app N ≫ R₂.map (d.app N)) (M : C₀) :
    L₂.map (c.app M) ≫ v₂.app (A.obj M) ≫ H.map (v₁.app M) =
      v.app M ≫ d.app (L₀.obj M) := by
  apply (a₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← reassoc_of% (a₂.unit.naturality (c.app M))]
  rw [reassoc_of% (h₂ (A.obj M)), reassoc_of% (hv M)]
  erw [← t₂.naturality (v₁.app M)]
  dsimp only [Functor.comp_map, Functor.comp_obj]
  rw [← Category.assoc (B.map _), ← B.map_comp, h₁ M, B.map_comp]
  rw [Category.assoc, ← reassoc_of% (c.naturality (a₀.unit.app M))]
  rw [ht]

attribute [local semireducible] G R J adj jAdj gComp gId alpha
set_option backward.isDefEq.respectTransparency true

private def siteSquare {D : Type*} [Category D] [HasPullbacks D]
    (P : MorphismProperty D) [P.IsStableUnderBaseChange]
    {U' U X' X : D} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) :
    MorphismProperty.Over.pullback P ⊤ g ⋙ MorphismProperty.Over.pullback P ⊤ j' ≅
      MorphismProperty.Over.pullback P ⊤ j ⋙ MorphismProperty.Over.pullback P ⊤ a :=
  (MorphismProperty.Over.pullbackComp j' g).symm ≪≫
    eqToIso (congrArg (fun f ↦ MorphismProperty.Over.pullback P ⊤ f) w.symm) ≪≫
      MorphismProperty.Over.pullbackComp a j

private def sectionObjectMap {D : Type*} [Category D] [HasPullbacks D]
    (P : MorphismProperty D) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {U' U X' X : D} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (hj : P j) (hj' : P j') (w : a ≫ j = j' ≫ g) (E : P.Over ⊤ U) :
    (MorphismProperty.Over.map ⊤ hj').obj
        ((MorphismProperty.Over.pullback P ⊤ a).obj E) ⟶
      (MorphismProperty.Over.pullback P ⊤ g).obj
        ((MorphismProperty.Over.map ⊤ hj).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst E.hom a) (pullback.snd E.hom a ≫ j') (by
      change pullback.fst E.hom a ≫ (E.hom ≫ j) =
        (pullback.snd E.hom a ≫ j') ≫ g
      rw [Category.assoc, ← w, ← Category.assoc, pullback.condition, Category.assoc]))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd _ g = _
      exact pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem siteSquare_unit {D : Type*} [Category D] [HasPullbacks D]
    (P : MorphismProperty D) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {U' U X' X : D} (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (hj : P j) (hj' : P j') (w : a ≫ j = j' ≫ g) (E : P.Over ⊤ U) :
    (MorphismProperty.Over.pullback P ⊤ a).map
      ((MorphismProperty.Over.mapPullbackAdj P ⊤ j hj trivial).unit.app E) ≫
        (siteSquare P a j' j g w).inv.app ((MorphismProperty.Over.map ⊤ hj).obj E) =
      (MorphismProperty.Over.mapPullbackAdj P ⊤ j' hj' trivial).unit.app
        ((MorphismProperty.Over.pullback P ⊤ a).obj E) ≫
          (MorphismProperty.Over.pullback P ⊤ j').map
            (sectionObjectMap P a j' j g hj hj' w E) := by
  have he {A Z : D} {f k : A ⟶ Z} (h : f = k) :
      eqToIso (congrArg (fun f ↦ MorphismProperty.Over.pullback P ⊤ f) h) =
        MorphismProperty.Over.pullbackCongr (P := P) (Q := ⊤) h := by
    cases h
    apply Iso.ext
    apply NatTrans.ext
    funext V
    apply MorphismProperty.Over.Hom.ext
    simp [MorphismProperty.Over.pullbackCongr]
  apply MorphismProperty.Over.Hom.ext
  dsimp only [siteSquare]
  rw [he w.symm]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  dsimp [sectionObjectMap, MorphismProperty.Over.mapPullbackAdj,
    MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
    MorphismProperty.Over.isoMk, MorphismProperty.Comma.isoMk,
    MorphismProperty.Comma.homFromCommaOfIsIso, MorphismProperty.Over.pullback,
    MorphismProperty.Over.map, MorphismProperty.Comma.Hom.comp,
    MorphismProperty.Comma.mapRight, MorphismProperty.Over.mk,
    MorphismProperty.Comma.isoFromComma, MorphismProperty.Over.homMk, Comma.isoMk]
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [Category.assoc, pullback.map]
  · simp [Category.assoc, pullback.map]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem towerSiteSquare_unit {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g) (E : U.ProEt) :
    (Scheme.proEtaleBaseChange a).map
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
        (inferInstance : WeaklyEtale j) trivial).unit.app E) ≫
        (towerSiteSquare a j' j g w).inv.app
          ((MorphismProperty.Over.map (f := j) ⊤ (inferInstance : WeaklyEtale j)).obj E) =
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j'
        (inferInstance : WeaklyEtale j') trivial).unit.app
        ((Scheme.proEtaleBaseChange a).obj E) ≫
          (Scheme.proEtaleBaseChange j').map (openBetaSectionObjectMap a j' j g w E) := by
  exact siteSquare_unit (P := @WeaklyEtale) a j' j g
    (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') w E

set_option backward.isDefEq.respectTransparency false in
private theorem openBetaRestriction_on_unit {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g) (M : Modules B X') (V : X.ProEt)
    (s : M.val.obj (op ((Scheme.proEtaleBaseChange g).obj V))) :
    ((openBetaRestriction B a j' j g w).app M).val.app
      (op ((Scheme.proEtaleBaseChange j).obj V))
        (((openBetaModuleAdj B j).unit.app ((moduleDirectImage B g).obj M)).val.app
          (op V) s) =
    ((modulePullback B j').obj M).val.map
      ((towerSiteSquare a j' j g w).inv.app V).op
        (((openBetaModuleAdj B j').unit.app M).val.app
          (op ((Scheme.proEtaleBaseChange g).obj V)) s) := by
  let N := (moduleDirectImage B g).obj M
  let c := (towerSiteSquare a j' j g w).app V
  let P := (modulePullback B j').obj M
  let t := (((openBetaModuleAdj B j').unit.app
    ((modulePullback B g).obj N)).val.app (op ((Scheme.proEtaleBaseChange g).obj V))
      (((openBetaModuleAdj B g).unit.app N).val.app (op V) s))
  have ha := towerSquare_unit_sections B a j' j g w N V s
  dsimp only [towerUnitSection] at ha
  change _ = _ at ha
  change (((modulePullback B j').map ((openBetaModuleAdj B g).counit.app M)).val.app
    (op ((Scheme.proEtaleBaseChange a).obj ((Scheme.proEtaleBaseChange j).obj V))))
      (((moduleSquareG B a j' j g w).inv.app N).val.app _
        (((openBetaModuleAdj B a).unit.app ((modulePullback B j).obj N)).val.app _
          (((openBetaModuleAdj B j).unit.app N).val.app _ s))) = _
  have ha' := congrArg (fun z ↦
    (((modulePullback B j').map ((openBetaModuleAdj B g).counit.app M)).val.app
      (op ((Scheme.proEtaleBaseChange a).obj ((Scheme.proEtaleBaseChange j).obj V)))) z) ha
  refine ha'.trans ?_
  refine (PresheafOfModules.naturality_apply
    ((modulePullback B j').map ((openBetaModuleAdj B g).counit.app M)).val c.inv.op t).trans ?_
  apply congrArg (fun x ↦ P.val.map c.inv.op x)
  have hg := (openBetaModuleAdj B j').unit.naturality
    ((openBetaModuleAdj B g).counit.app M)
  have hge := congrArg (fun z ↦ z.val.app (op ((Scheme.proEtaleBaseChange g).obj V))
    (((openBetaModuleAdj B g).unit.app N).val.app (op V) s)) hg
  refine hge.symm.trans ?_
  have hf := congrArg (fun z ↦ z.val.app (op V) s)
    ((openBetaModuleAdj B g).right_triangle_components M)
  change ((openBetaModuleAdj B g).counit.app M).val.app
    (op ((Scheme.proEtaleBaseChange g).obj V))
      (((openBetaModuleAdj B g).unit.app N).val.app (op V) s) = s at hf
  exact congrArg (fun x ↦ ((openBetaModuleAdj B j').unit.app M).val.app
    (op ((Scheme.proEtaleBaseChange g).obj V)) x) hf

/-- The section comparison is invertible and is identity on the same pulled-back
sections, expressed using the canonical restriction maps `openBetaSection`.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-open-square-section-restriction-mate).
Proof: conjugate the inverse-image compositor square to the normalized direct-image
square. Its unit equation computes the mate on adjunction-unit sections. Naturality
and the triangle identity remove the direct-image counit. Restriction along the site
adjunction unit gives the asserted formula by fibre-product extensionality. The
composite-adjunction conjugate of the invertible open comparison gives invertibility. -/
theorem openBetaRestriction_normalized {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    IsIso (openBetaRestriction B a j' j g w) ∧
      (∀ (M : Modules B X') (V : U.ProEt)
        (x : ((moduleDirectImage B g).obj M).val.obj
          (op ((MorphismProperty.Over.map (f := j) ⊤
            (inferInstance : WeaklyEtale j)).obj V))),
        ((openBetaRestriction B a j' j g w).app M).val.app (op V)
            (openBetaSection B j ((moduleDirectImage B g).obj M) V x) =
          openBetaSection B j' M ((Scheme.proEtaleBaseChange a).obj V)
            (M.val.map (openBetaSectionObjectMap a j' j g w V).op x)) := by
  constructor
  · rw [← (openBetaModule_normalized B a j' j g w sq).1]
    infer_instance
  · intro M E s
    let V := (MorphismProperty.Over.map (f := j) ⊤
      (inferInstance : WeaklyEtale j)).obj E
    let d := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let d' := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j'
      (inferInstance : WeaklyEtale j') trivial
    let K := Scheme.proEtaleBaseChange a
    let F := Scheme.proEtaleBaseChange j'
    have hk := towerSiteSquare_unit a j' j g w E
    dsimp only [openBetaSection]
    erw [PresheafOfModules.naturality_apply]
    change ((modulePullback B j').obj M).val.map (K.map (d.unit.app E)).op
      (((openBetaRestriction B a j' j g w).app M).val.app
        (op ((Scheme.proEtaleBaseChange j).obj V))
          (((openBetaModuleAdj B j).unit.app ((moduleDirectImage B g).obj M)).val.app
            (op V) s)) = _
    rw [openBetaRestriction_on_unit B a j' j g w M V s]
    erw [← PresheafOfModules.map_comp_apply, ← op_comp, hk, op_comp,
      PresheafOfModules.map_comp_apply]
    congr 1
    exact (PresheafOfModules.naturality_apply
      ((openBetaModuleAdj B j').unit.app M).val
        (openBetaSectionObjectMap a j' j g w E).op s).symm

/-- Apply the sheaf comparison termwise to the strict inverse system, with its
transition maps retained. Source: Stacks, Tag 09AE
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaTower {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    towerJ B j ⋙ towerPullback B g ≅ towerPullback B a ⋙ towerJ B j' :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ (Modules B U) (Modules B X')).mapIso
      (openBetaModule B a j' j g w sq) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

/-- Apply the same natural comparison to every differential of an unbounded complex
of strict towers. Source: Stacks, Tags 09AE and 015F
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaComplex {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    (towerJ B j).mapHomologicalComplex (.up ℤ) ⋙
        (towerPullback B g).mapHomologicalComplex (.up ℤ) ≅
      (towerPullback B a).mapHomologicalComplex (.up ℤ) ⋙
        (towerJ B j').mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (openBetaTower B a j' j g w sq) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

/-- Exact descent of the single-sheaf comparison, without a boundedness restriction.
Source: Stacks, Tags 09AE and 015F
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaSingle {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    (moduleJ B j).mapDerivedCategory ⋙ (modulePullback B g).mapDerivedCategory ≅
      (modulePullback B a).mapDerivedCategory ⋙ (moduleJ B j').mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openBetaModule B a j' j g w sq) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

set_option backward.isDefEq.respectTransparency true in
/-- The derived tower comparison is the exact descent of the specific sheaf comparison,
and its inverse has the specified open-unit transpose before evaluation.
Source: Stacks, Tags 015F, 09AE and 04J0
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: extend the sheaf comparison termwise; naturality gives the transition-map and
chain-map equations. Use lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-localization-universal-property (2),(3) to descend the comparison, its
inverse identities and its transpose equation. The descended units are the specified
jAdj units, so injectivity of their Hom equivalence identifies the result with beta.
No faithfulness of derived evaluations is used. -/
theorem openBetaNormalization {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    beta B a j' j g w sq =
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (openBetaTower B a j' j g w sq) ≪≫
        Functor.mapDerivedCategoryCompIso _ _ ∧
    (∀ M : Derived B U,
      (jAdj B j').homEquiv _ _ ((beta B a j' j g w sq).inv.app M) =
        (G B a).map ((jAdj B j).unit.app M) ≫
          (squareG B a j' j g w).inv.app ((J B j).obj M)) := by
  have hb : betaInv B a j' j g w =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B a) (F₂ := towerJ B j')
        (G₁ := towerJ B j) (G₂ := towerPullback B g)
        (towerSquare (modulePullback B a) (moduleJ B j') (moduleJ B j)
          (modulePullback B g) (openBetaModule B a j' j g w sq).symm)).hom := by
    let e := @asIso _ _ _ _ (singleBetaInv B a j' j g w)
      (openBetaModule_isIso B a j' j g w sq)
    let tw := towerSquare (modulePullback B g) (modulePullback B j')
      (modulePullback B j) (modulePullback B a) (moduleSquareG B a j' j g w)
    have hτ : (Functor.mapDerivedCategorySquareIso
        (F₁ := towerPullback B j) (F₂ := towerPullback B a)
        (G₁ := towerPullback B g) (G₂ := towerPullback B j') tw.symm).hom =
        (squareG B a j' j g w).inv := by
      have he : squareG B a j' j g w = Functor.mapDerivedCategorySquareIso
          (F₁ := towerPullback B g) (F₂ := towerPullback B j')
          (G₁ := towerPullback B j) (G₂ := towerPullback B a) tw :=
        Iso.ext (squareG_lift B a j' j g w)
      rw [he]
      simp only [Functor.mapDerivedCategorySquareIso,
        Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
        Iso.symm_hom, Iso.symm_inv, Category.assoc]
    have hm (K : Modules B U) :
        (moduleJAdj B j').unit.app ((modulePullback B a).obj K) ≫
            (modulePullback B j').map (e.hom.app K) =
          (modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
            (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj K) := by
      simpa only [e, asIso_hom, singleBetaInv, singleBetaInvApp,
        Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj] using
        ((moduleJAdj B j').homEquiv ((modulePullback B a).obj K)
          ((modulePullback B g).obj ((moduleJ B j).obj K))).apply_symm_apply
          ((modulePullback B a).map ((moduleJAdj B j).unit.app K) ≫
            (moduleSquareG B a j' j g w).inv.app ((moduleJ B j).obj K))
    apply NatTrans.ext
    funext M
    apply ((jAdj B j').homEquiv ((G B a).obj M)
      ((G B g).obj ((J B j).obj M))).injective
    change (jAdj B j').homEquiv ((G B a).obj M) ((G B g).obj ((J B j).obj M))
      (betaInvApp B a j' j g w M) = _
    rw [betaInvApp, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    symm
    rw [← hτ, ← exactAdj_jAdj B j, ← exactAdj_jAdj B j']
    dsimp only [tw]
    rw [← towerSquare_symm]
    exact exact_mate_tower (C₁ := Modules B U) (D₁ := Modules B X)
      (C₂ := Modules B U') (D₂ := Modules B X')
      (f₁ := moduleJ B j) (g₁ := modulePullback B j)
      (f₂ := moduleJ B j') (g₂ := modulePullback B j')
      (u := modulePullback B a) (v := modulePullback B g)
      (moduleJAdj B j) (moduleJAdj B j') (moduleSquareG B a j' j g w).symm e hm M
  constructor
  · apply Iso.ext_inv
    rw [show (beta B a j' j g w sq).inv = betaInv B a j' j g w from rfl, hb]
    rw [towerSquare_symm]
    have ht : towerSquare (moduleJ B j) (modulePullback B g) (modulePullback B a)
        (moduleJ B j') (openBetaModule B a j' j g w sq) =
          openBetaTower B a j' j g w sq := by
      unfold towerSquare openBetaTower
      rfl
    rw [ht]
    simp only [Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
  · intro M
    exact ((jAdj B j').homEquiv _ _).apply_symm_apply _

/-- Evaluation is compatible with the specific comparison for every coefficient ring.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization).
Proof: termwise evaluation commutes with inverse image, open extension, their units
and the inverse comparison on complexes. Localization uniqueness descends that
commutative diagram; it compares the actual maps, not just their isomorphism classes. -/
theorem openBetaEvaluation {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) (M : Derived B U) (n : ℕ) :
    (ev B X' n).map ((beta B a j' j g w sq).hom.app M) ≫
        (evalJ B j' n).hom.app ((G B a).obj M) ≫
        (moduleJ B j').mapDerivedCategory.map ((evalG B a n).hom.app M) =
      (evalG B g n).hom.app ((J B j).obj M) ≫
        (modulePullback B g).mapDerivedCategory.map ((evalJ B j n).hom.app M) ≫
        (openBetaSingle B a j' j g w sq).hom.app ((ev B U n).obj M) := by
  have he := evalD_square (moduleJ B j) (modulePullback B g)
    (modulePullback B a) (moduleJ B j') (openBetaModule B a j' j g w sq) M n
  have hb := (openBetaNormalization B a j' j g w sq).1
  change beta B a j' j g w sq =
    Functor.mapDerivedCategorySquareIso (openBetaTower B a j' j g w sq) at hb
  rw [show towerSquare (moduleJ B j) (modulePullback B g) (modulePullback B a)
    (moduleJ B j') (openBetaModule B a j' j g w sq) =
      openBetaTower B a j' j g w sq from by
        unfold towerSquare openBetaTower
        rfl, ← hb] at he
  rw [← evalJ_eq B j n, ← evalJ_eq B j' n, ← evalG_eq B a n, ← evalG_eq B g n] at he
  exact he

/-- The module open compositor conjugate to the specified inverse-image compositor.
Source: Stacks, Tags 09AE and 0DV0
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleJComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    moduleJ B j ⋙ moduleJ B k ≅ moduleJ B (j ≫ k) :=
  Adjunction.leftAdjointCompIso (moduleJAdj B j) (moduleJAdj B k)
    (moduleJAdj B (j ≫ k)) (moduleGComp B j k).symm

/-- The inverse-image identity conjugate to the section-normalized direct-image identity.
Source: Stacks, Tag 07A7 (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleGId (X : Scheme.{u}) : modulePullback B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Adjunction.leftAdjointIdIso (openBetaModuleAdj B (𝟙 X)) (moduleRId B X)

/-- The module open identity, using the specified inverse-image unit comparison.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaModuleJId (X : Scheme.{u}) : moduleJ B (𝟙 X) ≅ 𝟭 (Modules B X) :=
  Adjunction.leftAdjointIdIso (moduleJAdj B (𝟙 X)) (openBetaModuleGId B X)

set_option backward.isDefEq.respectTransparency false

@[irreducible] private def moduleCompEq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    modulePullback B h ≅ modulePullback B g ⋙ modulePullback B f :=
  eqToIso (congrArg (modulePullback B) w.symm) ≪≫ moduleGComp B f g

private theorem moduleCompEq_coherence {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (ab : W ⟶ Y) (bc : X ⟶ Z) (abc : W ⟶ Z)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc) :
    moduleCompEq B a bc abc hr ≪≫
        Functor.isoWhiskerRight (moduleCompEq B b c bc hbc) (modulePullback B a) =
      moduleCompEq B ab c abc hl ≪≫
        Functor.isoWhiskerLeft (modulePullback B c) (moduleCompEq B a b ab hab) := by
  subst ab bc
  cases hr
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [moduleCompEq, eqToIso_refl, Iso.refl_trans, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using ordinary_coherence a b c B M

private theorem moduleSquare_normalize {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) :
    moduleSquareG B k r p i w =
      (moduleCompEq B r i (k ≫ p) w.symm).symm ≪≫
        moduleCompEq B k p (k ≫ p) rfl := by
  rw [moduleSquareG_eq]
  unfold moduleCompEq
  exact normalizeIsoSquare (moduleGComp B r i) (moduleGComp B k p)
    (congrArg (modulePullback B) w.symm)

private theorem moduleCompEq_refl {V W S : Scheme.{u}} (f : V ⟶ W) (k : W ⟶ S) :
    moduleGComp B f k = moduleCompEq B f k (f ≫ k) rfl := by
  unfold moduleCompEq
  exact (Iso.refl_trans _).symm
private theorem moduleSquare_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : Modules B X) :
    (moduleGComp B b a).hom.app ((modulePullback B j).obj N) ≫
        (modulePullback B b).map ((moduleSquareG B a j₁ j g w₁).inv.app N) ≫
        (moduleSquareG B b j₂ j₁ h w₂).inv.app ((modulePullback B g).obj N) =
      (moduleSquareG B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (modulePullback B j₂).map ((moduleGComp B h g).hom.app N) := by
  rw [moduleCompEq_refl B b a, moduleCompEq_refl B h g,
    moduleSquare_normalize B a j₁ j g w₁, moduleSquare_normalize B b j₂ j₁ h w₂,
    moduleSquare_normalize B (b ≫ a) j₂ j (h ≫ g) w]
  simp only [Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have first := NatTrans.congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B b a j (b ≫ a) (a ≫ j) ((b ≫ a) ≫ j)
      rfl rfl rfl (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at first
  have first' := rearrange_square _ _ _ _ first.symm
  rw [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at first'
  rw [reassoc_of% first']
  have second := NatTrans.congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B b j₁ g (b ≫ j₁) (a ≫ j) ((b ≫ a) ≫ j) rfl w₁.symm
      (by rw [Category.assoc, ← w₁, ← Category.assoc]) (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at second
  have second' := rearrange_square _ _ _ _ second
  simp only [NatIso.inv_hom_app] at second'
  rw [reassoc_of% second']
  rw [Iso.hom_inv_id_app_assoc]
  have key := NatTrans.congr_app (congrArg Iso.hom
    (moduleCompEq_coherence B j₂ h g (b ≫ j₁) (h ≫ g) ((b ≫ a) ≫ j)
      w₂.symm rfl (by rw [Category.assoc, ← w₁, ← Category.assoc]) w.symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [← key]

private theorem moduleSquare_id {U X : Scheme.{u}} (j : U ⟶ X)
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (N : Modules B X) :
    (moduleSquareG B (𝟙 U) j j (𝟙 X) h).inv.app N ≫
        (modulePullback B j).map ((moduleGId B X).hom.app N) =
      (moduleGId B U).hom.app ((modulePullback B j).obj N) := by
  have hl := congr_app (moduleGComp_id_left B j) N
  have hr := congr_app (moduleGComp_id_right B j) N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hl hr
  have ht : (eqToIso (congrArg (modulePullback B) h)).hom ≫
      (eqToIso (congrArg (modulePullback B) (Category.comp_id j))).hom =
        (eqToIso (congrArg (modulePullback B) (Category.id_comp j))).hom := by
    simp only [eqToIso.hom, eqToHom_trans]
  have htN := congr_app ht N
  simp only [NatTrans.comp_app] at htN
  simp only [moduleSquareG_eq, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    eqToIso.inv, Category.assoc]
  change (moduleGComp B (𝟙 U) j).inv.app N ≫
      (eqToIso (congrArg (modulePullback B) h)).hom.app N ≫
      (moduleGComp B j (𝟙 X)).hom.app N ≫
      (modulePullback B j).map ((moduleGId B X).hom.app N) = _
  rw [hr, htN, ← hl]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem moduleSquare_flip {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    moduleSquareG B r k i p h.symm = (moduleSquareG B k r p i h).symm := by
  simp only [moduleSquareG_eq, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

private theorem moduleSquare_id_open {U X : Scheme.{u}} (p : U ⟶ X)
    (h : p ≫ (𝟙 X) = (𝟙 U) ≫ p) (N : Modules B X) :
    (moduleSquareG B p (𝟙 U) (𝟙 X) p h).inv.app N ≫
        (moduleGId B U).hom.app ((modulePullback B p).obj N) =
      (modulePullback B p).map ((moduleGId B X).hom.app N) := by
  rw [moduleSquare_flip B (𝟙 U) p p (𝟙 X) h.symm, Iso.symm_inv]
  apply (cancel_epi ((moduleSquareG B (𝟙 U) p p (𝟙 X) h.symm).inv.app N)).1
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact (moduleSquare_id B p h.symm N).symm

/-- Base-change composition before evaluation.
Source: Stacks, Tags 04J0, 09AE and 0B65
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: First paste the section-identity restriction comparisons. Their mates are the
compositor squares, so mate pasting identifies the pasted squares. Taking their
left open mates pastes the inverse beta maps; invert that equation. This is an equation
of sheaf maps before extension to strict towers and complexes. -/
theorem openBetaModuleBaseChangeComp {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    [IsOpenImmersion j] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g))
    (s₁ : IsPullback a j₁ j g) (s₂ : IsPullback b j₂ j₁ h)
    (s : IsPullback (b ≫ a) j₂ j (h ≫ g)) (M : Modules B U) :
    (moduleGComp B h g).hom.app ((moduleJ B j).obj M) ≫
        (modulePullback B h).map ((openBetaModule B a j₁ j g w₁ s₁).hom.app M) ≫
        (openBetaModule B b j₂ j₁ h w₂ s₂).hom.app ((modulePullback B a).obj M) =
      (openBetaModule B (b ≫ a) j₂ j (h ≫ g) w s).hom.app M ≫
        (moduleJ B j₂).map ((moduleGComp B b a).hom.app M) := by
  let e₁ := openBetaModule B a j₁ j g w₁ s₁
  let e₂ := openBetaModule B b j₂ j₁ h w₂ s₂
  let e := openBetaModule B (b ≫ a) j₂ j (h ≫ g) w s
  have hInv : (moduleJ B j₂).map ((moduleGComp B b a).hom.app M) ≫
      e₂.inv.app ((modulePullback B a).obj M) ≫ (modulePullback B h).map (e₁.inv.app M) =
        e.inv.app M ≫ (moduleGComp B h g).hom.app ((moduleJ B j).obj M) := by
    exact transposed_pasting (moduleJAdj B j) (moduleJAdj B j₁) (moduleJAdj B j₂)
      (moduleGComp B b a).hom (moduleGComp B h g).hom
      (moduleSquareG B a j₁ j g w₁).inv (moduleSquareG B b j₂ j₁ h w₂).inv
      (moduleSquareG B (b ≫ a) j₂ j (h ≫ g) w).inv
      (singleBetaInv B a j₁ j g w₁) (singleBetaInv B b j₂ j₁ h w₂)
      (singleBetaInv B (b ≫ a) j₂ j (h ≫ g) w)
      (fun N ↦ by
        simpa only [Adjunction.homEquiv_unit, openBetaModule, Iso.symm_inv, asIso_hom] using
          (openBetaModule_normalized B a j₁ j g w₁ s₁).2 N) (fun N ↦ by
        simpa only [Adjunction.homEquiv_unit, openBetaModule, Iso.symm_inv, asIso_hom] using
          (openBetaModule_normalized B b j₂ j₁ h w₂ s₂).2 N)
      (fun N ↦ by
        simpa only [Adjunction.homEquiv_unit, openBetaModule, Iso.symm_inv, asIso_hom] using
          (openBetaModule_normalized B (b ≫ a) j₂ j (h ≫ g) w s).2 N)
      (moduleSquare_pasting_inv B j j₁ j₂ g h a b w₁ w₂ w) M
  change _ ≫ (modulePullback B h).map (e₁.hom.app M) ≫ e₂.hom.app _ =
    e.hom.app M ≫ _
  apply (cancel_epi (e.inv.app M)).1
  rw [← Category.assoc, ← Category.assoc, ← hInv]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(modulePullback B h).map_id]
  erw [Category.id_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem moduleInv_mate {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g) :
    mateEquiv (moduleJAdj B j) (moduleJAdj B j') (singleBetaInv B a j' j g w) =
      (moduleSquareG B a j' j g w).inv := by
  apply mateEquiv_eq_of_unit
  intro M
  symm
  exact ((moduleJAdj B j').homEquiv _ _).apply_symm_apply _

private theorem moduleJComp_conjugate {U V X : Scheme.{u}} (k : U ⟶ V) (j : V ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] :
    conjugateEquiv (moduleJAdj B (k ≫ j)) ((moduleJAdj B k).comp (moduleJAdj B j))
      (openBetaModuleJComp B k j).hom = (moduleGComp B k j).hom := by
  simp [openBetaModuleJComp, Adjunction.leftAdjointCompIso, conjugateIsoEquiv]

private theorem moduleInv_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (hp : ∀ N : Modules B X,
      (modulePullback B b).map ((moduleGComp B k j).hom.app N) ≫
        (moduleSquareG B b k₁ k a wk).inv.app ((modulePullback B j).obj N) ≫
        (modulePullback B k₁).map ((moduleSquareG B a j₁ j g wj).inv.app N) =
      (moduleSquareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (moduleGComp B k₁ j₁).hom.app ((modulePullback B g).obj N)) :
    singleBetaInv B b (k₁ ≫ j₁) (k ≫ j) g w =
      (((TwoSquare.mk _ _ _ _ (singleBetaInv B b k₁ k a wk)).vComp
        (TwoSquare.mk _ _ _ _ (singleBetaInv B a j₁ j g wj))).whiskerLeft
          (openBetaModuleJComp B k j).hom).whiskerRight (openBetaModuleJComp B k₁ j₁).inv := by
  apply (mateEquiv (moduleJAdj B (k ≫ j)) (moduleJAdj B (k₁ ≫ j₁))).injective
  rw [moduleInv_mate, mateEquiv_conjugateEquiv_vcomp _
    ((moduleJAdj B k₁).comp (moduleJAdj B j₁)),
    conjugateEquiv_mateEquiv_vcomp _ ((moduleJAdj B k).comp (moduleJAdj B j)),
    mateEquiv_hcomp, moduleInv_mate, moduleInv_mate, moduleJComp_conjugate]
  rw [show conjugateEquiv ((moduleJAdj B k₁).comp (moduleJAdj B j₁)) (moduleJAdj B (k₁ ≫ j₁))
    (openBetaModuleJComp B k₁ j₁).inv = (moduleGComp B k₁ j₁).inv from
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _]
  apply TwoSquare.ext
  intro N
  dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  set_option backward.isDefEq.respectTransparency false in
    change _ = ((modulePullback B b).map ((moduleGComp B k j).hom.app N) ≫
    ((moduleSquareG B b k₁ k a wk).inv.app ((modulePullback B j).obj N) ≫
      (modulePullback B k₁).map ((moduleSquareG B a j₁ j g wj).inv.app N))) ≫
        (moduleGComp B k₁ j₁).inv.app ((modulePullback B g).obj N)
  rw [hp N]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- Open composition before evaluation.
Source: Stacks, Tags 04J0, 09AE and 0B65
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: Restriction to successive opens is the same sectionwise restriction. Paste
these restriction comparisons and take successive open mates using the composite
open adjunction. The normalized open compositor is its conjugate. Invert the
resulting inverse-beta equation, the same equation remains valid on sheaves. -/
theorem openBetaModuleOpenComp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : Modules B V) :
    (modulePullback B g).map ((openBetaModuleJComp B k j).inv.app M) ≫
        (openBetaModule B a j₁ j g wj sj).hom.app ((moduleJ B k).obj M) ≫
        (moduleJ B j₁).map ((openBetaModule B b k₁ k a wk sk).hom.app M) ≫
        (openBetaModuleJComp B k₁ j₁).hom.app ((modulePullback B b).obj M) =
      (openBetaModule B b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M := by
  have hp (N : Modules B X) :
      (modulePullback B b).map ((moduleGComp B k j).hom.app N) ≫
        (moduleSquareG B b k₁ k a wk).inv.app ((modulePullback B j).obj N) ≫
        (modulePullback B k₁).map ((moduleSquareG B a j₁ j g wj).inv.app N) =
      (moduleSquareG B b (k₁ ≫ j₁) (k ≫ j) g w).inv.app N ≫
        (moduleGComp B k₁ j₁).hom.app ((modulePullback B g).obj N) := by
    have hh := moduleSquare_pasting_inv B g a b j k j₁ k₁
      wj.symm wk.symm w.symm N
    rw [moduleSquare_flip B a j₁ j g wj, moduleSquare_flip B b k₁ k a wk,
      moduleSquare_flip B b (k₁ ≫ j₁) (k ≫ j) g w] at hh
    simp only [Iso.symm_inv] at hh
    apply (cancel_epi ((moduleSquareG B b (k₁ ≫ j₁) (k ≫ j) g w).hom.app N)).1
    rw [← Category.assoc, ← hh]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [(modulePullback B k₁).map_id, Category.comp_id]
  have hi := congr_app (moduleInv_open_comp B k j k₁ j₁ a b g wk wj w hp) M
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, TwoSquare.natTrans] at hi
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hi
  let e := openBetaModule B b (k₁ ≫ j₁) (k ≫ j) g w s
  let e₁ := openBetaModule B b k₁ k a wk sk
  let e₂ := openBetaModule B a j₁ j g wj sj
  change _ = e.hom.app M
  apply (cancel_epi (e.inv.app M)).1
  change (singleBetaInv B b (k₁ ≫ j₁) (k ≫ j) g w).app M ≫ _ = _
  rw [hi]
  simp only [Category.assoc]
  change (openBetaModuleJComp B k₁ j₁).inv.app _ ≫ (moduleJ B j₁).map (e₁.inv.app M) ≫
    e₂.inv.app ((moduleJ B k).obj M) ≫
      (modulePullback B g).map ((openBetaModuleJComp B k j).hom.app M) ≫
      (modulePullback B g).map ((openBetaModuleJComp B k j).inv.app M) ≫ e₂.hom.app _ ≫
        (moduleJ B j₁).map (e₁.hom.app M) ≫ (openBetaModuleJComp B k₁ j₁).hom.app _ = _
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app]
  erw [(modulePullback B g).map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(moduleJ B j₁).map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- Identity base change under the specified unit identifications.
Source: Stacks, Tags 04J0, 09AE and 0B65
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: The section comparison for identity base change is identity under its unit
identification. Identity and change-of-adjunction laws for mates give the stated
identity under exactly gId, on module sheaves. -/
theorem openBetaModuleBaseChangeId {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : (𝟙 U) ≫ j = j ≫ (𝟙 X)) (hsq : IsPullback (𝟙 U) j j (𝟙 X))
    (M : Modules B U) :
    (openBetaModule B (𝟙 U) j j (𝟙 X) h hsq).hom.app M ≫
        (moduleJ B j).map ((openBetaModuleGId B U).hom.app M) =
      (openBetaModuleGId B X).hom.app ((moduleJ B j).obj M) := by
  have hid := betaInv_id_aux (moduleJAdj B j) (moduleGId B U) (moduleGId B X)
    (moduleSquareG B (𝟙 U) j j (𝟙 X) h) (moduleSquare_id B j h) M
  have he : moduleGId B U = openBetaModuleGId B U := by
    unfold moduleGId openBetaModuleGId openBetaModuleAdj
    rfl
  have he' : moduleGId B X = openBetaModuleGId B X := by
    unfold moduleGId openBetaModuleGId openBetaModuleAdj
    rfl
  rw [he, he'] at hid
  exact iso_unit_cancel ((openBetaModule B (𝟙 U) j j (𝟙 X) h hsq).app M) _ _ hid

/-- Identity open under the specified open-unit identifications, before evaluation.
Source: Stacks, Tags 09AE and 0B65
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: the restriction comparison is identity for identity opens. Its conjugate is
identity under the chosen open units by mate identity and adjunction-change laws.
This equation holds on module sheaves. -/
theorem openBetaModuleOpenId {U X : Scheme.{u}} (g : U ⟶ X)
    (w : g ≫ 𝟙 X = 𝟙 U ≫ g) (sq : IsPullback g (𝟙 U) (𝟙 X) g)
    (M : Modules B X) :
    (openBetaModule B g (𝟙 U) (𝟙 X) g w sq).hom.app M ≫
        (openBetaModuleJId B U).hom.app ((modulePullback B g).obj M) =
      (modulePullback B g).map ((openBetaModuleJId B X).hom.app M) := by
  have hid := betaInv_id_open_aux (moduleJAdj B (𝟙 X)) (moduleJAdj B (𝟙 U))
    (modulePullback B g) (openBetaModuleGId B X) (openBetaModuleGId B U)
    (openBetaModuleJId B X) (openBetaModuleJId B U)
    (moduleSquareG B g (𝟙 U) (𝟙 X) g w)
    (leftAdjointIdIso_transpose _ _) (leftAdjointIdIso_transpose _ _) (by
      simpa only [openBetaModuleGId, openBetaModuleAdj, moduleGId, moduleAdj] using
        moduleSquare_id_open B g w) M
  exact iso_unit_cancel ((openBetaModule B g (𝟙 U) (𝟙 X) g w sq).app M) _ _ hid

/-- Identity open under the specified open-unit identifications, before evaluation.
Source: Stacks, Tags 09AE and 0B65
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: the restriction comparison is identity for identity opens. Its conjugate is
identity under the chosen open units by mate identity and adjunction-change laws.
Exact termwise descent preserves that equation. -/
theorem openBetaOpenId {U X : Scheme.{u}} (g : U ⟶ X)
    (w : g ≫ 𝟙 X = 𝟙 U ≫ g) (sq : IsPullback g (𝟙 U) (𝟙 X) g)
    (M : Derived B X) :
    (beta B g (𝟙 U) (𝟙 X) g w sq).hom.app M ≫
        (jId B U).hom.app ((G B g).obj M) =
      (G B g).map ((jId B X).hom.app M) := by
  exact beta_id_open B g w sq M

/-- The component of the actual complex comparison is the sheaf comparison at the
same tower index and cochain degree. Source: Stacks, Tag 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: whiskering applies a transformation componentwise to the strict tower;
mapping a natural transformation to complexes applies it to every degree. The
composition identifications are identity in each degree. Thus the formula follows
already in the complex category, and in particular retains transitions and differentials. -/
theorem openBetaComplex_component {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) (K : CochainComplex (Towers B U) ℤ)
    (q : ℤ) (n : ℕᵒᵖ) :
    (((openBetaComplex B a j' j g w sq).hom.app K).f q).app n =
      (openBetaModule B a j' j g w sq).hom.app ((K.X q).obj n) := by
  simp only [openBetaComplex, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f]
  change 𝟙 _ ≫ ((openBetaTower B a j' j g w sq).hom.app (K.X q)).app n ≫ 𝟙 _ = _
  change 𝟙 _ ≫ (𝟙 _ ≫
    (openBetaModule B a j' j g w sq).hom.app ((K.X q).obj n) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

section Finite

variable [Finite B] [TopologicalSpace B] [DiscreteTopology B]

/-- Exactness structure of the existing finite realization, by composition of its
published exact functors. Source: Stacks, Tag 03DA
(blueprint: lem-cbc-tower-open-beta-normalization). -/
instance openBetaFinitePresentation_additive (X : Scheme.{u}) :
    (C B X B (RingHom.id B)).Additive :=
  inferInstanceAs
    ((finiteCoefficientRealization X B ⋙ finiteRestriction B X B (RingHom.id B)).Additive)

/-- Exactness structure of the existing finite realization, by composition of its
published exact functors. Source: Stacks, Tag 03DA
(blueprint: lem-cbc-tower-open-beta-normalization). -/
instance openBetaFinitePresentation_finiteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (C B X B (RingHom.id B)) :=
  inferInstanceAs (PreservesFiniteLimits (finiteCoefficientRealization X B ⋙
    finiteRestriction B X B (RingHom.id B)))

/-- Exactness structure of the existing finite realization, by composition of its
published exact functors. Source: Stacks, Tag 03DA
(blueprint: lem-cbc-tower-open-beta-normalization). -/
instance openBetaFinitePresentation_finiteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (C B X B (RingHom.id B)) :=
  inferInstanceAs (PreservesFiniteColimits (finiteCoefficientRealization X B ⋙
    finiteRestriction B X B (RingHom.id B)))

/-- The finite pullback comparison is the inverse mate of the published sectionwise
direct-image comparison, so its normalization is fixed without arbitrary choices.
Source: Stacks, Tags 04J0 and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaFinitePullHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    C B Y B (RingHom.id B) ⋙ modulePullback B f ⟶
      upperStar (ModuleCat.{u + 1} B) f ⋙ C B X B (RingHom.id B) :=
  ((mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (openBetaModuleAdj B f)).symm
      (TwoSquare.mk _ _ _ _ (cDirect B f B (RingHom.id B)).hom)).natTrans

/-- This particular mate is invertible because the two scalar presentations are
equivalences; no invertibility of arbitrary mates is asserted.
Source: Stacks, Tags 03DA and 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: use realization_equivalence from FiniteOpenBaseChangeNormalized at both endpoints.
Transport the
fixed-module pullback adjunction through these equivalences; the direct-image
comparison cDirect then identifies right adjoints. Unique left-adjoint comparison
is invertible and its conjugate normalization identifies it with the displayed mate. -/
theorem openBetaFinitePullHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (openBetaFinitePullHom B f) := by
  let := realization_equivalence B X
  let := realization_equivalence B Y
  exact inverseMate_isIso_of_equivalences (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (openBetaModuleAdj B f) (TwoSquare.mk _ _ _ _ (cDirect B f B (RingHom.id B)).hom)

/-- The unit-preserving finite pullback comparison of the two coefficient presentations.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaFinitePull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    C B Y B (RingHom.id B) ⋙ modulePullback B f ≅
      upperStar (ModuleCat.{u + 1} B) f ⋙ C B X B (RingHom.id B) :=
  @asIso _ _ _ _ (openBetaFinitePullHom B f) (openBetaFinitePullHom_isIso B f)

/-- Open extension comparison as the inverse mate of the already normalized
restriction comparison. Source: Stacks, Tag 09AE
(blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaFiniteOpenHom {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    C B U B (RingHom.id B) ⋙ moduleJ B j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙ C B X B (RingHom.id B) :=
  ((mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (moduleJAdj B j)).symm
      (TwoSquare.mk _ _ _ _ (openBetaFinitePull B j).inv)).natTrans

/-- The unit-preserving comparison of open extensions in equivalent presentations
is invertible. Source: Stacks, Tag 09AE
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: transfer the open adjunction through the two realization equivalences, identify
its right adjoint by openBetaFinitePull, and apply unique left-adjoint comparison.
The adjunction-unit equation identifies that isomorphism with the specified mate. -/
theorem openBetaFiniteOpenHom_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (openBetaFiniteOpenHom B j) := by
  let := realization_equivalence B U
  let := realization_equivalence B X
  exact inverseMate_isIso_of_equivalences
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (moduleJAdj B j) (TwoSquare.mk _ _ _ _ (openBetaFinitePull B j).inv)

/-- The canonical finite open-extension comparison retaining the open adjunction unit.
Source: Stacks, Tag 09AE (blueprint: lem-cbc-tower-open-beta-normalization). -/
def openBetaFiniteOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    C B U B (RingHom.id B) ⋙ moduleJ B j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙ C B X B (RingHom.id B) :=
  @asIso _ _ _ _ (openBetaFiniteOpenHom B j) (openBetaFiniteOpenHom_isIso B j)

section FiniteComparisonProof

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] C openBetaFinitePull openBetaFiniteOpen
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  upperStar upperStarLowerStarAdjunction upperStarComp upperStarCompIso upperStarCongr

private lemma finiteMateSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

private lemma finitePull_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (openBetaModuleAdj B f) (openBetaFinitePull B f).hom =
        TwoSquare.mk _ _ _ _ (cDirect B f B (RingHom.id B)).hom := by
  unfold openBetaFinitePull openBetaFinitePullHom
  exact (mateEquiv _ _).apply_symm_apply _

private lemma finiteDirect_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (Y : Y.ProEtᵒᵖ)
    (m : ((C B _ B (RingHom.id B)).obj
      ((lowerStar (ModuleCat.{u + 1} B) f).obj F)).val.obj Y) :
    ((cUnderlying B X B (RingHom.id B)).hom.app F).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj Y)
        (((cDirect B f B (RingHom.id B)).hom.app F).val.app Y m) =
      ((cUnderlying B _ B (RingHom.id B)).hom.app
        ((lowerStar (ModuleCat.{u + 1} B) f).obj F)).hom.app Y m :=
  (Classical.choose_spec (cDirect_existsUnique B f B (RingHom.id B))).1 F Y m

private lemma finiteUnderlying_map {X : Scheme.{u}}
    {F F' : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)}
    (h : F ⟶ F') (Y : X.ProEtᵒᵖ)
    (m : ((C B X B (RingHom.id B)).obj F).val.obj Y) :
    ((cUnderlying B X B (RingHom.id B)).hom.app F').hom.app Y
        (((C B X B (RingHom.id B)).map h).val.app Y m) =
      h.hom.app Y (((cUnderlying B X B (RingHom.id B)).hom.app F).hom.app Y m) := by
  have ht := (cUnderlying B X B (RingHom.id B)).hom.naturality h
  exact ConcreteCategory.congr_hom (congr_app (congrArg
    (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map ht) Y) m

private lemma finiteUnderlying_restrict {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    {Y Z : X.ProEtᵒᵖ} (h : Y ⟶ Z)
    (m : ((C B X B (RingHom.id B)).obj F).val.obj Y) :
    ((cUnderlying B X B (RingHom.id B)).hom.app F).hom.app Z
        (((C B X B (RingHom.id B)).obj F).val.map h m) =
      F.obj.map h (((cUnderlying B X B (RingHom.id B)).hom.app F).hom.app Y m) := by
  exact ConcreteCategory.congr_hom
    (((cUnderlying B X B (RingHom.id B)).hom.app F).hom.naturality h) m

private lemma finitePull_compSquare {V W Z : Scheme.{u}}
    (f : V ⟶ W) (g : W ⟶ Z) :
    ((TwoSquare.mk _ _ _ _ (openBetaFinitePull B g).hom).vComp
      (TwoSquare.mk _ _ _ _ (openBetaFinitePull B f).hom)).whiskerRight
        (moduleGComp B f g).hom =
      (TwoSquare.mk _ _ _ _ (openBetaFinitePull B (f ≫ g)).hom).whiskerLeft
        (upperStarComp (ModuleCat.{u + 1} B) f g).hom := by
  let q := (TwoSquare.mk _ _ _ _ (openBetaFinitePull B g).hom).vComp
    (TwoSquare.mk _ _ _ _ (openBetaFinitePull B f).hom)
  have hc : q.whiskerRight (moduleGComp B f g).hom =
      (TwoSquare.mk _ _ _ _ (openBetaFinitePull B (f ≫ g)).hom).whiskerLeft
        (upperStarComp (ModuleCat.{u + 1} B) f g).hom := by
    apply finiteMateSquare
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) (f ≫ g))
      ((openBetaModuleAdj B g).comp (openBetaModuleAdj B f))
      (openBetaModuleAdj B (f ≫ g))
    dsimp only [q]
    rw [mateEquiv_hcomp, finitePull_mate, finitePull_mate, finitePull_mate]
    have hm : conjugateEquiv ((openBetaModuleAdj B g).comp (openBetaModuleAdj B f))
        (openBetaModuleAdj B (f ≫ g)) (moduleGComp B f g).hom =
          (moduleRComp B f g).hom := by
      simpa only [moduleGComp, openBetaModuleAdj, modulePullback, moduleDirectImage,
        Modules, Iso.symm_hom] using!
        (Adjunction.conjugateEquiv_leftAdjointCompIso_inv
          (Scheme.proEtaleRingModuleAdjunction g (coefficients B Z)
            (coefficients B W) (constantRingIso B g))
          (Scheme.proEtaleRingModuleAdjunction f (coefficients B W)
            (coefficients B V) (constantRingIso B f))
          (Scheme.proEtaleRingModuleAdjunction (f ≫ g) (coefficients B Z)
            (coefficients B V) (constantRingIso B (f ≫ g))) (moduleRComp B f g))
    rw [hm]
    rw [conjugateEquiv_upperStarComp_hom]
    apply TwoSquare.ext
    intro N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, TwoSquare.natTrans]
    apply (ConcreteCategory.bijective_of_isIso
      (((cUnderlying B V B (RingHom.id B)).hom.app N).hom.app
        ((Scheme.proEtaleBaseChange (f ≫ g)).op.obj Y))).1
    obtain ⟨Y⟩ := Y
    erw [directComp_hom_apply f g B]
    erw [finiteUnderlying_restrict]
    erw [directImage_map_apply g B, finiteDirect_apply, finiteDirect_apply,
      finiteDirect_apply]
    erw [finiteUnderlying_map, lowerStarComp_hom_app_hom_app]
    rfl
  exact hc

private lemma finiteSquareTransport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {α : Sort*} (P : α → C ⥤ D) (Q : α → E ⥤ F)
    (R : E ⥤ C) (S : F ⥤ D) (q : ∀ x, TwoSquare R (Q x) (P x) S)
    {x y : α} (h : x = y)
    {P₁ P₂ : C ⥤ D} {Q₁ Q₂ : E ⥤ F}
    (a : P x ≅ P₁) (a' : P y ≅ P₂) (b : Q x ≅ Q₁) (b' : Q y ≅ Q₂)
    (p : TwoSquare R Q₁ P₁ S) (p' : TwoSquare R Q₂ P₂ S)
    (ha : p.whiskerRight a.hom = (q x).whiskerLeft b.hom)
    (ha' : p'.whiskerRight a'.hom = (q y).whiskerLeft b'.hom)
    (z : P₂ ≅ P₁) (w : Q₁ ≅ Q₂)
    (hz : z = a'.symm ≪≫ eqToIso (congrArg P h.symm) ≪≫ a)
    (hw : w = b.symm ≪≫ eqToIso (congrArg Q h) ≪≫ b') :
    p'.whiskerRight z.inv = p.whiskerLeft w.hom := by
  rw [hz, hw]
  subst y
  have h₁ (M : E) := congrArg (fun t ↦ t.natTrans.app M) ha
  have h₂ (M : E) := congrArg (fun t ↦ t.natTrans.app M) ha'
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁ h₂
  apply TwoSquare.ext
  intro M
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, eqToIso_refl,
    Iso.refl_trans, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a.hom.app (R.obj M))).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [h₂, reassoc_of% (h₁ M), ← S.map_comp_assoc, Iso.hom_inv_id_app,
    S.map_id, Category.id_comp]

private lemma finiteSquareComponents
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂) (R₃ : C₃ ⥤ D₃)
    (Qj : C₀ ⥤ C₁) (Qg : C₀ ⥤ C₂) (Qa : C₁ ⥤ C₃) (Qj' : C₂ ⥤ C₃)
    (Pj : D₀ ⥤ D₁) (Pg : D₀ ⥤ D₂) (Pa : D₁ ⥤ D₃) (Pj' : D₂ ⥤ D₃)
    (αj : R₀ ⋙ Pj ⟶ Qj ⋙ R₁) (αg : R₀ ⋙ Pg ⟶ Qg ⋙ R₂)
    (αa : R₁ ⋙ Pa ⟶ Qa ⋙ R₃) (αj' : R₂ ⋙ Pj' ⟶ Qj' ⋙ R₃)
    (z : Pg ⋙ Pj' ≅ Pj ⋙ Pa) (w : Qj ⋙ Qa ≅ Qg ⋙ Qj')
    (h : ((TwoSquare.mk _ _ _ _ αg).vComp (TwoSquare.mk _ _ _ _ αj')).whiskerRight
        z.inv =
      ((TwoSquare.mk _ _ _ _ αj).vComp (TwoSquare.mk _ _ _ _ αa)).whiskerLeft w.hom)
    (N : C₀) :
    z.inv.app (R₀.obj N) ≫ Pj'.map (αg.app N) ≫ αj'.app (Qg.obj N) =
      Pa.map (αj.app N) ≫ αa.app (Qj.obj N) ≫ R₃.map (w.hom.app N) := by
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
    using congrArg (fun t ↦ t.natTrans.app N) h

private lemma finitePull_square {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    (w : a ≫ j = j' ≫ g)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (moduleSquareG B a j' j g w).inv.app ((C B X B (RingHom.id B)).obj N) ≫
      (modulePullback B j').map ((openBetaFinitePull B g).hom.app N) ≫
      (openBetaFinitePull B j').hom.app ((upperStar (ModuleCat.{u + 1} B) g).obj N) =
    (modulePullback B a).map ((openBetaFinitePull B j).hom.app N) ≫
      (openBetaFinitePull B a).hom.app ((upperStar (ModuleCat.{u + 1} B) j).obj N) ≫
      (C B U' B (RingHom.id B)).map ((upperStarCompIso (ModuleCat.{u + 1} B) w).hom.app N) := by
  let p := (TwoSquare.mk _ _ _ _ (openBetaFinitePull B j).hom).vComp
    (TwoSquare.mk _ _ _ _ (openBetaFinitePull B a).hom)
  let p' := (TwoSquare.mk _ _ _ _ (openBetaFinitePull B g).hom).vComp
    (TwoSquare.mk _ _ _ _ (openBetaFinitePull B j').hom)
  have hw : upperStarCompIso (ModuleCat.{u + 1} B) w =
      (upperStarComp (ModuleCat.{u + 1} B) a j).symm ≪≫
      eqToIso (congrArg (upperStar (ModuleCat.{u + 1} B)) w) ≪≫
      upperStarComp (ModuleCat.{u + 1} B) j' g := by
    simp only [upperStarCompIso, upperStarCongr]
  have hs := finiteSquareTransport (modulePullback B) (upperStar (ModuleCat.{u + 1} B))
    (C B X B (RingHom.id B)) (C B U' B (RingHom.id B))
    (fun f ↦ TwoSquare.mk _ _ _ _ (openBetaFinitePull B f).hom) w
    (moduleGComp B a j) (moduleGComp B j' g)
    (upperStarComp (ModuleCat.{u + 1} B) a j)
    (upperStarComp (ModuleCat.{u + 1} B) j' g) p p'
    (finitePull_compSquare B a j) (finitePull_compSquare B j' g)
    (moduleSquareG B a j' j g w) (upperStarCompIso (ModuleCat.{u + 1} B) w)
    (moduleSquareG_eq B a j' j g w) hw
  exact finiteSquareComponents
    (C B X B (RingHom.id B)) (C B U B (RingHom.id B))
    (C B X' B (RingHom.id B)) (C B U' B (RingHom.id B))
    (upperStar (ModuleCat.{u + 1} B) j) (upperStar (ModuleCat.{u + 1} B) g)
    (upperStar (ModuleCat.{u + 1} B) a) (upperStar (ModuleCat.{u + 1} B) j')
    (modulePullback B j) (modulePullback B g) (modulePullback B a) (modulePullback B j')
    (openBetaFinitePull B j).hom (openBetaFinitePull B g).hom
    (openBetaFinitePull B a).hom (openBetaFinitePull B j').hom
    (moduleSquareG B a j' j g w) (upperStarCompIso (ModuleCat.{u + 1} B) w) hs N


private lemma finiteMateCube
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category DY] [Category DX] [Category DY'] [Category DX']
    [Category EY] [Category EX] [Category EY'] [Category EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (sr : Gr ⋙ Lf' ≅ Lf ⋙ Hr) (bs : Mf ⋙ Hs ≅ Gs ⋙ Mf')
    (f : PY ⋙ Mf ≅ Lf ⋙ PX) (f' : PY' ⋙ Mf' ≅ Lf' ⋙ PX')
    (g : PY ⋙ Gs ≅ Gr ⋙ PY') (g' : PX ⋙ Hs ≅ Hr ⋙ PX')
    (r : PX ⋙ Sf ≅ Rf ⋙ PY) (r' : PX' ⋙ Sf' ≅ Rf' ⋙ PY')
    (tr : Rf ⋙ Gr ⟶ Hr ⋙ Rf') (ts : Sf ⋙ Gs ⟶ Hs ⋙ Sf')
    (hf : mateEquiv af bf f.hom = TwoSquare.mk _ _ _ _ r.inv)
    (hf' : mateEquiv af' bf' f'.hom = TwoSquare.mk _ _ _ _ r'.inv)
    (hsr : mateEquiv af af' sr.hom = TwoSquare.mk _ _ _ _ tr)
    (hbs : mateEquiv bf bf' bs.inv = TwoSquare.mk _ _ _ _ ts)
    (h : ∀ K, ts.app (PX.obj K) ≫ Sf'.map (g'.hom.app K) ≫
      r'.hom.app (Hr.obj K) = Gs.map (r.hom.app K) ≫
        g.hom.app (Rf.obj K) ≫ PY'.map (tr.app K)) (M : DY) :
    bs.hom.app (PY.obj M) ≫ Mf'.map (g.hom.app M) ≫ f'.hom.app (Gr.obj M) =
      Hs.map (f.hom.app M) ≫ g'.hom.app (Lf.obj M) ≫ PX'.map (sr.inv.app M) := by
  have ht (K : DX) : g.hom.app (Rf.obj K) ≫ PY'.map (tr.app K) ≫
      r'.inv.app (Hr.obj K) = Gs.map (r.inv.app K) ≫
        ts.app (PX.obj K) ≫ Sf'.map (g'.hom.app K) := by
    apply (cancel_epi (Gs.map (r.hom.app K))).1
    simp only [← Gs.map_comp_assoc, Iso.hom_inv_id_app,
      Gs.map_id, Category.id_comp]
    apply (cancel_mono (r'.hom.app (Hr.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hh := (h K).symm
    dsimp only [Functor.comp_obj, Functor.comp_map] at hh ⊢
    simpa only [Category.comp_id] using hh
  have hc := mateEquiv_app_cube_converse af af' bf bf' sr.hom bs.inv
    f.hom f'.hom g.hom g'.hom (fun K ↦ by
      rw [hf, hf', hsr, hbs]
      exact ht K) M
  apply (cancel_epi (bs.inv.app (PY.obj M))).1
  apply (cancel_mono (PX'.map (sr.hom.app M))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← PX'.map_comp,
    Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.comp_map] at hc ⊢
  simpa only [PX'.map_id, Category.comp_id] using hc

private lemma finiteOpen_mate {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (moduleJAdj B j) (openBetaFiniteOpen B j).hom =
        TwoSquare.mk _ _ _ _ (openBetaFinitePull B j).inv := by
  unfold openBetaFiniteOpen openBetaFiniteOpenHom
  exact (mateEquiv _ _).apply_symm_apply _

private lemma finiteOpen_cube {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g)
    (M : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} B)) :
    (openBetaModule B a j' j g w sq).hom.app ((C B U B (RingHom.id B)).obj M) ≫
      (moduleJ B j').map ((openBetaFinitePull B a).hom.app M) ≫
      (openBetaFiniteOpen B j').hom.app ((upperStar (ModuleCat.{u + 1} B) a).obj M) =
    (modulePullback B g).map ((openBetaFiniteOpen B j).hom.app M) ≫
      (openBetaFinitePull B g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj M) ≫
      (C B X' B (RingHom.id B)).map
        ((openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} B) sq).inv.app M) := by
  exact finiteMateCube
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j')
    (moduleJAdj B j) (moduleJAdj B j')
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} B) sq)
    (openBetaModule B a j' j g w sq)
    (openBetaFiniteOpen B j) (openBetaFiniteOpen B j')
    (openBetaFinitePull B a) (openBetaFinitePull B g)
    (openBetaFinitePull B j) (openBetaFinitePull B j')
    (upperStarCompIso (ModuleCat.{u + 1} B) w).hom
    (moduleSquareG B a j' j g w).inv
    (finiteOpen_mate B j) (finiteOpen_mate B j')
    (by
      simpa only [openImmersionLowerShriekBaseChangeIso, asIso_hom] using!
        mateEquiv_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq)
    (by
      change mateEquiv (moduleJAdj B j) (moduleJAdj B j')
        (singleBetaInv B a j' j g w) = _
      exact moduleInv_mate B a j' j g w)
    (fun N ↦ finitePull_square B a j' j g w N) M

/-- Finite specialization agrees with the dependency's actual ordinary derived map,
under the canonical unit-preserving scalar-presentation comparisons.
Source: Stacks, Tags 09AE and 0GL1
(blueprint: lem-cbc-tower-open-beta-normalization).
Proof: the section-preserving direct-image comparisons commute with composition.
Mate pasting transfers this to the canonical pullback square. The ordinary open
base-change mate and the module open base-change mate are those square maps;
the converse mate-cube identity therefore compares the specified open extensions.
Exact-functor cube descent carries this identity to the unbounded derived category,
where the ordinary face is the recorded ordinaryOpenExtensionBaseChangeIso. -/
theorem openBetaFiniteCompatibility {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} B))) :
    (openBetaSingle B a j' j g w sq).hom.app
        ((C B U B (RingHom.id B)).mapDerivedCategory.obj M) ≫
      (moduleJ B j').mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (openBetaFinitePull B a)).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso (openBetaFiniteOpen B j')).hom.app
        ((upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory.obj M) =
    (modulePullback B g).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (openBetaFiniteOpen B j)).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso (openBetaFinitePull B g)).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M) ≫
      (C B X' B (RingHom.id B)).mapDerivedCategory.map
        ((ordinaryOpenExtensionBaseChangeIso B a j' j g sq).hom.app M) := by
  have hc := Functor.mapDerivedCategory_exactCube
    (C B U B (RingHom.id B)) (moduleJ B j) (modulePullback B g)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j)
    (C B X B (RingHom.id B)) (upperStar (ModuleCat.{u + 1} B) g)
    (C B X' B (RingHom.id B)) (upperStar (ModuleCat.{u + 1} B) a)
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j')
    (modulePullback B a) (moduleJ B j') (C B U' B (RingHom.id B))
    (openBetaFiniteOpen B j) (openBetaFinitePull B g)
    (openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} B) sq).symm
    (openBetaModule B a j' j g w sq)
    (openBetaFinitePull B a) (openBetaFiniteOpen B j')
    (fun N ↦ (finiteOpen_cube B a j' j g w sq N).symm)
  have hd := (NatTrans.congr_app hc M).symm
  have ho : openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} B) sq =
      (conjugateIsoEquiv
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).comp
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g))
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) a).comp
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j'))).symm
        (@asIso _ _ _ _ (baseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq)
          (isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} B) sq)) := by
    apply Iso.ext
    rfl
  rw [ho] at hd
  exact hd


end FiniteComparisonProof

end Finite

end AlgebraicGeometry.ProEtale.StrictTower

attribute [instance] CategoryTheory.catToReflQuiver
