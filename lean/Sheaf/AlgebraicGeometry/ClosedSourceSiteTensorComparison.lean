/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization
public import Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor
public import Sheaf.Paper.SupportedCup
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import all Sheaf.Paper.SupportedCup
import all Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization
import all Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor
import all Sheaf.AlgebraicGeometry.SupportSiteComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate

/-!
# Sectionwise and multiplicative normalization of closed-source site exchange

Source: Stacks Project, Tags 0GLZ, 099V, 099W, 03EL and 07A4; the closed-source
refinement in supported cup functoriality, Steps 2 and 6
(blueprint: lem-pur-closed-source-site-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c d
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ClosedSourceSiteTensor
open SupportedConstantNormalization

/-- Transport the cup construction's coefficient to the recorded constant sheaf.
Source: Stacks 099W, degree zero; def-pur-supported-cup, cupConstantIso
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def cupSupportIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C) ≅
      supported P.Coefficient true i :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).mapIso
    (ProEtale.cupConstantIso P C)

/-- Precisely the pro-etale cup multiplication, transported by cupConstantIso.
Source: def-pur-supported-cup, restriction and multiplication on the intersection
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def multiplication (P : WeilConjectures.PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    supported P.Coefficient true i ⊗ supported P.Coefficient true j ⟶
      supported P.Coefficient true (Etale.intersectionSupport i j) :=
  (tensorIso (cupSupportIso P i).symm (cupSupportIso P j).symm).hom ≫
    ProEtale.cupCoefficientMap P i j ≫ (cupSupportIso P (Etale.intersectionSupport i j)).hom

/-- The actual pullback square in the normalization theorem, with canonical projections.
Source: Stacks 03S6, scheme fibre products
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def baseSquare {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) :
    ChosenCartesianSquare (pullback.snd v i) (pullback.fst v i) i v where
  w := pullback.condition.symm
  isoPullback := pullbackSymmetry v i
  hom_fst := pullbackSymmetry_hom_comp_fst v i
  hom_snd := pullbackSymmetry_hom_comp_snd v i

/-- The prescribed pro-etale exchange, without a new choice of isomorphism.
Source: Stacks 03S6; lem-pur-supported-constant-exchange-normalization
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def baseExchange (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) :=
  exchange A true (baseSquare i v)

/-- The comparison adjunction unit on terminal sections, with native section types.
Source: Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def terminalComparisonUnitIso (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology D) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≅
      ((ProEtale.comparisonUpperStar D X).obj F).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X))) := by
  letI := ProEtale.isIso_comparisonAdjunction_unit D X
  exact asIso (((ProEtale.comparisonAdjunction D X).unit.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 X))))

private lemma terminalComparisonUnitIso_hom (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology D) :
    (terminalComparisonUnitIso D X F).hom =
      ((ProEtale.comparisonAdjunction D X).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) := by
  rfl

private lemma terminalComparisonUnitIso_naturality (D : Type*) [Category.{u + 1} D]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D] (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology D} (f : F ⟶ G) :
    (terminalComparisonUnitIso D X F).hom ≫
        ((ProEtale.comparisonUpperStar D X).map f).hom.app
          (op (Scheme.ProEt.mk (𝟙 X))) =
      f.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
        (terminalComparisonUnitIso D X G).hom := by
  rw [terminalComparisonUnitIso_hom, terminalComparisonUnitIso_hom]
  have h := congrArg (fun a ↦ a.hom.app (op (Scheme.Etale.mk (𝟙 X))))
    ((ProEtale.comparisonAdjunction D X).unit.naturality f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.id_map, Functor.comp_map, ProEtale.comparisonLowerStar,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.comp_obj, Functor.id_obj] at h
  convert h.symm using 1 <;> rfl


/-- Terminal evaluation of comparison pullback along an arbitrary scheme map.
Source: Stacks 099R and 0GLZ, the specified coherent comparison.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def genericComparisonSectionIso (A : Type (u + 1)) [CommRing A]
    {X' X : Scheme.{u}} (h : X' ⟶ X) (F : Modules A false X) :
    ((compare A X').obj ((pull A false h).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X'))) ≅
      ((pull A true h).obj ((compare A X).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X'))) :=
  (((sheafToPresheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} A)).mapIso
    ((comparePullback A h).app F)).app (op (Scheme.ProEt.mk (𝟙 X'))))

private lemma genericComparisonSectionIso_hom (A : Type (u + 1)) [CommRing A]
    {X' X : Scheme.{u}} (h : X' ⟶ X) (F : Modules A false X) :
    (genericComparisonSectionIso A h F).hom =
      ((comparePullback A h).hom.app F).hom.app
        (op (Scheme.ProEt.mk (𝟙 X'))) := by
  rfl

/-- Evaluate the prescribed comparison-pullback iso using native section types.
Source: Stacks 099R and 0GLZ; the coherent comparison-pullback construction.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def comparisonSectionPullbackIso (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (F : Modules A false X) (Y : X.ProEt) :
    ((compare A Y.left).obj ((pull A false (X := Y.left) Y.hom).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 Y.left))) ≅
      ((pull A true (X := Y.left) Y.hom).obj ((compare A X).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 Y.left))) :=
  genericComparisonSectionIso A (X' := Y.left) Y.hom F

/-- The canonical comparison section formula. Restrict along a weakly etale object,
commute site comparison with pullback, and invert the comparison unit on terminal sections.
This is the module-valued realization of Tag 0GLZ, normalized by the adjunction unit.
Source: Stacks 0GLZ and 099W, degree zero
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def comparisonSections (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (F : Modules A false X) (Y : X.ProEt) :
    ((compare A X).obj F).obj.obj (op Y) ≅
      ((pull A false (X := Y.left) Y.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) :=
  (((compare A X).obj F).obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl Y.left)
      (Category.id_comp Y.hom) :
        (MorphismProperty.Over.map ⊤ Y.prop).obj (Scheme.ProEt.mk (𝟙 Y.left)) ≅ Y).op) ≪≫
    (asIso (((ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) Y.hom Y.prop).inv.app ((compare A X).obj F)).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y.left))))) ≪≫
    (comparisonSectionPullbackIso A F Y).symm ≪≫
    (terminalComparisonUnitIso (ModuleCat.{u + 1} A) Y.left
      ((pull A false (X := Y.left) Y.hom).obj F)).symm

/-- The prescribed etale exchange with the common supported-constant interface.
Source: Stacks 03S6; the existing etale closed constant pullback adjoint.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def etaleExchangeNative (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    (pull A false v).obj (supported A false i) ⟶
      supported A false (pullback.fst v i) :=
  Etale.closedConstantPullbackAdjoint A i v

/-- The specified etale closed exchange followed by terminal direct-image evaluation.
Source: lem-pur-etale-closed-constant-tensor; Stacks 03S6
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def etaleSupportSections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    ((pull A false (X := Y.left) Y.hom).obj (supported A false i)).obj.obj
        (op (Scheme.Etale.mk (𝟙 Y.left))) ⟶
      (constant A false (pullback Y.hom i)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback Y.hom i)))) :=
  (etaleExchangeNative A (X' := Y.left) i Y.hom).hom.app
      (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
    (constant A false (pullback Y.hom i)).obj.map
      (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y.left) (pullback.fst Y.hom i)))
        (Category.comp_id _) :
        (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst Y.hom i)).obj
          (Scheme.Etale.mk (𝟙 Y.left)) ≅
            Scheme.Etale.mk (𝟙 (pullback Y.hom i))).inv.op

/-- Degree-zero canonical comparison on constant sections, followed by the constant unit.
Source: Stacks 099W (1), i=0; lem-cbc-abelian-etale-proetale-cohomology-comparison
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def constantComparisonSections (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (constant A false T).obj.obj (op (Scheme.Etale.mk (𝟙 T))) ⟶
      (constant A true T).obj.obj (op (Scheme.ProEt.mk (𝟙 T))) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
    (constant A false T)).hom.app (op (Scheme.Etale.mk (𝟙 T))) ≫
      (compareUnit A T).hom.hom.app (op (Scheme.ProEt.mk (𝟙 T)))

/-- Terminal evaluation for a direct image on the pro-etale site.
Source: the pullback of the identity isomorphism; Stacks 099W.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def genericTerminal (D : Type*) [Category.{u + 1} D]
    {C X : Scheme.{u}} (i : C ⟶ X) (F : Sheaf (Scheme.ProEt.topology C) D) :
    ((ProEtale.lowerStar D i).obj F).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) ≅
      F.obj.obj (op (Scheme.ProEt.mk (𝟙 C))) :=
  F.obj.mapIso
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) i)) (Category.comp_id _) :
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
        (Scheme.ProEt.mk (𝟙 X)) ≅ Scheme.ProEt.mk (𝟙 C)).symm.op

/-- Evaluate inverse image along a pro-etale test by localization restriction.
Source: Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def genericLocalization (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {X : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology X) D) (Y : X.ProEt) :
    F.obj.obj (op Y) ≅
      ((ProEtale.upperStar D (Z := Y.left) Y.hom).obj F).obj.obj
        (op (Scheme.ProEt.mk (𝟙 Y.left))) :=
  F.obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl Y.left) (Category.id_comp Y.hom) :
      (MorphismProperty.Over.map ⊤ Y.prop).obj (Scheme.ProEt.mk (𝟙 Y.left)) ≅ Y).op ≪≫
    asIso (((ProEtale.upperStarIsoLocalizationRestriction
      D Y.hom Y.prop).inv.app F).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y.left))))

/-- The canonical weakly etale base-change isomorphism before evaluation.
Source: Stacks 099W, weakly etale localization base change.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def sectionBaseChangeIso (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {C X : Scheme.{u}} (i : C ⟶ X)
    (Y : X.ProEt) :
    ProEtale.lowerStar D i ⋙ ProEtale.upperStar D (Z := Y.left) Y.hom ≅
      ProEtale.upperStar D (pullback.snd Y.hom i) ⋙
        ProEtale.lowerStar D (pullback.fst Y.hom i) := by
  letI := ProEtale.isIso_baseChangeMap_of_isPullback D
    (IsPullback.of_hasPullback (Z := X) Y.hom i)
  exact asIso (ProEtale.baseChangeMap D
    (IsPullback.of_hasPullback (Z := X) Y.hom i).toCommSq)

/-- The base-change isomorphism has the prescribed mate as its forward map.
Source: the definition of the weakly etale base-change isomorphism.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
lemma sectionBaseChangeIso_hom (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {C X : Scheme.{u}} (i : C ⟶ X)
    (Y : X.ProEt) :
    (sectionBaseChangeIso D i Y).hom =
      ProEtale.baseChangeMap D (IsPullback.of_hasPullback Y.hom i).toCommSq := by
  rfl

/-- Evaluate a sheaf isomorphism between two specified section identifications.
Source: functoriality of evaluation; Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def evaluatedSectionIso
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ≅ F.obj.obj W) (r : G.obj.obj W ≅ C)
    (f : F ≅ G) : B ≅ C :=
  l ≪≫ ((sheafSections J D).obj W).mapIso f ≪≫ r

/-- Forward evaluation of a sheaf isomorphism is componentwise composition.
Source: functoriality of evaluation; Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
lemma evaluatedSectionIso_hom
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ≅ F.obj.obj W) (r : G.obj.obj W ≅ C)
    (f : F ≅ G) :
    (evaluatedSectionIso l r f).hom = l.hom ≫ f.hom.hom.app W ≫ r.hom := by
  rfl

/-- Canonical section evaluation used in closed-source base change.
Source: Stacks 099W, degree zero and localization.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def terminalSupport (A : Type (u + 1)) [CommRing A]
    (pro : Bool) {C X : Scheme.{u}} (i : C ⟶ X) :
    (supported A pro i).obj.obj (op (match pro with
      | false => Scheme.Etale.mk (𝟙 X)
      | true => Scheme.ProEt.mk (𝟙 X))) ≅
    (constant A pro C).obj.obj (op (match pro with
      | false => Scheme.Etale.mk (𝟙 C)
      | true => Scheme.ProEt.mk (𝟙 C))) := by
  cases pro with
  | false =>
    exact (constant A false C).obj.mapIso
      (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) i))
        (Category.comp_id _) :
        (MorphismProperty.Over.pullback @Etale ⊤ i).obj
          (Scheme.Etale.mk (𝟙 X)) ≅ Scheme.Etale.mk (𝟙 C)).symm.op
  | true => exact genericTerminal (ModuleCat.{u + 1} A) i (constant A true C)

/-- Canonical section evaluation used in closed-source base change.
Source: Stacks 099W, degree zero and localization.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def localizationSections (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} (F : Modules A true X) (Y : X.ProEt) :
    F.obj.obj (op Y) ≅
      ((pull A true (X := Y.left) Y.hom).obj F).obj.obj (op (Scheme.ProEt.mk (𝟙 Y.left))) :=
  genericLocalization (ModuleCat.{u + 1} A) F Y

/-- Canonical section evaluation used in closed-source base change.
Source: Stacks 099W, degree zero and localization.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def sectionComposite
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ⟶ F.obj.obj W) (r : G.obj.obj W ⟶ C)
    (f : F ⟶ G) : B ⟶ C := l ≫ f.hom.app W ≫ r

/-- The weakly etale exchange with constant coefficients as an isomorphism.
Source: Stacks 099W and canonical constant inverse image.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def constantSectionExchangeIso (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (pull A true (X := Y.left) Y.hom).obj (supported A true i) ≅
      supported A true (pullback.fst Y.hom i) :=
  (sectionBaseChangeIso (ModuleCat.{u + 1} A) i Y).app (constant A true C) ≪≫
    (push A true (pullback.fst Y.hom i)).mapIso
      (unitIso A true (pullback.snd Y.hom i))

/-- Evaluate a pro-etale constant direct image on a weakly etale test by restriction
of constants to its scheme fibre product. All identifications preserve constant scalars.
Source: Stacks 099W and the constant inverse-image identification
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def proSupportSections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (supported A true i).obj.obj (op Y) ≅
      (constant A true (pullback Y.hom i)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (pullback Y.hom i)))) :=
  evaluatedSectionIso
    (localizationSections A (supported A true i) Y)
    (terminalSupport A true (X := Y.left) (pullback.fst Y.hom i))
    (constantSectionExchangeIso A i Y)

/-- The canonical support-change map, induced by adjunction and constant restriction.
Source: Stacks 03S6 and 03EL; intersection base-change identification
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def supportChange (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    (g : D ⟶ C) (h : g ≫ i = j) :
    supported A true i ⟶ supported A true j :=
  (push A true i).map ((adj A true g).unit.app (constant A true C) ≫
    (push A true g).map (unitIso A true g).hom) ≫
      (ProEtale.lowerStarComp (ModuleCat.{u + 1} A) g i).hom.app (constant A true D) ≫
        (ProEtale.lowerStarCongr (ModuleCat.{u + 1} A) h).hom.app (constant A true D)

/-- The universal scheme map identifying the two pullback intersections.
Source: Stacks 03EL, fibre-product associativity
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def intersectionChange {C D X X' : Scheme.{u}}
    (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X) :
    pullback (pullback.fst v i) (pullback.fst v j) ⟶
      pullback v (Etale.intersectionSupport i j) :=
  pullback.lift
    (pullback.fst (pullback.fst v i) (pullback.fst v j) ≫ pullback.fst v i)
    (pullback.lift
      (pullback.fst (pullback.fst v i) (pullback.fst v j) ≫ pullback.snd v i)
      (pullback.snd (pullback.fst v i) (pullback.fst v j) ≫ pullback.snd v j)
      (by simp only [Category.assoc, ← pullback.condition];
          rw [← Category.assoc, pullback.condition, Category.assoc]))
    (by simp only [Etale.intersectionSupport, Category.assoc, pullback.lift_fst_assoc]
        rw [pullback.condition])

/-- Support transport from v-inverse-image of the intersection to the intersection
of the two inverse images, with the canonical universal lift.
Source: Stacks 03EL, fibre products
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def baseSupportChange (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X) :
    supported A true (pullback.fst v (Etale.intersectionSupport i j)) ⟶
      supported A true (Etale.intersectionSupport (pullback.fst v i) (pullback.fst v j)) :=
  supportChange A _ _ (intersectionChange i j v)
    (by simp [intersectionChange, Etale.intersectionSupport])

/-- Finiteness of the recorded coefficient quotient, with its existing proof.
Source: Serre, Local Fields II, section 2; def-pur-conventions
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
instance finiteRing (P : WeilConjectures.PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The coefficient universe lift preserves finiteness.
Source: def-pur-conventions, finite coefficient convention
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
instance finiteCoefficient (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The derived multiplication square on the actual degree-zero models. Its vertical
arrows are the canonical single/left-derived identification followed by the specified
ordinary exchange. Its tensor comparison is the uniquely characterized derived
comparison, computed on K-flat representatives, rather than an arbitrary isomorphism.
Source: Stacks 07A4 and 0G7E; lem-weil-pbc-ringed-topoi-derived-tensor-pullback
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def DerivedSquare
    {B : Type c} [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {E : Type d} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E] [MonoidalClosed E]
    [Abelian.HasFunctorialFlatResolution E]
    (L : B ⥤ E) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.Monoidal] [L.PreservesFlat] [L.IsLeftAdjoint]
    {M N K : B} {M' N' K' : E} (μ : M ⊗ N ⟶ K) (μ' : M' ⊗ N' ⟶ K')
    (qM : L.obj M ⟶ M') (qN : L.obj N ⟶ N') (qK : L.obj K ⟶ K') : Prop :=
  L.leftDerivedFunctor.map (ProEtale.cupDerivedCoefficientMap μ) ≫
      L.singleFunctorCompLeftDerivedFunctorIso.hom.app K ≫
      (DerivedCategory.singleFunctor E 0).map qK =
    ((L.leftDerivedTensorComparison.app
      ((DerivedCategory.singleFunctor B 0).obj M)).app
        ((DerivedCategory.singleFunctor B 0).obj N)) ≫
      tensorHom
        (L.singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
          (DerivedCategory.singleFunctor E 0).map qM)
        (L.singleFunctorCompLeftDerivedFunctorIso.hom.app N ≫
          (DerivedCategory.singleFunctor E 0).map qN) ≫
      ProEtale.cupDerivedCoefficientMap μ'

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private lemma pro_restriction_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    restriction A true i = Functor.LaxMonoidal.ε (ProEtale.lowerStar
      (ModuleCat.{u + 1} A) i) := by
  change Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A) = _
  apply ((sheafificationAdjunction (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  unfold Scheme.proEtaleConstantDirectImageMap
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i)
    (ModuleCat.{u + 1} A) (Scheme.ProEt.topology X) (Scheme.ProEt.topology C) W).symm

private lemma pro_constant_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    (unitIso A true i).hom = Functor.OplaxMonoidal.η
      (ProEtale.upperStar (ModuleCat.{u + 1} A) i) := by
  apply ((adj A true i).homEquiv _ _).injective
  simp only [unitIso, Iso.app_hom,
    ProEtale.CachedConstantCoherence.proConstant_eq_inverse]
  unfold Scheme.constantInverse
  change ((adj A true i).homEquiv _ _)
      (((adj A true i).homEquiv _ _).symm (restriction A true i)) = _
  rw [Equiv.apply_symm_apply, pro_restriction_unit, Adjunction.homEquiv_apply]
  exact (Adjunction.unit_app_unit_comp_map_η _).symm

private lemma multiplication_unit (P : WeilConjectures.PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    tensorHom (restriction P.Coefficient true i) (restriction P.Coefficient true j) ≫
        multiplication P i j =
      (λ_ (constant P.Coefficient true X)).hom ≫
        restriction P.Coefficient true (Etale.intersectionSupport i j) := by
  have h : tensorHom (ProEtale.cupCoefficientRestriction P i)
      (ProEtale.cupCoefficientRestriction P j) ≫ ProEtale.cupCoefficientMap P i j =
      ProEtale.cupCoefficientMultiplication P X ≫
        ProEtale.cupCoefficientRestriction P (Etale.intersectionSupport i j) :=
    (ProEtale.cupCoefficientMap_existsUnique P i j).exists.choose_spec
  rw [ProEtale.cupRestriction_eq_laxUnit, ProEtale.cupRestriction_eq_laxUnit,
    ProEtale.cupRestriction_eq_laxUnit] at h
  rw [pro_restriction_unit, pro_restriction_unit, pro_restriction_unit]
  apply (cancel_epi (tensorHom (ProEtale.cupConstantIso P X).hom
    (ProEtale.cupConstantIso P X).hom)).mp
  dsimp only [multiplication, cupSupportIso, tensorIso_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv]
  dsimp only [ProEtale.cupCoefficientMultiplication, tensorIso_hom] at h
  have h' := congrArg (fun f ↦ f ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (Etale.intersectionSupport i j)).map
        (ProEtale.cupConstantIso P (pullback i j)).hom) h
  simp only [← tensorHom_comp_tensorHom, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id] at h' ⊢
  have hi : (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (Etale.intersectionSupport i j)).map
      (𝟙 (𝟙_ (Sheaf (Scheme.ProEt.topology (pullback i j))
        (ModuleCat.{u + 1} P.Coefficient)))) = 𝟙 _ :=
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (Etale.intersectionSupport i j)).map_id _
  rw [hi, Category.comp_id] at h'
  exact h'


private lemma normalized_product
    {B E : Type*} [Category B] [Category E]
    [MonoidalCategory B] [MonoidalCategory E]
    (F : B ⥤ E) [F.Monoidal]
    {M N K : B} {M' N' K' : E}
    (rM : 𝟙_ B ⟶ M) (rN : 𝟙_ B ⟶ N) (rK : 𝟙_ B ⟶ K)
    (rM' : 𝟙_ E ⟶ M') (rN' : 𝟙_ E ⟶ N') (rK' : 𝟙_ E ⟶ K')
    (μ : M ⊗ N ⟶ K) (μ' : M' ⊗ N' ⟶ K')
    (qM : F.obj M ⟶ M') (qN : F.obj N ⟶ N') (qK : F.obj K ⟶ K')
    [Epi (F.map (tensorHom rM rN))]
    (hm : tensorHom rM rN ≫ μ = (λ_ (𝟙_ B)).hom ≫ rK)
    (hm' : tensorHom rM' rN' ≫ μ' = (λ_ (𝟙_ E)).hom ≫ rK')
    (hM : F.map rM ≫ qM = Functor.OplaxMonoidal.η F ≫ rM')
    (hN : F.map rN ≫ qN = Functor.OplaxMonoidal.η F ≫ rN')
    (hK : F.map rK ≫ qK = Functor.OplaxMonoidal.η F ≫ rK') :
    F.map μ ≫ qK = Functor.OplaxMonoidal.δ F M N ≫ tensorHom qM qN ≫ μ' := by
  apply (cancel_epi (F.map (tensorHom rM rN))).mp
  rw [← F.map_comp_assoc, hm, F.map_comp, Category.assoc, hK]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom_assoc, hM, hN,
    ← tensorHom_comp_tensorHom_assoc, hm']
  have h := congrArg (fun f ↦ Functor.OplaxMonoidal.δ F (𝟙_ B) (𝟙_ B) ≫ f ≫
      Functor.OplaxMonoidal.η F ≫ rK') (ProEtale.comparison_multiplication F)
  simpa only [Category.assoc, Functor.Monoidal.δ_μ_assoc,
    IsIso.inv_hom_id_assoc, Category.id_comp] using h.symm

private lemma restriction_epi (P : WeilConjectures.PurityFiniteSetting.{u})
    (pro : Bool) {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    Epi (restriction P.Coefficient pro i) := by
  obtain ⟨w, ⟨h⟩⟩ := presentation P pro i
  exact epi_of_isColimit_cofork h

private lemma restriction_tensor_epi (P : WeilConjectures.PurityFiniteSetting.{u})
    (pro : Bool) {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    Epi (tensorHom (restriction P.Coefficient pro i) (restriction P.Coefficient pro j)) := by
  cases pro with
  | false =>
    have := restriction_epi P false i
    have := restriction_epi P false j
    let : Epi (restriction P.Coefficient false i ▷
        constant P.Coefficient false X) :=
      (tensorRight (constant P.Coefficient false X)).map_epi _
    let : Epi (supported P.Coefficient false i ◁
        restriction P.Coefficient false j) :=
      (tensorLeft (supported P.Coefficient false i)).map_epi _
    rw [MonoidalCategory.tensorHom_def]
    exact epi_comp _ _
  | true =>
    have := restriction_epi P true i
    have := restriction_epi P true j
    let : Epi (restriction P.Coefficient true i ▷
        constant P.Coefficient true X) :=
      (tensorRight (constant P.Coefficient true X)).map_epi _
    let : Epi (supported P.Coefficient true i ◁
        restriction P.Coefficient true j) :=
      (tensorLeft (supported P.Coefficient true i)).map_epi _
    rw [MonoidalCategory.tensorHom_def]
    exact epi_comp _ _

private lemma etale_restriction_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    restriction A false i = Functor.LaxMonoidal.ε
      (Etale.lowerStar (ModuleCat.{u + 1} A) i) := by
  change ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app
      (ModuleCat.of A A)) = _
  erw [Etale.upperStarConstantSheafIso_hom_app_tensorUnit]
  rw [Adjunction.homEquiv_apply]
  exact (Adjunction.unit_app_unit_comp_map_η
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i))

private lemma comparison_product (P : WeilConjectures.PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (compare P.Coefficient X).map (Etale.closedConstantTensorMap P.Coefficient i j) ≫
        gamma P.Coefficient (Etale.intersectionSupport i j) =
      Functor.OplaxMonoidal.δ (compare P.Coefficient X) _ _ ≫
        tensorHom (gamma P.Coefficient i) (gamma P.Coefficient j) ≫ multiplication P i j := by
  have := restriction_tensor_epi P false i j
  have := (compare P.Coefficient X).map_epi
    (tensorHom (restriction P.Coefficient false i) (restriction P.Coefficient false j))
  apply normalized_product (compare P.Coefficient X)
    (restriction P.Coefficient false i) (restriction P.Coefficient false j)
    (restriction P.Coefficient false (Etale.intersectionSupport i j))
    (restriction P.Coefficient true i) (restriction P.Coefficient true j)
    (restriction P.Coefficient true (Etale.intersectionSupport i j))
    (Etale.closedConstantTensorMap P.Coefficient i j) (multiplication P i j)
    (gamma P.Coefficient i) (gamma P.Coefficient j)
    (gamma P.Coefficient (Etale.intersectionSupport i j))
  · simp only [etale_restriction_unit]
    exact ProEtale.etale_normalization P i j
  · exact multiplication_unit P i j
  · exact (site_normalization P i).2.2.2.2.2.1
  · exact (site_normalization P j).2.2.2.2.2.1
  · exact (site_normalization P (Etale.intersectionSupport i j)).2.2.2.2.2.1

private lemma supportChange_restriction (P : WeilConjectures.PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    (g : D ⟶ C) (h : g ≫ i = j) :
    restriction P.Coefficient true i ≫ supportChange P.Coefficient i j g h =
      restriction P.Coefficient true j := by
  subst j
  simp only [supportChange, pro_constant_unit, pro_restriction_unit,
    ProEtale.lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  erw [(ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) g).unit_app_unit_comp_map_η]
  exact (ProEtale.cupLaxUnit_comp P g i).symm

private lemma baseExchange_restriction (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X X' : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (v : X' ⟶ X) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).map
        (restriction P.Coefficient true i) ≫
        baseExchange P.Coefficient i v =
      Functor.OplaxMonoidal.η (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v) ≫
        restriction P.Coefficient true (pullback.fst v i) := by
  rw [← pro_constant_unit]
  exact (scheme_normalization P true (baseSquare i v)).2.2.2.2.1

private lemma pullback_product (P : WeilConjectures.PurityFiniteSetting.{u})
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : X' ⟶ X) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).map (multiplication P i j) ≫
        baseExchange P.Coefficient (Etale.intersectionSupport i j) v ≫
        baseSupportChange P.Coefficient i j v =
      Functor.OplaxMonoidal.δ (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v) _ _ ≫
        tensorHom (baseExchange P.Coefficient i v) (baseExchange P.Coefficient j v) ≫
          multiplication P (pullback.fst v i) (pullback.fst v j) := by
  have := restriction_tensor_epi P true i j
  have := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).map_epi
    (tensorHom (restriction P.Coefficient true i) (restriction P.Coefficient true j))
  apply normalized_product (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v)
    (restriction P.Coefficient true i) (restriction P.Coefficient true j)
    (restriction P.Coefficient true (Etale.intersectionSupport i j))
    (restriction P.Coefficient true (pullback.fst v i))
    (restriction P.Coefficient true (pullback.fst v j))
    (restriction P.Coefficient true
      (Etale.intersectionSupport (pullback.fst v i) (pullback.fst v j)))
    (multiplication P i j) (multiplication P (pullback.fst v i) (pullback.fst v j))
    (baseExchange P.Coefficient i v) (baseExchange P.Coefficient j v)
    (baseExchange P.Coefficient (Etale.intersectionSupport i j) v ≫
      baseSupportChange P.Coefficient i j v)
  · exact multiplication_unit P i j
  · exact multiplication_unit P _ _
  · exact baseExchange_restriction P i v
  · exact baseExchange_restriction P j v
  · rw [← Category.assoc, baseExchange_restriction, Category.assoc]
    exact congrArg
      (fun f ↦ Functor.OplaxMonoidal.η
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v) ≫ f)
      (supportChange_restriction P _ _ _ _)

private lemma monoidal_unit_square
    {B E D H : Type*} [Category B] [Category E] [Category D] [Category H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory D] [MonoidalCategory H]
    (F : B ⥤ E) (G : D ⥤ H) (R : D ⥤ B) (S : H ⥤ E)
    [F.Monoidal] [G.Monoidal] [R.LaxMonoidal] [S.LaxMonoidal]
    (β : R ⋙ F ⟶ G ⋙ S) [NatTrans.IsMonoidal β] :
    F.map (Functor.LaxMonoidal.ε R) ≫ β.app (𝟙_ D) ≫
        S.map (Functor.OplaxMonoidal.η G) =
      Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε S := by
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
  have hu := NatTrans.IsMonoidal.unit (τ := β)
  simp only [Functor.LaxMonoidal.comp_ε, Category.assoc] at hu
  rw [reassoc_of% hu]
  simp only [← CategoryTheory.Functor.map_comp, Functor.Monoidal.ε_η,
    CategoryTheory.Functor.map_id, Category.comp_id, Functor.Monoidal.ε_η_assoc]

private lemma gamma_standard (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    gamma P.Coefficient i =
      (ProEtale.lowerStarComparisonUpperStarBaseChange i
        (ModuleCat.{u + 1} P.Coefficient)).app (constant P.Coefficient false C) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
        (compareUnit P.Coefficient C).hom := by
  symm
  apply (site_normalization P i).2.2.2.2.2.2
  have := ProEtale.comparison_monoidal P i
  rw [etale_restriction_unit, pro_restriction_unit]
  change (compare P.Coefficient X).map
      (Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)) ≫
      (ProEtale.lowerStarComparisonUpperStarBaseChange i
        (ModuleCat.{u + 1} P.Coefficient)).app (𝟙_ _) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
        (Functor.OplaxMonoidal.η (compare P.Coefficient C)) =
    Functor.OplaxMonoidal.η (compare P.Coefficient X) ≫
      Functor.LaxMonoidal.ε (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)
  exact monoidal_unit_square _ _ _ _ _

private lemma gamma_terminal (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X).unit.app
      (supported P.Coefficient false i)).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
      (gamma P.Coefficient i).hom.app (op (Scheme.ProEt.mk (𝟙 X))) ≫
      (terminalSupport P.Coefficient true i).hom =
    (terminalSupport P.Coefficient false i).hom ≫
      constantComparisonSections P.Coefficient C := by
  rw [gamma_standard]
  have h := ProEtale.unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app
    (ModuleCat.{u + 1} P.Coefficient) i (constant P.Coefficient false C)
  have hh := congrArg (fun f ↦ f.hom.app (op (Scheme.Etale.mk (𝟙 X)))) h
  dsimp at hh
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  erw [← Category.assoc, hh]
  let t : (MorphismProperty.Over.pullback @Etale ⊤ i).obj
      (Scheme.Etale.mk (𝟙 X)) ≅ Scheme.Etale.mk (𝟙 C) :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) i)) (Category.comp_id _)
  have hn := (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) C).unit.app
      (constant P.Coefficient false C) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) C).map
        (compareUnit P.Coefficient C).hom).hom).naturality t.inv.op
  change _ = _ at hn
  have hb : (((ProEtale.lowerStarCompComparisonLowerStarIso i
      (ModuleCat.{u + 1} P.Coefficient)).inv.app
        ((compare P.Coefficient C).obj (constant P.Coefficient false C))).hom.app
          (op (Scheme.Etale.mk (𝟙 X)))) = 𝟙 _ := by
    simp only [ProEtale.lowerStarCompComparisonLowerStarIso,
      ProEtale.toProEtCompOverPullbackIso, Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, Functor.sheafPushforwardContinuousComp,
      Iso.trans_inv, Iso.symm_inv,
      Iso.refl_inv, Iso.refl_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      NatTrans.op_app, NatIso.ofComponents_hom_app,
      Functor.comp_obj,
      ObjectProperty.FullSubcategory.comp_hom]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  erw [hb, Category.comp_id]
  change _ = _ at hn
  dsimp only [terminalSupport, genericTerminal, constantComparisonSections, Iso.symm_hom,
    Functor.mapIso_hom, Iso.op_hom]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Category.assoc, ProEtale.comparisonLowerStar,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.comp_obj,
    Functor.id_obj] at hn
  rw [Etale.lowerStar_map_hom_app, ProEtale.lowerStar_map_hom_app]
  convert hn.symm using 1 <;> rfl

private lemma square_standard (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) :
    ProEtale.supportSiteProEtaleComparisonSquare D (baseSquare i v) =
      ProEtale.upperStarCompIso D (IsPullback.of_hasPullback v i).toCommSq.w := by
  rfl

private lemma transpose_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : r ⊣ s) (a' : r' ⊣ s') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) (B : s ⋙ L ⟶ Q ⋙ s')
    (hB : B = (mateEquiv a a' t.hom).natTrans) (d : D) {d' : D'}
    (q : Q.obj d ⟶ d') :
    closedTranspose a a' L Q t d q = B.app d ≫ s'.map q := by
  symm
  apply normalized_closed_exchange a a' L Q t B d q
  subst B
  exact mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ t.hom) d

private noncomputable def standardExchange (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (pull A true (X := Y.left) Y.hom).obj (supported A true i) ⟶
      supported A true (pullback.fst Y.hom i) :=
  (constantSectionExchangeIso A i Y).hom

private lemma pro_exchange_basechange (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) [IsClosedImmersion i] :
    baseExchange A (X' := Y.left) i Y.hom = standardExchange A i Y := by
  unfold standardExchange
  rw [constantSectionExchangeIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    sectionBaseChangeIso_hom]
  unfold baseExchange exchange
  apply transpose_mate
  rw [square, square_standard]
  exact ProEtale.baseChangeMap_eq_mateEquiv
    (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback Y.hom i).toCommSq

private lemma localizationSections_naturality (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {F G : Modules A true X} (f : F ⟶ G) (Y : X.ProEt) :
    f.hom.app (op Y) ≫ (localizationSections A G Y).hom =
      (localizationSections A F Y).hom ≫
        ((pull A true (X := Y.left) Y.hom).map f).hom.app (op (Scheme.ProEt.mk (𝟙 Y.left))) := by
  dsimp only [localizationSections, genericLocalization, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom]
  erw [← Category.assoc, ← f.hom.naturality, Category.assoc]
  have hn := congrArg (fun t ↦ t.hom.app (op (Scheme.ProEt.mk (𝟙 Y.left))))
    ((ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) Y.hom Y.prop).inv.naturality f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hn
  erw [hn]
  simp only [Category.assoc]

private lemma pro_sections_standard (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (proSupportSections A i Y).hom =
      sectionComposite
        (localizationSections A (supported A true i) Y).hom
        (terminalSupport A true (X := Y.left) (pullback.fst Y.hom i)).hom
        (standardExchange A i Y) := by
  rw [proSupportSections, evaluatedSectionIso_hom]
  rfl

private lemma section_transport
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ⟶ F.obj.obj W) (r : G.obj.obj W ⟶ C)
    {f g : F ⟶ G} (hf : f = g) {q : B ⟶ C}
    (hq : q = sectionComposite l r g) :
    q = sectionComposite l r f := by
  exact hq.trans (congrArg (sectionComposite l r) hf.symm)

private lemma pro_sections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    (proSupportSections A i Y).hom =
      (localizationSections A (supported A true i) Y).hom ≫
        (baseExchange A (X' := Y.left) i Y.hom).hom.app (op (Scheme.ProEt.mk (𝟙 Y.left))) ≫
          (terminalSupport A true (X := Y.left) (pullback.fst Y.hom i)).hom := by
  exact section_transport _ _ (pro_exchange_basechange A i Y)
    (pro_sections_standard A i Y)

private lemma etale_exchange (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    exchange P.Coefficient false (baseSquare i v) =
      etaleExchangeNative P.Coefficient i v := by
  unfold etaleExchangeNative
  symm
  apply (scheme_normalization P false (baseSquare i v)).2.2.2.2.2
  rw [etale_restriction_unit P.Coefficient i,
    etale_restriction_unit P.Coefficient (pullback.fst v i)]
  erw [← Etale.section_unit P.Coefficient i,
    ← Etale.section_unit P.Coefficient (pullback.fst v i)]
  simpa only [Etale.closedConstantPullbackRestriction, unitIso, Iso.app_hom] using
    (Etale.pullback_restriction P.Coefficient i v).symm

private lemma etaleExchangeNative_isIso (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    IsIso (etaleExchangeNative A i v) := by
  exact (Etale.closedConstantTensor A X i i i v).1

private lemma etaleSupportSections_isIso (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    IsIso (etaleSupportSections A i Y) := by
  have := etaleExchangeNative_isIso A (X' := Y.left) i Y.hom
  dsimp only [etaleSupportSections]
  infer_instance

private lemma constantComparisonSections_isIso (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : IsIso (constantComparisonSections A T) := by
  have := ProEtale.isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} A) T
  dsimp only [constantComparisonSections]
  infer_instance

private lemma section_diagram
    {V : Type*} [Category V] {A B C D E F G H : V}
    (χ : B ≅ A) (u : C ≅ B) (e : C ⟶ D) (u' : D ⟶ E)
    (e' : B ⟶ E) (g : E ⟶ F) (tp : F ⟶ G) (te : D ⟶ H) (c : H ⟶ G)
    (q : A ⟶ F) (hs : χ.hom ≫ q = e' ≫ g)
    (hn : u.hom ≫ e' = e ≫ u') (ht : u' ≫ g ≫ tp = te ≫ c) :
    q ≫ tp = χ.inv ≫ u.inv ≫ e ≫ te ≫ c := by
  apply (cancel_epi χ.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hs, Category.assoc]
  apply (cancel_epi u.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hn, Category.assoc, ht]

private lemma comparisonSections_hom (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} (F : Modules A false X) (Y : X.ProEt) :
    (comparisonSections A F Y).hom =
      (localizationSections A ((compare A X).obj F) Y).hom ≫
        (comparisonSectionPullbackIso A F Y).inv ≫
          (terminalComparisonUnitIso (ModuleCat.{u + 1} A) Y.left
            ((pull A false (X := Y.left) Y.hom).obj F)).inv := by
  dsimp only [comparisonSections, localizationSections, genericLocalization,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, Iso.op_hom]
  simp only [Category.assoc]

private lemma etaleSupportSections_hom (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    etaleSupportSections A i Y =
      (etaleExchangeNative A (X' := Y.left) i Y.hom).hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
        (terminalSupport A false (X := Y.left) (pullback.fst Y.hom i)).hom := by
  dsimp only [etaleSupportSections, terminalSupport, Iso.symm_hom,
    Functor.mapIso_hom, Iso.op_hom]

private lemma section_combination {V : Type*} [Category V]
    {A B C D E F G H I J : V}
    {γ : A ⟶ B} {p : B ⟶ G} {l : B ⟶ C} {l' : A ⟶ D}
    {q : D ⟶ C} {β : C ⟶ E} {tp : E ⟶ G}
    {χ : D ⟶ I} {u : I ⟶ F} {e : F ⟶ H} {te : H ⟶ J} {c : J ⟶ G}
    {s : A ⟶ F} {t : F ⟶ J}
    (hp : p = l ≫ β ≫ tp) (hl : γ ≫ l = l' ≫ q)
    (hd : (q ≫ β) ≫ tp = χ ≫ u ≫ e ≫ te ≫ c)
    (hs : s = l' ≫ χ ≫ u) (ht : t = e ≫ te) :
    γ ≫ p = s ≫ t ≫ c := by
  rw [hp, ← Category.assoc, hl]
  calc
    (l' ≫ q) ≫ β ≫ tp = l' ≫ ((q ≫ β) ≫ tp) := by simp only [Category.assoc]
    _ = l' ≫ (χ ≫ u ≫ e ≫ te ≫ c) := congrArg (fun f ↦ l' ≫ f) hd
    _ = s ≫ t ≫ c := by rw [hs, ht]; simp only [Category.assoc]

private lemma terminal_comparison_transport (A : Type (u + 1)) [CommRing A]
    {X' X : Scheme.{u}} (h : X' ⟶ X)
    (F : Modules A false X) (G : Modules A false X') (H : Modules A true X')
    (e : (pull A false h).obj F ⟶ G) (g : (compare A X').obj G ⟶ H)
    (q : (pull A true h).obj ((compare A X).obj F) ⟶ H)
    {T U : ModuleCat.{u + 1} A}
    (tp : H.obj.obj (op (Scheme.ProEt.mk (𝟙 X'))) ⟶ T)
    (te : G.obj.obj (op (Scheme.Etale.mk (𝟙 X'))) ⟶ U) (c : U ⟶ T)
    (hs : (compare A X').map e ≫ g = (comparePullback A h).hom.app F ≫ q)
    (ht : (terminalComparisonUnitIso (ModuleCat.{u + 1} A) X' G).hom ≫
      g.hom.app (op (Scheme.ProEt.mk (𝟙 X'))) ≫ tp = te ≫ c) :
    q.hom.app (op (Scheme.ProEt.mk (𝟙 X'))) ≫ tp =
      (genericComparisonSectionIso A h F).inv ≫
      (terminalComparisonUnitIso (ModuleCat.{u + 1} A) X'
        ((pull A false h).obj F)).inv ≫
      e.hom.app (op (Scheme.Etale.mk (𝟙 X'))) ≫ te ≫ c := by
  have hs' := congrArg (fun f ↦ f.hom.app (op (Scheme.ProEt.mk (𝟙 X')))) hs
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hs'
  exact section_diagram
    (genericComparisonSectionIso A h F)
    (terminalComparisonUnitIso (ModuleCat.{u + 1} A) X' ((pull A false h).obj F))
    (e.hom.app (op (Scheme.Etale.mk (𝟙 X'))))
    (terminalComparisonUnitIso (ModuleCat.{u + 1} A) X' G).hom
    (((compare A X').map e).hom.app (op (Scheme.ProEt.mk (𝟙 X'))))
    (g.hom.app (op (Scheme.ProEt.mk (𝟙 X')))) tp te c
    (q.hom.app (op (Scheme.ProEt.mk (𝟙 X'))))
    (by simpa only [genericComparisonSectionIso_hom, Functor.comp_obj] using hs'.symm)
    (terminalComparisonUnitIso_naturality (ModuleCat.{u + 1} A) X' e) ht

private lemma terminal_base_square (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    (((pull P.Coefficient true v).map (gamma P.Coefficient i)).hom.app
        (op (Scheme.ProEt.mk (𝟙 X'))) ≫
      (baseExchange P.Coefficient i v).hom.app (op (Scheme.ProEt.mk (𝟙 X')))) ≫
        (terminalSupport P.Coefficient true (pullback.fst v i)).hom =
      (genericComparisonSectionIso P.Coefficient v
        (supported P.Coefficient false i)).inv ≫
      (terminalComparisonUnitIso (ModuleCat.{u + 1} P.Coefficient) X'
        ((pull P.Coefficient false v).obj (supported P.Coefficient false i))).inv ≫
      (etaleExchangeNative P.Coefficient i v).hom.app (op (Scheme.Etale.mk (𝟙 X'))) ≫
      (terminalSupport P.Coefficient false (pullback.fst v i)).hom ≫
      constantComparisonSections P.Coefficient (pullback v i) := by
  have hs := (comparison_square P (baseSquare i v)).1
  rw [etale_exchange P i v] at hs
  have ht := gamma_terminal P (pullback.fst v i)
  exact terminal_comparison_transport P.Coefficient v
    (supported P.Coefficient false i)
    (supported P.Coefficient false (pullback.fst v i))
    (supported P.Coefficient true (pullback.fst v i))
    (etaleExchangeNative P.Coefficient i v)
    (gamma P.Coefficient (pullback.fst v i))
    ((pull P.Coefficient true v).map (gamma P.Coefficient i) ≫
      baseExchange P.Coefficient i v)
    (terminalSupport P.Coefficient true (pullback.fst v i)).hom
    (terminalSupport P.Coefficient false (pullback.fst v i)).hom
    (constantComparisonSections P.Coefficient (pullback v i)) hs
    (by simpa only [terminalComparisonUnitIso_hom] using ht)

private lemma localized_section_transport (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} (F : Modules A false X) (G : Modules A true X)
    (γ : (compare A X).obj F ⟶ G) (Y : X.ProEt)
    (H : Modules A false Y.left) (K : Modules A true Y.left)
    (e : (pull A false (X := Y.left) Y.hom).obj F ⟶ H)
    (β : (pull A true (X := Y.left) Y.hom).obj G ⟶ K)
    {U T : ModuleCat.{u + 1} A}
    (tp : K.obj.obj (op (Scheme.ProEt.mk (𝟙 Y.left))) ⟶ T)
    (te : H.obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) ⟶ U) (c : U ⟶ T)
    (p : G.obj.obj (op Y) ⟶ T)
    (t : ((pull A false (X := Y.left) Y.hom).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 Y.left))) ⟶ U)
    (hp : p = (localizationSections A G Y).hom ≫
      β.hom.app (op (Scheme.ProEt.mk (𝟙 Y.left))) ≫ tp)
    (hd : (((pull A true (X := Y.left) Y.hom).map γ).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y.left))) ≫
      β.hom.app (op (Scheme.ProEt.mk (𝟙 Y.left)))) ≫ tp =
      (genericComparisonSectionIso A (X' := Y.left) Y.hom F).inv ≫
      (terminalComparisonUnitIso (ModuleCat.{u + 1} A) Y.left
        ((pull A false (X := Y.left) Y.hom).obj F)).inv ≫
      e.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫ te ≫ c)
    (ht : t = e.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) ≫ te) :
    γ.hom.app (op Y) ≫ p = (comparisonSections A F Y).hom ≫ t ≫ c := by
  exact section_combination hp (localizationSections_naturality A γ Y) hd
    (comparisonSections_hom A F Y) ht

private lemma section_formula (P : WeilConjectures.PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (Y : X.ProEt) :
    (gamma P.Coefficient i).hom.app (op Y) ≫
        (proSupportSections P.Coefficient i Y).hom =
      (comparisonSections P.Coefficient (supported P.Coefficient false i) Y).hom ≫
        etaleSupportSections P.Coefficient i Y ≫
          constantComparisonSections P.Coefficient (pullback Y.hom i) := by
  exact localized_section_transport P.Coefficient
    (supported P.Coefficient false i) (supported P.Coefficient true i)
    (gamma P.Coefficient i) Y
    (supported P.Coefficient false (X := Y.left) (pullback.fst Y.hom i))
    (supported P.Coefficient true (X := Y.left) (pullback.fst Y.hom i))
    (etaleExchangeNative P.Coefficient (X' := Y.left) i Y.hom)
    (baseExchange P.Coefficient (X' := Y.left) i Y.hom)
    (terminalSupport P.Coefficient true (X := Y.left) (pullback.fst Y.hom i)).hom
    (terminalSupport P.Coefficient false (X := Y.left) (pullback.fst Y.hom i)).hom
    (constantComparisonSections P.Coefficient (pullback Y.hom i))
    (proSupportSections P.Coefficient i Y).hom (etaleSupportSections P.Coefficient i Y)
    (pro_sections P.Coefficient i Y)
    (terminal_base_square P (X' := Y.left) i Y.hom)
    (etaleSupportSections_hom P.Coefficient i Y)

section
variable {B : Type c} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {E : Type d} [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Monoidal] [F.PreservesFlat] [F.IsLeftAdjoint]

private noncomputable def st (M N : B) :
    (HomologicalComplex.single B (.up ℤ) 0).obj M ⊗
      (HomologicalComplex.single B (.up ℤ) 0).obj N ≅
      (HomologicalComplex.single B (.up ℤ) 0).obj (M ⊗ N) :=
  (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor B) M
    ((HomologicalComplex.single B (.up ℤ) 0).obj N)) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft M) (.up ℤ) 0).app N)

omit [Abelian.HasFunctorialFlatResolution B] in
private lemma st_inv_f (M N : B) :
    (st M N).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (M ⊗ N)).hom ≫
        tensorHom (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫
        HomologicalComplex.ιMapBifunctor
          ((HomologicalComplex.single B (.up ℤ) 0).obj M)
          ((HomologicalComplex.single B (.up ℤ) 0).obj N) (curriedTensor B) (.up ℤ)
          0 0 0 (by simp) := by
  simp only [st, Iso.trans_inv, Iso.app_inv, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f, Category.assoc]
  rw [MonoidalCategory.tensorHom_def', Category.assoc]
  rfl

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesFlat]
  [Abelian.HasFunctorialFlatResolution B] [Abelian.HasFunctorialFlatResolution E] in
private lemma st_comparison (M N : B) :
    (F.mapHomologicalComplex (.up ℤ)).map (st M N).inv ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
          ((HomologicalComplex.single B (.up ℤ) 0).obj M)).app
          ((HomologicalComplex.single B (.up ℤ) 0).obj N) ≫
        tensorHom ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N) =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (M ⊗ N) ≫
        (HomologicalComplex.single E (.up ℤ) 0).map (Functor.OplaxMonoidal.δ F M N) ≫
        (st (F.obj M) (F.obj N)).inv := by
  ext n : 1
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, st_inv_f,
      Functor.map_comp, Category.assoc,
      Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
      HomologicalComplex.mapBifunctorComparison_f]
    erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self,
      HomologicalComplex.mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans_app_app]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      curriedTensor_map_app, curriedTensor_obj_map, Functor.comp_obj,
      Functor.mapHomologicalComplex_obj_X]
    rw [← MonoidalCategory.tensorHom_def_assoc]
    erw [← Functor.OplaxMonoidal.δ_natural_assoc]
    simp only [tensorHom_comp_tensorHom_assoc, Iso.map_inv_hom_id_assoc]
  · apply IsZero.eq_of_src
    exact F.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (M ⊗ N) n hn)

omit [Abelian.HasFunctorialFlatResolution B] in
private lemma st_inv_naturality {M N M' N' : B} (f : M ⟶ M') (g : N ⟶ N') :
    (HomologicalComplex.single B (.up ℤ) 0).map (tensorHom f g) ≫ (st M' N').inv =
      (st M N).inv ≫ tensorHom
        ((HomologicalComplex.single B (.up ℤ) 0).map f)
        ((HomologicalComplex.single B (.up ℤ) 0).map g) := by
  ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self, st_inv_f,
    Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.single_map_f_self,
    curriedTensor_map_app, curriedTensor_obj_map]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_assoc]

omit [F.PreservesFlat] [Abelian.HasFunctorialFlatResolution B]
  [Abelian.HasFunctorialFlatResolution E] in
private lemma cochain_square {M N K : B} {M' N' K' : E}
    (μ : M ⊗ N ⟶ K) (μ' : M' ⊗ N' ⟶ K')
    (qM : F.obj M ⟶ M') (qN : F.obj N ⟶ N') (qK : F.obj K ⟶ K')
    (h : F.map μ ≫ qK = Functor.OplaxMonoidal.δ F M N ≫ tensorHom qM qN ≫ μ') :
    (F.mapHomologicalComplex (.up ℤ)).map
        ((st M N).hom ≫ (HomologicalComplex.single B (.up ℤ) 0).map μ) ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app K ≫
      (HomologicalComplex.single E (.up ℤ) 0).map qK =
    ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        ((HomologicalComplex.single B (.up ℤ) 0).obj M)).app
        ((HomologicalComplex.single B (.up ℤ) 0).obj N) ≫
      tensorHom
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
          (HomologicalComplex.single E (.up ℤ) 0).map qM)
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app N ≫
          (HomologicalComplex.single E (.up ℤ) 0).map qN) ≫
      (st M' N').hom ≫ (HomologicalComplex.single E (.up ℤ) 0).map μ' := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (st M N).inv)).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc,
    ← tensorHom_comp_tensorHom_assoc]
  rw [reassoc_of% st_comparison F M N]
  rw [← reassoc_of% st_inv_naturality, Iso.inv_hom_id_assoc]
  have hn := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.naturality μ
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp, h]
  simp only [CategoryTheory.Functor.map_comp]

private noncomputable def cc (K : CochainComplex B ℤ) :
    F.leftDerivedFunctor.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj K) ≫
    F.mapDerivedCategoryFactors.hom.app K

omit [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E]
  [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [F.Monoidal] [F.PreservesFlat] [F.IsLeftAdjoint] in
private lemma single_left_derived (M : B) :
    F.singleFunctorCompLeftDerivedFunctorIso.hom.app M =
      cc F ((HomologicalComplex.single B (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) := by
  simp only [cc, Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  apply congrArg (fun f ↦ F.leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫ f)
  apply (cancel_epi (F.mapDerivedCategoryFactors.inv.app
    ((HomologicalComplex.single B (.up ℤ) 0).obj M))).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc,
    Functor.mapCochainComplexSingleFunctor] using
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M

omit [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E]
  [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [F.Monoidal] [F.PreservesFlat] [F.IsLeftAdjoint] in
private lemma cc_counit (K : CochainComplex B ℤ) :
    cc F K =
      F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) := by
  have h := congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient B (.up ℤ)).obj K)
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom, Quotient.lift.isLift_inv] at h
  erw [F.mapDerivedCategory.map_id, Category.id_comp,
    (DerivedCategory.Qh (C := E)).map_id, Category.comp_id, Category.comp_id] at h
  exact h

private lemma mu_Q (K L : CochainComplex B ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q K L =
      Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := B))
        ((HomotopyCategory.quotient B (.up ℤ)).obj K)
        ((HomotopyCategory.quotient B (.up ℤ)).obj L) := by
  change (tensorHom (𝟙 _) (𝟙 _)) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := B)) _ _ ≫
        (DerivedCategory.Qh (C := B)).map (𝟙 _)) ≫
        𝟙 _ = _
  simp only [tensorHom_id]
  erw [id_whiskerRight, (DerivedCategory.Qh (C := B)).map_id,
    Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

private lemma cc_tensor (K L : CochainComplex B ℤ) :
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L)) ≫ tensorHom (cc F K) (cc F L) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj K)
        ((F.mapHomologicalComplex (.up ℤ)).obj L) =
    F.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
      cc F (K ⊗ L) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L) := by
  have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom
    ((HomotopyCategory.quotient B (.up ℤ)).obj K)
    ((HomotopyCategory.quotient B (.up ℤ)).obj L)
  simp only [cc_counit, mu_Q]
  simp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as] at h
  convert h using 1 <;> rfl
omit [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E]
  [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [F.Monoidal] [F.PreservesFlat] [F.IsLeftAdjoint] in
private lemma cc_naturality {K L : CochainComplex B ℤ} (f : K ⟶ L) :
    F.leftDerivedFunctor.map (DerivedCategory.Q.map f) ≫ cc F L =
      cc F K ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  dsimp only [cc]
  rw [F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  rw [F.mapDerivedCategoryFactors_hom_naturality]
  simp only [Category.assoc]

private lemma derived_square {M N K : B} {M' N' K' : E}
    (μ : M ⊗ N ⟶ K) (μ' : M' ⊗ N' ⟶ K')
    (qM : F.obj M ⟶ M') (qN : F.obj N ⟶ N') (qK : F.obj K ⟶ K')
    (h : F.map μ ≫ qK = Functor.OplaxMonoidal.δ F M N ≫ tensorHom qM qN ≫ μ') :
    DerivedSquare F μ μ' qM qN qK := by
  unfold DerivedSquare ProEtale.cupDerivedCoefficientMap ProEtale.cupSingleTensorMap
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, tensorIso_hom, tensorHom_id, Category.id_comp,
    id_whiskerRight]
  simp only [Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  change F.leftDerivedFunctor.map
      (Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
        DerivedCategory.Q.map (st M N).hom ≫
          DerivedCategory.Q.map ((HomologicalComplex.single B (.up ℤ) 0).map μ)) ≫
      F.singleFunctorCompLeftDerivedFunctorIso.hom.app K ≫
        DerivedCategory.Q.map ((HomologicalComplex.single E (.up ℤ) 0).map qK) = _
  simp only [single_left_derived, F.leftDerivedFunctor.map_comp, Category.assoc,
    reassoc_of% cc_naturality, ← DerivedCategory.Q.map_comp]
  rw [cochain_square F μ μ' qM qN qK h]
  simp only [DerivedCategory.Q.map_comp]
  erw [← reassoc_of% cc_tensor]
  erw [← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, DerivedCategory.Q.map_comp]
  rfl

end

/-- The prescribed closed exchanges have the section formula and preserve both ordinary
and derived restriction-and-multiplication pairings, on every weakly etale test.
Source: Stacks 0GLZ, 099V, 099W, 03EL, 07A4 and 0G7E; supported cup functoriality
Steps 2 and 6 (blueprint: lem-pur-closed-source-site-tensor-comparison).

Proof:
1. Identify the prescribed exchanges with the usual monoidal mates by their constant-unit
normalization and uniqueness. Evaluate the comparison mate at the terminal object and
use naturality along its canonical pullback isomorphism. Weakly etale base change is
localization restriction; its site-map formula and pullback universal properties identify
the terminal evaluation with proSupportSections. The normalized comparison square and
naturality of the comparison unit then give the stated section formula.
2. Restriction compatibility is naturality of gamma; scalar compatibility is linearity.
3. The supplied cokernel presentations make constant restriction epic. Tensor preserves
epimorphisms, as do the inverse-image functors. Precompose each multiplication square
with the tensor of the two constant restrictions. Oplax monoidal naturality, unit
normalization of the exchanges, and normalization of multiplication identify both sides.
The support-change map preserves restriction by adjunction and lower-star composition.
Cancel the epic tensor. This argument works for every scheme morphism v.
4. The canonical single-complex tensor isomorphism commutes with the cochain oplax
comparison: degree zero is the single-object evaluation identity and every other degree
is zero. Apply this to the ordinary squares. Naturality of the exact left-derived functor
comparison and its tensor-comparison identity then transport these cochain squares to
the displayed DerivedSquare equations. Empty and nonreduced supports need no exception. -/
theorem closedSourceSiteTensorComparison
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    {C D X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : X' ⟶ X) :
    (∀ Y : X.ProEt,
      IsIso (etaleSupportSections P.Coefficient i Y) ∧
      IsIso (constantComparisonSections P.Coefficient (pullback Y.hom i)) ∧
      (gamma P.Coefficient i).hom.app (op Y) ≫
          (proSupportSections P.Coefficient i Y).hom =
        (comparisonSections P.Coefficient (supported P.Coefficient false i) Y).hom ≫
          etaleSupportSections P.Coefficient i Y ≫
          constantComparisonSections P.Coefficient (pullback Y.hom i)) ∧
    (∀ (Y Z : X.ProEt) (g : Z ⟶ Y),
      (gamma P.Coefficient i).hom.app (op Y) ≫
          (supported P.Coefficient true i).obj.map g.op =
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
          (supported P.Coefficient false i)).obj.map g.op ≫
          (gamma P.Coefficient i).hom.app (op Z)) ∧
    (∀ (Y : X.ProEt) (a : P.Coefficient)
      (s : ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
        (supported P.Coefficient false i)).obj.obj (op Y)),
      (gamma P.Coefficient i).hom.app (op Y) (a • s) =
        a • (gamma P.Coefficient i).hom.app (op Y) s) ∧
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (Etale.closedConstantTensorMap P.Coefficient i j) ≫
        gamma P.Coefficient (Etale.intersectionSupport i j) =
      Functor.OplaxMonoidal.δ
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X) _ _ ≫
        tensorHom (gamma P.Coefficient i) (gamma P.Coefficient j) ≫ multiplication P i j) ∧
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).map (multiplication P i j) ≫
        baseExchange P.Coefficient (Etale.intersectionSupport i j) v ≫
        baseSupportChange P.Coefficient i j v =
      Functor.OplaxMonoidal.δ (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v) _ _ ≫
        tensorHom (baseExchange P.Coefficient i v) (baseExchange P.Coefficient j v) ≫
          multiplication P (pullback.fst v i) (pullback.fst v j)) ∧
    DerivedSquare (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (Etale.closedConstantTensorMap P.Coefficient i j) (multiplication P i j)
      (gamma P.Coefficient i) (gamma P.Coefficient j)
      (gamma P.Coefficient (Etale.intersectionSupport i j)) ∧
    DerivedSquare (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v) (multiplication P i j)
      (multiplication P (pullback.fst v i) (pullback.fst v j))
      (baseExchange P.Coefficient i v) (baseExchange P.Coefficient j v)
      (baseExchange P.Coefficient (Etale.intersectionSupport i j) v ≫
        baseSupportChange P.Coefficient i j v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y
    refine ⟨etaleSupportSections_isIso P.Coefficient i Y,
      constantComparisonSections_isIso P.Coefficient (pullback Y.hom i), ?_⟩
    exact section_formula P i Y
  · intro Y Z g
    exact ((gamma P.Coefficient i).hom.naturality g.op).symm
  · intro Y a s
    exact ((gamma P.Coefficient i).hom.app (op Y)).hom.map_smul a s
  · exact comparison_product P i j
  · exact pullback_product P i j v
  · exact derived_square _ _ _ _ _ _ (comparison_product P i j)
  · exact derived_square _ _ _ _ _ _ (pullback_product P i j v)

end AlgebraicGeometry.ClosedSourceSiteTensor
