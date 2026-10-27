/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Paper.CompletedStalkReparametrizationCoherence
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.PointProEtaleSectionsExact
import all Sheaf.Paper.IntegralOperationsWellDefined
import all Sheaf.Paper.PointQuotientAugmentationDiagram
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Localization of point-section maps into completed-pullback cones

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, clause (3), point-transport supplement;
Stacks Tags 014E, 04VI, 04VK and 06YS
(blueprint: lem-trf-point-pullback-cone-localization).

All complexes are unbounded. A tower index n denotes the positive exponent n+1.
The strict towers, their coefficient-induced transitions, the signed Roos complex,
and its two-coordinate sections comparison are the published constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointPullbackCone

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] limit completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard CochainComplex.mappingCocone towerTransitionEndomorphism
  pointIntegralSections integralOperationsPullbackLevel

/-- S(P)=[Gamma P] on flat-term K-flat complexes, with its actual action on chain maps.
Source: blueprint clause (3) (blueprint: lem-trf-point-pullback-cone-localization). -/
def source :=
  (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
    CompletedStalk.sectionsComplex D l E ⋙ CompletedStalk.moduleQ l E

/-- T(P)=[H(Gamma C(P))], with the actual coefficient-induced pullback transitions.
Source: blueprint clause (3) (blueprint: lem-trf-point-pullback-cone-localization). -/
def target :=
  (integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
    integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (CompletedStalk.sectionsComplex D l E) ⋙
    integralOperationsRoosFunctor ⋙ CompletedStalk.moduleQ l E

/-- The full homotopy subcategory on exactly the flat-term K-flat representatives.
Source: Stacks 06YS (blueprint: lem-trf-point-pullback-cone-localization). -/
def goodHomotopy : ObjectProperty
    (HomotopyCategory (integralTowerModules l E (Spec (.of D.k))) (.up ℤ)) :=
  fun X ↦ integralOperationsGoodComplex l E (Spec (.of D.k)) X.as

/-- The canonical homotopy quotient, restricted to the resolving class.
Source: Stacks 014E, 06YS (blueprint: lem-trf-point-pullback-cone-localization). -/
def toHomotopy :=
  (goodHomotopy D l E).lift
    ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
      HomotopyCategory.quotient _ (.up ℤ)) (fun P ↦ P.property)

/-- The exact-sections comparison with the two published localization sizes.
Source: Stacks 015F (blueprint: lem-trf-point-pullback-cone-localization). -/
def sectionsFactors :=
  @Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _)
    _ _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointIntegralSections l E D.k) _ _ _

/-- The normalized b_q for any endomorphism of the point: apply completed pullback to
[q] inverse, then its representative comparison, exact sections, and the identity on
both Roos coordinates. The Frobenius specialization is used in the main statement.
Source: blueprint clause (3) (blueprint: lem-trf-point-pullback-cone-localization). -/
def representativeComparison (g : Spec (.of D.k) ⟶ Spec (.of D.k))
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :=
  (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullback l E g).mapIso (asIso (DerivedCategory.Q.map q)).symm) ≪≫
    (pointFibreIntegralAmbient D l E).mapIso
      ((integralDerivedPullbackComparison l E g).app P) ≪≫
    (sectionsFactors D l E).app ((integralOperationsPullbackComplexFunctor l E g).obj P.obj) ≪≫
    (CompletedStalk.moduleQ l E).mapIso
      (CompletedStalk.sectionsRoos D l E
        ((integralOperationsPullbackTowerFunctor l E g).obj P.obj))

-- Reuse the natural comparison and identify it with the prescribed coordinate normalization.
private def roosComparison :=
  let := WeilConjectures.PointQuotientAugmentation.sectionsProducts l E D.k
  WeilConjectures.PointQuotientAugmentation.roosComparison (pointIntegralSections l E D.k)

private theorem roosComparison_app
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    (roosComparison D l E).app T = CompletedStalk.sectionsRoos D l E T := by
  let := WeilConjectures.PointQuotientAugmentation.sectionsProducts l E D.k
  apply (CompletedStalk.sectionsRoos_existsUnique D l E T).unique
  · have h := WeilConjectures.PointQuotientAugmentation.roosComparison_coordinates
      (pointIntegralSections l E D.k)
    exact ⟨fun n i ↦ h.1 T n i, fun n i ↦ h.2 T n i⟩
  · exact (CompletedStalk.sectionsRoos_existsUnique D l E T).exists.choose_spec

private def sourceComparison :
    integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙
        pointFibreIntegralAmbient D l E ≅ source D l E :=
  Functor.isoWhiskerLeft (integralOperationsGoodComplex l E (Spec (.of D.k))).ι
    (sectionsFactors D l E)

private def targetComparison :
    integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙
        (integralDerivedPullback l E (frobeniusPointIso D).hom ⋙
          pointFibreIntegralAmbient D l E) ≅ target D l E :=
  Functor.isoWhiskerRight (integralDerivedPullbackComparison l E (frobeniusPointIso D).hom)
      (pointFibreIntegralAmbient D l E) ≪≫
    Functor.isoWhiskerLeft
      ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
        integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom)
      (sectionsFactors D l E) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((integralOperationsGoodComplex l E (Spec (.of D.k))).ι ⋙
          integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom)
        (roosComparison D l E)) (CompletedStalk.moduleQ l E)

-- Transport from Qh to the exact object assignment required by the statement.
private def homotopyComparison
    (F : DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _))
    (F₀ : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory ⥤ _)
    (e : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ F ≅ F₀)
    (P : (goodHomotopy D l E).FullSubcategory) :
    F.obj (DerivedCategory.Qh.obj P.obj) ≅ F₀.obj ⟨P.obj.as, P.property⟩ :=
  F.mapIso ((DerivedCategory.quotientCompQhIso _).app P.obj.as) ≪≫
    e.app ⟨P.obj.as, P.property⟩

attribute [local irreducible] homotopyComparison

private def homotopyFactor
    (F : DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _))
    (F₀ : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory ⥤ _)
    (e : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ F ≅ F₀) :
    (goodHomotopy D l E).FullSubcategory ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _) where
  obj P := F₀.obj ⟨P.obj.as, P.property⟩
  map {P Q} f := (homotopyComparison D l E F F₀ e P).inv ≫
    F.map (DerivedCategory.Qh.map f.hom) ≫ (homotopyComparison D l E F F₀ e Q).hom
  map_id P := by
    change (homotopyComparison D l E F F₀ e P).inv ≫
      F.map (DerivedCategory.Qh.map (𝟙 P.obj)) ≫
        (homotopyComparison D l E F F₀ e P).hom = _
    erw [DerivedCategory.Qh.map_id, F.map_id, Category.id_comp]
    exact (homotopyComparison D l E F F₀ e P).inv_hom_id
  map_comp f g := by
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc]


private theorem mapped_conjugation
    {C : Type*} [Category* C] {H : Type*} [Category* H] (F : C ⥤ H)
    {X X' Y Y' : C} {A B : H} (i : X ≅ X') (j : Y ≅ Y')
    (a : F.obj X' ≅ A) (b : F.obj Y' ≅ B) (f : X ⟶ Y) :
    (F.mapIso i ≪≫ a).inv ≫ F.map f ≫ (F.mapIso j ≪≫ b).hom =
      a.inv ≫ F.map (i.inv ≫ f ≫ j.hom) ≫ b.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
private theorem homotopyFactor_fac
    (F : DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _))
    (F₀ : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory ⥤ _)
    (e : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ F ≅ F₀) :
    toHomotopy D l E ⋙ homotopyFactor D l E F F₀ e = F₀ := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro P
    rfl
  intro P Q f
  change HEq ((homotopyComparison D l E F F₀ e
      ⟨(HomotopyCategory.quotient _ _).obj P.obj, P.property⟩).inv ≫
    F.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f.hom)) ≫
      (homotopyComparison D l E F F₀ e
        ⟨(HomotopyCategory.quotient _ _).obj Q.obj, Q.property⟩).hom) (F₀.map f)
  apply heq_of_eq
  let j := DerivedCategory.quotientCompQhIso
    (integralTowerModules l E (Spec (.of D.k)))
  have hn : j.inv.app P.obj ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f.hom) ≫
        j.hom.app Q.obj = DerivedCategory.Q.map f.hom := by
    simpa only [Iso.app_inv, Iso.app_hom, Functor.comp_map] using
      (NatIso.naturality_1 j f.hom)
  have hcmp : (homotopyComparison D l E F F₀ e
      ⟨(HomotopyCategory.quotient _ _).obj P.obj, P.property⟩).inv ≫
      F.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f.hom)) ≫
        (homotopyComparison D l E F F₀ e
          ⟨(HomotopyCategory.quotient _ _).obj Q.obj, Q.property⟩).hom =
      (e.app P).inv ≫ F.map (j.inv.app P.obj ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f.hom) ≫
          j.hom.app Q.obj) ≫ (e.app Q).hom := by
    unfold homotopyComparison
    change (F.mapIso (j.app P.obj) ≪≫ e.app P).inv ≫ _ ≫
      (F.mapIso (j.app Q.obj) ≪≫ e.app Q).hom = _
    exact mapped_conjugation F (j.app P.obj) (j.app Q.obj) (e.app P) (e.app Q) _
  exact hcmp.trans ((congrArg
    (fun t ↦ (e.app P).inv ≫ F.map t ≫ (e.app Q).hom) hn).trans
      (NatIso.naturality_1 e f))

private theorem homotopyFactor_inverts
    (F : DerivedCategory (integralTowerModules l E (Spec (.of D.k))) ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _))
    (F₀ : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory ⥤ _)
    (e : integralOperationsGoodLocalization l E (Spec (.of D.k)) ⋙ F ≅ F₀) :
    ((HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage
      (goodHomotopy D l E).ι).IsInvertedBy (homotopyFactor D l E F F₀ e) := by
  intro P Q f hf
  have : IsIso (DerivedCategory.Qh.map f.hom) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) f.hom hf
  change IsIso (_ ≫ F.map (DerivedCategory.Qh.map f.hom) ≫ _)
  infer_instance

attribute [local irreducible] homotopyFactor

-- The remaining identities are formal conjugation and fraction calculations.
private theorem comparison_inverts
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (L : A ⥤ B) (F : B ⥤ C) (F₀ : A ⥤ C)
    (e : L ⋙ F ≅ F₀) {X Y : A} (f : X ⟶ Y) [IsIso (L.map f)] :
    IsIso (F₀.map f) := by
  have h : F₀.map f = (e.app X).inv ≫ F.map (L.map f) ≫ (e.app Y).hom := by
    simpa using (NatIso.naturality_1 e f).symm
  rw [h]
  infer_instance

private theorem comparison_roof
    {A : Type*} [Category* A] {B : Type*} [Category* B]
    {C : Type*} [Category* C] (L : A ⥤ B) (F : B ⥤ C) (F₀ : A ⥤ C)
    (e : L ⋙ F ≅ F₀) {X Y Z : A} (a : Z ⟶ X) (b : Z ⟶ Y)
    [IsIso (L.map a)] [IsIso (F₀.map a)] :
    inv (F₀.map a) ≫ F₀.map b =
      (e.app X).inv ≫ F.map (inv (L.map a) ≫ L.map b) ≫ (e.app Y).hom := by
  apply (cancel_epi (F₀.map a)).1
  simp only [IsIso.hom_inv_id_assoc, Functor.map_comp, Functor.map_inv]
  simp only [Iso.app_inv, Iso.app_hom]
  rw [← Category.assoc (F₀.map a), e.inv.naturality a]
  simp only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc]
  exact (NatIso.naturality_1 e b).symm

private theorem representativeComparison_eq
    (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (q : P.obj ⟶ N) [QuasiIso q] :
    representativeComparison D l E (frobeniusPointIso D).hom N P q =
      ((integralDerivedPullback l E (frobeniusPointIso D).hom ⋙
        pointFibreIntegralAmbient D l E).mapIso (asIso (DerivedCategory.Q.map q)).symm) ≪≫
        (targetComparison D l E).app P := by
  apply Iso.ext
  dsimp only [representativeComparison, targetComparison, Iso.app_hom,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp, Functor.comp_map]
  rw [← Iso.app_hom (roosComparison D l E), roosComparison_app]
  rfl

-- Naturality determines the value at every resolving quasi-isomorphism.
private theorem resolution_formula
    {C : Type*} [Category* C] {H : Type*} [Category* H]
    (F G : C ⥤ H) (η : F ⟶ G) {X Y : C} (q : X ⟶ Y) [IsIso q]
    {A B T : H} (eX : F.obj X ≅ A) (eY : F.obj Y ≅ B) (d : G.obj X ≅ T)
    (s : A ⟶ B) [IsIso s] (η₀ : A ⟶ T)
    (hn : F.map q ≫ eY.hom = eX.hom ≫ s)
    (hη : η.app X ≫ d.hom = eX.hom ≫ η₀) :
    η.app Y ≫ G.map (inv q) ≫ d.hom = eY.hom ≫ inv s ≫ η₀ := by
  apply (cancel_epi (F.map q)).1
  rw [← Category.assoc, η.naturality q]
  simp only [Category.assoc, ← G.map_comp_assoc, IsIso.hom_inv_id, G.map_id,
    Category.id_comp]
  rw [hη, ← Category.assoc, hn]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

private theorem normalize_identity_formula
    {C : Type*} [Category* C] {B : Type*} [Category* B]
    {H : Type*} [Category* H] (L : C ⥤ B) (S : C ⥤ H)
    (F G : B ⥤ H) (τ : F ⟶ G) (X : C) {T : H}
    (d : G.obj (L.obj X) ≅ T) (e : F.obj (L.obj X) ≅ S.obj X)
    (η₀ : S.obj X ⟶ T)
    (h : τ.app (L.obj X) ≫ G.map (inv (L.map (𝟙 X))) ≫ d.hom =
      e.hom ≫ inv (S.map (𝟙 X)) ≫ η₀) :
    τ.app (L.obj X) ≫ d.hom = e.hom ≫ η₀ := by
  simpa using h

private theorem refine_roof
    {C : Type*} [Category* C] {H : Type*} [Category* H]
    (F : C ⥤ H) {X Y Z R : C} (r : R ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y)
    [IsIso (F.map r)] [IsIso (F.map a)] [IsIso (F.map (r ≫ a))] :
    inv (F.map a) ≫ F.map b = inv (F.map (r ≫ a)) ≫ F.map (r ≫ b) := by
  simp only [Functor.map_comp, IsIso.inv_comp, Category.assoc,
    IsIso.inv_hom_id_assoc]

attribute [local irreducible] sourceComparison targetComparison roosComparison

/-- Point sections and the sectionwise completed-pullback cone factor through homotopy,
invert the resolving-class quasi-isomorphisms, and extend every chain-natural family
uniquely to the ambient derived category, with the prescribed formula for every resolution.
The roof equation and the equality of the two images for equal derived roofs are explicit;
every derived morphism between good representatives admits such a roof.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model.proof.md,
clause (3), point-transport comparison supplement, original steps 7--8; Stacks 014E,
04VI, 04VK, 06YS (blueprint: lem-trf-point-pullback-cone-localization).

Proof (the eight DAG steps):
1. Exact additive sections respect dh+hd (lem-weil-point-proetale-sections-exact).
   For T use lem-trf-point-quotient-tower-homotopy to obtain compatible level
   homotopies and lem-pur-strict-roos-homotopy-functor to obtain the signed homotopy
   (b,a) -> (-hb,ha). Thus S and T factor through the good homotopy subcategory.
2. The comparison c_X is natural: after either roosFirst or roosSecond its naturality
   square is precisely Gamma(u_n) followed by the corresponding source projection.
   These two sets of product projections jointly determine every degree map.
3. Exact sections invert good quasi-isomorphisms. For T, clause (1) of
   lem-pur-integral-operations-well-defined makes the pullback Roos map a
   quasi-isomorphism; conjugate its section map by c to identify it with T(f).
4. The first clause of lem-weil-pbc-site-derived-tensor-descent makes the good
   homotopy quotient a localization: its fraction localization is equivalent to D(R).
   Use lem-weil-pbc-localization-universal-property after this equivalence.
5. Exact sections give sectionsFactors. The natural representative comparison of
   lem-pur-integral-operations-well-defined followed by c gives alpha on good P.
   For every resolution q the specified b_q is alpha_P followed contravariantly
   by completed pullback and sections of [q] inverse; at q=id it is alpha_P.
6. The natural-transformation localization property extends eta uniquely, satisfying
   alpha_P composed with the extended component = eta_P after sectionsFactors.
   Eta is arbitrary and need not be invertible.
7. Naturality at [q], followed by cancellation of its invertible images, gives the
   displayed formula for every N and q. It is independent of the resolution because
   it equals the same extended component. Conversely q=id gives the characterization
   in step 6, hence uniqueness.
8. Apply chain naturality to both roof legs and invert the denominator square:
   eta_P followed by T(a) inverse and T(b) equals S(a) inverse, S(b), eta_P'.
   The comparisons identify both fraction images with the derived functor images;
   thus equal derived roofs have equal S and T images. By
   lem-pc-quasi-isomorphisms-multiplicative-system and
   lem-pc-right-fraction-representation every derived morphism has an ambient roof.
   Resolve its middle complex using lem-pc-kflat-resolution and compose both legs.
   This gives a roof in the resolving class, without boundedness or completeness.
-/
theorem pointPullbackConeLocalization (_hl : l ≠ D.p) :
    ∃ (S T : (goodHomotopy D l E).FullSubcategory ⥤
        @DerivedCategory (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian _)),
      toHomotopy D l E ⋙ S = source D l E ∧
      toHomotopy D l E ⋙ T = target D l E ∧
      ((HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage
        (goodHomotopy D l E).ι).IsInvertedBy S ∧
      ((HomotopyCategory.quasiIso _ (.up ℤ)).inverseImage
        (goodHomotopy D l E).ι).IsInvertedBy T ∧
      ∃ hInv : ∀ (P P' : (integralOperationsGoodComplex l E
            (Spec (.of D.k))).FullSubcategory) (a : P ⟶ P'),
          QuasiIso a.hom → IsIso ((source D l E).map a) ∧ IsIso ((target D l E).map a),
        (∀ η : source D l E ⟶ target D l E,
          ∃! ηbar : pointFibreIntegralAmbient D l E ⟶
              integralDerivedPullback l E (frobeniusPointIso D).hom ⋙
                pointFibreIntegralAmbient D l E,
            ∀ (N : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
              (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
              (q : P.obj ⟶ N) [QuasiIso q],
              ηbar.app (DerivedCategory.Q.obj N) ≫
                  (representativeComparison D l E (frobeniusPointIso D).hom N P q).hom =
                (sectionsFactors D l E).hom.app N ≫
                  inv ((CompletedStalk.moduleQ l E).map
                    ((CompletedStalk.sectionsComplex D l E).map q)) ≫ η.app P) ∧
        (∀ (η : source D l E ⟶ target D l E)
          (P Q P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
          (a : Q ⟶ P) (b : Q ⟶ P') (ha : QuasiIso a.hom),
          η.app P ≫ inv (I := (hInv Q P a ha).2) ((target D l E).map a) ≫
              (target D l E).map b =
            inv (I := (hInv Q P a ha).1) ((source D l E).map a) ≫
              (source D l E).map b ≫ η.app P') ∧
        (∀ (P P' Q Q' : (integralOperationsGoodComplex l E
            (Spec (.of D.k))).FullSubcategory)
          (a : Q ⟶ P) (b : Q ⟶ P') (a' : Q' ⟶ P) (b' : Q' ⟶ P')
          (ha : QuasiIso a.hom) (ha' : QuasiIso a'.hom),
          inv (I := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a.hom).mpr ha)
              (DerivedCategory.Q.map a.hom) ≫
              DerivedCategory.Q.map b.hom =
            inv (I := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a'.hom).mpr ha')
                (DerivedCategory.Q.map a'.hom) ≫ DerivedCategory.Q.map b'.hom →
          (inv (I := (hInv Q P a ha).1) ((source D l E).map a) ≫
              (source D l E).map b =
            inv (I := (hInv Q' P a' ha').1) ((source D l E).map a') ≫
              (source D l E).map b') ∧
          (inv (I := (hInv Q P a ha).2) ((target D l E).map a) ≫
              (target D l E).map b =
            inv (I := (hInv Q' P a' ha').2) ((target D l E).map a') ≫
              (target D l E).map b')) ∧
        (∀ (P P' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
          (φ : DerivedCategory.Q.obj P.obj ⟶ DerivedCategory.Q.obj P'.obj),
          ∃ (Q : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
            (a : Q ⟶ P) (b : Q ⟶ P') (ha : QuasiIso a.hom),
            φ = inv (I := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a.hom).mpr ha)
              (DerivedCategory.Q.map a.hom) ≫ DerivedCategory.Q.map b.hom) := by
  let A := integralTowerModules l E (Spec (.of D.k))
  let L := integralOperationsGoodLocalization l E (Spec (.of D.k))
  let W := (HomologicalComplex.quasiIso A (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E (Spec (.of D.k))).ι
  let F := pointFibreIntegralAmbient D l E
  let G := integralDerivedPullback l E (frobeniusPointIso D).hom ⋙ F
  let e := sourceComparison D l E
  let d := targetComparison D l E
  let : L.IsLocalization W :=
    WeilConjectures.integralOperationsGoodLocalization_isLocalization l E _
  have hInv (P P' : (integralOperationsGoodComplex l E
      (Spec (.of D.k))).FullSubcategory) (a : P ⟶ P') (ha : QuasiIso a.hom) :
      IsIso ((source D l E).map a) ∧ IsIso ((target D l E).map a) := by
    have : IsIso (L.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ha
    exact ⟨comparison_inverts L F _ e a, comparison_inverts L G _ d a⟩
  refine ⟨homotopyFactor D l E F _ e, homotopyFactor D l E G _ d,
    homotopyFactor_fac D l E F _ e, homotopyFactor_fac D l E G _ d,
    homotopyFactor_inverts D l E F _ e, homotopyFactor_inverts D l E G _ d,
    hInv, ?_, ?_, ?_, ?_⟩
  · intro η
    let ff := Localization.fullyFaithfulWhiskeringLeft L W
      (@DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
        (HasDerivedCategory.ofIsGrothendieckAbelian _))
    let θ : L ⋙ F ⟶ L ⋙ G := e.hom ≫ η ≫ d.inv
    let ηbar : F ⟶ G := ff.preimage θ
    have hη (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory) :
        ηbar.app (DerivedCategory.Q.obj P.obj) ≫ (d.app P).hom =
          (sectionsFactors D l E).hom.app P.obj ≫ η.app P := by
      have ht := congrArg (fun t ↦ t.app P) (ff.map_preimage θ)
      change ηbar.app (L.obj P) = θ.app P at ht
      have ht' : ηbar.app (DerivedCategory.Q.obj P.obj) = θ.app P := ht
      exact (congrArg (· ≫ (d.app P).hom) ht').trans (by
        simp only [θ, NatTrans.comp_app, Iso.app_hom, Category.assoc,
          Iso.inv_hom_id_app, Category.comp_id]
        simp only [e, sourceComparison, Functor.isoWhiskerLeft_hom,
          Functor.whiskerLeft_app]
        rfl)
    have hformula (N : CochainComplex A ℤ)
        (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
        (q : P.obj ⟶ N) [QuasiIso q] :
        ηbar.app (DerivedCategory.Q.obj N) ≫
            (representativeComparison D l E (frobeniusPointIso D).hom N P q).hom =
          (sectionsFactors D l E).hom.app N ≫
            inv ((CompletedStalk.moduleQ l E).map
              ((CompletedStalk.sectionsComplex D l E).map q)) ≫ η.app P := by
      have hq : IsIso (DerivedCategory.Q.map q) := inferInstance
      have hs : IsIso ((CompletedStalk.moduleQ l E).map
          ((CompletedStalk.sectionsComplex D l E).map q)) := inferInstance
      rw [representativeComparison_eq D l E N P q]
      change ηbar.app (DerivedCategory.Q.obj N) ≫ G.map (inv (DerivedCategory.Q.map q)) ≫
        (d.app P).hom = _
      exact resolution_formula F G ηbar (DerivedCategory.Q.map q)
        ((sectionsFactors D l E).app P.obj) ((sectionsFactors D l E).app N)
        (d.app P) ((CompletedStalk.moduleQ l E).map
          ((CompletedStalk.sectionsComplex D l E).map q)) (η.app P)
        ((sectionsFactors D l E).hom.naturality q) (hη P)
    refine ⟨ηbar, hformula, ?_⟩
    intro τ hτ
    apply Localization.natTrans_ext L W
    intro P
    apply (cancel_mono (d.app P).hom).1
    change τ.app (DerivedCategory.Q.obj P.obj) ≫ (d.app P).hom =
      ηbar.app (DerivedCategory.Q.obj P.obj) ≫ (d.app P).hom
    exact Eq.trans (by
      have ht := hτ P.obj P (𝟙 P.obj)
      rw [representativeComparison_eq D l E P.obj P (𝟙 P.obj)] at ht
      exact normalize_identity_formula DerivedCategory.Q
        (CompletedStalk.sectionsComplex D l E ⋙ CompletedStalk.moduleQ l E)
        F G τ P.obj (d.app P) ((sectionsFactors D l E).app P.obj) (η.app P) ht)
      (hη P).symm
  · intro η P Q P' a b ha
    let := (hInv Q P a ha).1
    let := (hInv Q P a ha).2
    apply (cancel_epi ((source D l E).map a)).1
    rw [← Category.assoc, η.naturality a]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact (η.naturality b).symm
  · intro P P' Q Q' a b a' b' ha ha' h
    let := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a.hom).2 ha
    let := (DerivedCategory.isIso_Q_map_iff_quasiIso _ a'.hom).2 ha'
    have : IsIso (L.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ha
    have : IsIso (L.map a') := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ha'
    let := (hInv Q P a ha).1
    let := (hInv Q P a ha).2
    let := (hInv Q' P a' ha').1
    let := (hInv Q' P a' ha').2
    constructor
    · rw [comparison_roof L F _ e a b, comparison_roof L F _ e a' b']
      exact congrArg (fun t ↦ (e.app P).inv ≫ F.map t ≫ (e.app P').hom) h
    · rw [comparison_roof L G _ d a b, comparison_roof L G _ d a' b']
      exact congrArg (fun t ↦ (d.app P).inv ≫ G.map t ≫ (d.app P').hom) h
  · intro P P' φ
    obtain ⟨K, a, ha, b, hφ⟩ := DerivedCategory.right_fac φ
    have hqa : QuasiIso a := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 ha
    obtain ⟨R, r, hk, hf, hr, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) K
    let := hr
    let := hqa
    let R' : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory :=
      ⟨R, hk, fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (R.X i)).symm (hf i)⟩
    refine ⟨R', ObjectProperty.homMk (r ≫ a), ObjectProperty.homMk (r ≫ b),
      (show QuasiIso (r ≫ a) from inferInstance), ?_⟩
    rw [hφ]
    have : QuasiIso (r ≫ a) := inferInstance
    exact refine_roof DerivedCategory.Q r a b

end WeilConjectures.PointPullbackCone
