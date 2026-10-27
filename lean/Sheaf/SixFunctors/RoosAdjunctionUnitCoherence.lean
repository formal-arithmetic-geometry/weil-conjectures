module

public import Sheaf.SixFunctors.OpenTensorNormalizationData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence
import Sheaf.CategoryTheory.StrictRoosDerivation

/-! # Adjunction units and normalized signed Roos comparisons

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Tags 09BN and 09BP;
blueprint prop-sf-pf-coherence, open-factor base-change paragraph
(blueprint: lem-sf-roos-adjunction-unit-coherence).

The record below bundles the specified comparisons together with their equations.
Its fields are conclusions, not extra assumptions of the theorem. The underlying Roos
functor is the existing shifted cone. The signed coordinates put the unshifted product
first, with differential (dx,(1-s)x-dy). The same normalized theta is used for both
functors; every augmentation is an actual chain map with zero second coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uA vA uB vB wA wB uC vC r uD vD s

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RoosAdjunctionUnit

/-- Localize the specified degreewise adjunction using the standard exact-functor
factorizations. Both units and counits are the localized original maps.
Source: Stacks Project, Tag 015F (blueprint: lem-sf-roos-adjunction-unit-coherence).
This helper extends the recorded construction to independent universes; its common-universe
specialization is identified by `exactDerivedAdjunctionUniverses_commonUniverses`. -/
def exactDerivedAdjunctionUniverses
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

/-- The common-universe specialization is definitionally the landed adjunction.
This reflexivity witness identifies the helper with the dependency's existing construction;
it introduces neither a second adjunction choice nor a postponed theorem.
Source: Stacks 015F and the localized unit in the open-factor calculation
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev exactDerivedAdjunctionUniverses_commonUniverses
    {A B : Type uA} [Category.{vA} A] [Category.{vA} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    exactDerivedAdjunctionUniverses a =
      SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a := rfl

section Helpers
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]

/-- Transparent termwise application on strict tower complexes.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerComplex (F : A ⥤ B) [F.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)

/-- The standard exact localization of termwise application on strict towers.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerDerived [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The standard localization factorization for termwise tower application.
Source: Stacks 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
abbrev towerFactors [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :=
  @Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) inferInstance
    (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)

/-- The specified exact derived adjunction on strict towers.
Source: Stacks 015F, 0941 (blueprint: lem-sf-roos-adjunction-unit-coherence). -/
def towerAdjunction [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    towerDerived F ⊣ towerDerived G :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B A).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exactDerivedAdjunctionUniverses (a.whiskerRight ℕᵒᵖ)

/-- Signed coordinates (x,y)=(u,-v) on the existing shifted Roos cone.
Source: Stacks 0941; the signed normalization of exactProductFunctorStrictLimit
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
def coordinates [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosF.obj X).X (p + 1) ≅ (roosP X).X (p + 1) ⊞ (roosP X).X p :=
  roosχ X p ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso (Iso.refl _) {
      hom := -𝟙 _
      inv := -𝟙 _
      hom_inv_id := by simp
      inv_hom_id := by simp }

end Helpers

section Statement
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasLimits A] [HasLimits B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
  (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
  (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
  (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
    DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
  (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
    DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)

/-- The comparisons and all conclusions of the adjunction-unit calculation, in one
record. In particular, kappa is specified on both signed product coordinates; theta
is natural and has the ordinary-limit inclusion normalization on K-injectives; lambda
is exactly its conjugate of kappa. No cone filler or arbitrary comparison is an input.
Source: Stacks 0941, 09BN, 09BP and the open-factor calculation in prop-sf-pf-coherence
(blueprint: lem-sf-roos-adjunction-unit-coherence). -/
structure Coherence where
  thetaA : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q
  thetaB : DerivedCategory.Q ⋙ LB ≅ roosF ⋙ DerivedCategory.Q
  normalizationA : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
    (∀ p : ℤ, Injective (I.X p)) →
    etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.map (roosι I)
  normalizationB : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective],
    (∀ p : ℤ, Injective (I.X p)) →
    etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.map (roosι I)
  kappaF : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF
  kappaG : roosF ⋙ G.mapHomologicalComplex (.up ℤ) ≅ towerComplex G ⋙ roosF
  kappaF_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ),
    (kappaF.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex F).obj X) p).hom =
      F.map (coordinates X p).hom ≫
        F.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (F.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  kappaG_coordinates : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ),
    (kappaG.hom.app X).f (p + 1) ≫ (coordinates ((towerComplex G).obj X) p).hom =
      G.map (coordinates X p).hom ≫
        G.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map
          ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f (p + 1))
          ((piComparison (G.mapHomologicalComplex (.up ℤ))
            (fun n : ℕ ↦ X.asFunctor.obj (op n))).f p)
  lambdaF : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB
  lambdaG : LB ⋙ G.mapDerivedCategory ≅ towerDerived G ⋙ LA
  lambdaF_normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    F.mapDerivedCategory.map (thetaA.hom.app X) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappaF.hom.app X) =
      lambdaF.hom.app (DerivedCategory.Q.obj X) ≫
        LB.map ((towerFactors F).hom.app X) ≫ thetaB.hom.app ((towerComplex F).obj X)
  lambdaG_normalization : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
    G.mapDerivedCategory.map (thetaB.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map (kappaG.hom.app X) =
      lambdaG.hom.app (DerivedCategory.Q.obj X) ≫
        LA.map ((towerFactors G).hom.app X) ≫ thetaA.hom.app ((towerComplex G).obj X)
  product_unit : ∀ M : ℕ → A,
    a.unit.app (∏ᶜ M) ≫ G.map (piComparison F M) ≫
        piComparison G (fun n : ℕ ↦ F.obj (M n)) =
      Limits.Pi.map (fun n : ℕ ↦ a.unit.app (M n))
  chain_unit : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
        kappaG.hom.app ((towerComplex F).obj X) =
      roosF.map (((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X)
  towerUnit : 𝟭 (DerivedCategory.{wA} (ℕᵒᵖ ⥤ A)) ≅ towerDerived F ⋙ towerDerived G
  towerUnit_hom : towerUnit.hom = (towerAdjunction a).unit
  derived_unit : ∀ M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A),
    (exactDerivedAdjunctionUniverses a).unit.app (LA.obj M) ≫
        G.mapDerivedCategory.map (lambdaF.hom.app M) ≫
        lambdaG.hom.app ((towerDerived F).obj M) ≫ LA.map (towerUnit.inv.app M) =
      𝟙 (LA.obj M)
  augmentation : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (P : CochainComplex A ℤ)
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n)),
    (∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) →
    ∃ (b : P ⟶ roosF.obj X)
      (bGF : (G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
        roosF.obj ((towerComplex G).obj ((towerComplex F).obj X))),
      (∀ p : ℤ, b.f (p + 1) ≫ (coordinates X p).hom =
        biprod.lift ((Pi.lift gamma).f (p + 1)) 0) ∧
      (∀ p : ℤ, bGF.f (p + 1) ≫
        (coordinates ((towerComplex G).obj ((towerComplex F).obj X)) p).hom =
        biprod.lift ((Pi.lift (fun n : ℕ ↦
          (G.mapHomologicalComplex (.up ℤ)).map
            ((F.mapHomologicalComplex (.up ℤ)).map (gamma n)))).f (p + 1)) 0) ∧
      b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
          kappaG.hom.app ((towerComplex F).obj X) =
        (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫ bGF ∧
      (∀ p : ℤ,
        (b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (kappaF.hom.app X) ≫
          kappaG.hom.app ((towerComplex F).obj X)).f (p + 1) ≫
            (coordinates ((towerComplex G).obj ((towerComplex F).obj X)) p).hom =
        biprod.lift ((Pi.lift (fun n : ℕ ↦ gamma n ≫
          (a.mapHomologicalComplex (.up ℤ)).unit.app (X.asFunctor.obj (op n)))).f (p + 1)) 0) ∧
      (exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategory.map
            (DerivedCategory.Q.map b ≫ thetaA.inv.app X)) ≫
          G.mapDerivedCategory.map (lambdaF.hom.app (DerivedCategory.Q.obj X)) ≫
          lambdaG.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
          LA.map (towerUnit.inv.app (DerivedCategory.Q.obj X)) =
        DerivedCategory.Q.map b ≫ thetaA.inv.app X

end Statement

section ProofHelpers
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

omit [Abelian A] [Abelian B] in
private theorem preservesProducts (F : A ⥤ B)
    (h : ∀ M : ℕ → A, IsIso (piComparison F M)) :
    PreservesLimitsOfShape (Discrete ℕ) F where
  preservesLimit {K} := by
    have := h (fun n ↦ K.obj ⟨n⟩)
    have : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
      PreservesProduct.of_iso_comparison F (K.obj ∘ Discrete.mk)
    exact preservesLimit_of_iso_diagram F Discrete.natIsoFunctor.symm

private def canonicalKappa (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF :=
  NatIso.ofComponents (fun X ↦ by
    have := roosAdditiveComparison_isIso F X
    exact (asIso (roosAdditiveComparison F X) :
      (roosF ⋙ F.mapHomologicalComplex (.up ℤ)).obj X ≅
        (towerComplex F ⋙ roosF).obj X))
    (fun f ↦ by
      simpa only [Functor.comp_map, asIso_hom, roosTowerAction] using
        roosAdditiveComparison_natural F f)

omit [HasCountableProducts A] in
private theorem signedLift {V P Q : A} (f : V ⟶ Q) :
    biprod.lift (0 : V ⟶ P) f ≫ (biprod.braiding _ _).hom ≫
      biprod.map (𝟙 _) (-𝟙 _) = biprod.lift f 0 := by
  apply biprod.hom_ext <;> simp [Category.assoc]

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem signedComparison (F : A ⥤ B) [F.Additive]
    {V P Q : A} {P' Q' : B} (c : V ⟶ P ⊞ Q)
    (f : F.obj P ⟶ P') (g : F.obj Q ⟶ Q') :
    (F.map c ≫ F.biprodComparison P Q ≫ biprod.map f g) ≫
        (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _) =
      F.map (c ≫ (biprod.braiding _ _).hom ≫ biprod.map (𝟙 _) (-𝟙 _)) ≫
        F.biprodComparison Q P ≫ biprod.map g f := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      biprod.braiding_hom, biprod.lift_fst, biprod.map_snd,
      Functor.biprodComparison_fst_assoc, Functor.biprodComparison_snd_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc]
    simp
  · simp only [Category.assoc, biprod.map_snd, Preadditive.comp_neg,
      Category.comp_id, biprod.braiding_hom, biprod.lift_snd, biprod.map_fst,
      Functor.biprodComparison_fst_assoc, Functor.biprodComparison_snd_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp_assoc]
    simp

private theorem kappa_coordinates (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    ((canonicalKappa F).hom.app X).f (p + 1) ≫
        (coordinates ((towerComplex F).obj X) p).hom =
      F.map (coordinates X p).hom ≫
        F.biprodComparison ((roosP X).X (p + 1)) ((roosP X).X p) ≫
        biprod.map ((roosProductComparison F X).f (p + 1))
          ((roosProductComparison F X).f p) := by
  change (roosAdditiveComparison F X).f (p + 1) ≫ _ = _
  dsimp only [coordinates, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, ← Category.assoc]
  erw [roosAdditiveComparison_coordinates]
  simpa only [Category.assoc, towerComplex, roosTowerAction] using
    signedComparison F (roosχ X p).hom
      ((roosProductComparison F X).f p) ((roosProductComparison F X).f (p + 1))

private theorem chainUnit {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    (a : F ⊣ G) [IsIso a.unit]
    [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
        (G.mapHomologicalComplex (.up ℤ)).map ((canonicalKappa F).hom.app X) ≫
        (canonicalKappa G).hom.app ((towerComplex F).obj X) =
      roosF.map (((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X) := by
  let u := ((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X
  let v := (NatTrans.mapHomologicalComplex
    ((Functor.whiskeringRight ℕᵒᵖ A A).map (asIso a.unit).inv) (.up ℤ)).app X
  have hvu : v ≫ u = 𝟙 _ := by
    ext i n
    simp [u, v, Adjunction.whiskerRight_unit_app_app]
  have h := roosComparison_horizontal_coherence F G (𝟭 A) (asIso a.unit).inv X
  rw [roosAdditiveComparison_id] at h
  change (G.mapHomologicalComplex (.up ℤ)).map (roosAdditiveComparison F X) ≫
    roosAdditiveComparison G ((towerComplex F).obj X) ≫ roosF.map v =
    (NatTrans.mapHomologicalComplex (asIso a.unit).inv (.up ℤ)).app
      (roosF.obj X) ≫ (𝟙 _ ≫ roosF.map (𝟙 X)) at h
  have hh := congrArg (fun z ↦
    (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫ z ≫ roosF.map u) h
  have hc : (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
      (NatTrans.mapHomologicalComplex (asIso a.unit).inv (.up ℤ)).app (roosF.obj X) =
      𝟙 _ := by
    ext i
    change a.unit.app _ ≫ (asIso a.unit).inv.app _ = 𝟙 _
    exact (asIso a.unit).hom_inv_id_app _
  simp only [Category.assoc] at hh
  rw [← roosF.map_comp v u, hvu, roosF.map_id] at hh
  simp only [← Category.assoc, hc, roosF.map_id] at hh
  erw [Category.comp_id] at hh
  simpa only [canonicalKappa, NatIso.ofComponents_hom_app, asIso_hom, towerComplex,
    u, Functor.comp_obj, Functor.id_obj, Category.assoc,
    Category.comp_id, Category.id_comp] using hh


private theorem normalizedTheta [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
    (L : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (eta : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L)
    (hL : L.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso _ (.up ℤ)))
    (T : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (e : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ T)
    (hT : T.IsRightDerivedFunctor (roosDerivedUnit e)
      (HomologicalComplex.quasiIso _ (.up ℤ))) :
    ∃ theta : DerivedCategory.Q ⋙ L ≅ roosF ⋙ DerivedCategory.Q,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        eta.app X ≫ theta.hom.app X = DerivedCategory.Q.map (roosι X) := by
  let := hL
  let := hT
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  let rho : T ≅ L := T.rightDerivedUnique L (roosDerivedUnit e) eta W
  let theta := e ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q rho
  have hu X : DerivedCategory.Q.map (roosι X) ≫ theta.hom.app X = eta.app X := by
    have h := T.rightDerivedNatTrans_app L (roosDerivedUnit e) eta W (𝟙 _) X
    simpa [theta, rho, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      roosDerivedUnit, roosInclusion, roosLimitFunctor,
      Functor.rightDerivedNatTrans, Category.assoc] using h
  refine ⟨theta.symm, fun X ↦ ?_⟩
  change eta.app X ≫ theta.inv.app X = _
  rw [← hu X, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem descendComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (thetaA : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q)
    (thetaB : DerivedCategory.Q ⋙ LB ≅ roosF ⋙ DerivedCategory.Q)
    (kappa : roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ towerComplex F ⋙ roosF) :
    ∃ lambda : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        F.mapDerivedCategory.map (thetaA.hom.app X) ≫
            F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
            DerivedCategory.Q.map (kappa.hom.app X) =
          lambda.hom.app (DerivedCategory.Q.obj X) ≫
            LB.map ((towerFactors F).hom.app X) ≫
            thetaB.hom.app ((towerComplex F).obj X) := by
  let e₁ : DerivedCategory.Q ⋙ (LA ⋙ F.mapDerivedCategory) ≅
      roosF ⋙ (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight thetaA F.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft roosF F.mapDerivedCategoryFactors
  let e₂ : DerivedCategory.Q ⋙ (towerDerived F ⋙ LB) ≅
      towerComplex F ⋙ (roosF ⋙ DerivedCategory.Q) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (towerFactors F) LB ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (towerComplex F) thetaB
  let e := e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight kappa DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫ e₂.symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (DerivedCategory.{wB} B)
  let lambda := ff.preimageIso e
  have hl X : lambda.hom.app (DerivedCategory.Q.obj X) = e.hom.app X :=
    congr_app (ff.map_preimage e.hom) X
  refine ⟨lambda, fun X ↦ ?_⟩
  rw [hl X]
  have hh : e₁.hom.app X ≫ DerivedCategory.Q.map (kappa.hom.app X) =
      e.hom.app X ≫ e₂.hom.app X := by simp [e, Category.assoc]
  simpa only [e₁, e₂, Iso.trans_hom, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.map_id] using hh

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem localizedUnit
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (X : CochainComplex A ℤ) :
    (exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app X) := by
  dsimp only [exactDerivedAdjunctionUniverses]
  rw [Adjunction.localization_unit_app]
  dsimp only [CatCommSq.iso, Iso.symm_hom, Functor.comp_obj]
  simp only [Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [Functor.map_id]
  simp only [Category.id_comp]
  erw [Iso.inv_hom_id_app, Category.comp_id]

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem localizedUnitIso
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) [IsIso a.unit] :
    IsIso (exactDerivedAdjunctionUniverses a).unit := by
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory.{wA} A)
  have hi (X : CochainComplex A ℤ) :
      IsIso ((exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj X)) := by
    have : IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app X) := by
      have : ∀ i, IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app X).f i) :=
        fun i ↦ inferInstanceAs (IsIso (a.unit.app (X.X i)))
      exact HomologicalComplex.Hom.isIso_of_components _
    have h := localizedUnit a X
    have : IsIso ((exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj X) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X))
  have : IsIso (Functor.whiskerLeft DerivedCategory.Q
      (exactDerivedAdjunctionUniverses a).unit) := by
    have : ∀ X, IsIso ((Functor.whiskerLeft DerivedCategory.Q
      (exactDerivedAdjunctionUniverses a).unit).app X) := hi
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).map
      (exactDerivedAdjunctionUniverses a).unit) := by
    change IsIso (Functor.whiskerLeft DerivedCategory.Q
      (exactDerivedAdjunctionUniverses a).unit)
    infer_instance
  exact ff.isIso_of_isIso_map (exactDerivedAdjunctionUniverses a).unit

private theorem augmentationMapped (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n)
    (hgammaF : ∀ n,
      (F.mapHomologicalComplex (.up ℤ)).map (gamma (n + 1)) ≫
        ((towerComplex F).obj X).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      (F.mapHomologicalComplex (.up ℤ)).map (gamma n)) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosAugment gamma hgamma) ≫
        (canonicalKappa F).hom.app X =
      roosAugment (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n)) hgammaF := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective i
  apply (cancel_mono (roosχ ((towerComplex F).obj X) p).hom).mp
  change _ = (roosAugment _ hgammaF).f (p + 1) ≫ _
  rw [roosAugment_χ]
  exact roosAdditiveComparison_augmentation F X P gamma hgamma p

private theorem augmentationSigned {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {P : CochainComplex A ℤ} (gamma : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hgamma : ∀ n, gamma (n + 1) ≫
      X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n) (p : ℤ) :
    (roosAugment gamma hgamma).f (p + 1) ≫ (coordinates X p).hom =
      biprod.lift ((Pi.lift gamma).f (p + 1)) 0 := by
  dsimp only [coordinates, Iso.trans_hom, biprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, ← Category.assoc, roosAugment_χ]
  simpa only [Category.assoc] using
    signedLift (A := A) (P := (roosP X).X p) ((Pi.lift gamma).f (p + 1))

end ProofHelpers

private theorem conjugateUnit {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (G : B ⥤ A) (u : 𝟭 A ⟶ F ⋙ G)
    {P₀ H₀ P₂ H₂ : A} {P₁ H₁ : B}
    (t₀ : P₀ ⟶ H₀) (t₁ : P₁ ⟶ H₁) (t₂ : P₂ ⟶ H₂)
    (l₁ : F.obj P₀ ⟶ P₁) (l₂ : G.obj P₁ ⟶ P₂)
    (k₁ : F.obj H₀ ⟶ H₁) (k₂ : G.obj H₁ ⟶ H₂)
    (h₁ : F.map t₀ ≫ k₁ = l₁ ≫ t₁)
    (h₂ : G.map t₁ ≫ k₂ = l₂ ≫ t₂) :
    u.app P₀ ≫ G.map l₁ ≫ l₂ ≫ t₂ =
      t₀ ≫ u.app H₀ ≫ G.map k₁ ≫ k₂ := by
  rw [← h₂, ← G.map_comp_assoc, ← h₁, G.map_comp]
  have h := u.naturality t₀
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc]


section DerivedCalculation
variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]

private theorem derivedUnitCalculation (a : F ⊣ G) [IsIso a.unit]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (thetaA : DerivedCategory.Q ⋙ LA ≅ roosF ⋙ DerivedCategory.Q)
    (thetaB : DerivedCategory.Q ⋙ LB ≅ roosF ⋙ DerivedCategory.Q)
    (lambdaF : LA ⋙ F.mapDerivedCategory ≅ towerDerived F ⋙ LB)
    (lambdaG : LB ⋙ G.mapDerivedCategory ≅ towerDerived G ⋙ LA)
    (hF : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      F.mapDerivedCategory.map (thetaA.hom.app X) ≫
          F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
          DerivedCategory.Q.map ((canonicalKappa F).hom.app X) =
        lambdaF.hom.app (DerivedCategory.Q.obj X) ≫
          LB.map ((towerFactors F).hom.app X) ≫ thetaB.hom.app ((towerComplex F).obj X))
    (hG : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      G.mapDerivedCategory.map (thetaB.hom.app X) ≫
          G.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
          DerivedCategory.Q.map ((canonicalKappa G).hom.app X) =
        lambdaG.hom.app (DerivedCategory.Q.obj X) ≫
          LA.map ((towerFactors G).hom.app X) ≫ thetaA.hom.app ((towerComplex G).obj X))
    (M : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A)) :
    (exactDerivedAdjunctionUniverses a).unit.app (LA.obj M) ≫
        G.mapDerivedCategory.map (lambdaF.hom.app M) ≫
        lambdaG.hom.app ((towerDerived F).obj M) =
      LA.map ((towerAdjunction a).unit.app M) := by
  let FD := F.mapDerivedCategory
  let GD := G.mapDerivedCategory
  let TF := towerDerived F
  let TG := towerDerived G
  let u := (exactDerivedAdjunctionUniverses a).unit
  let ut := (towerAdjunction a).unit
  let mu : LA ⟶ TF ⋙ TG ⋙ LA :=
    (Functor.rightUnitor LA).inv ≫ Functor.whiskerLeft LA u ≫
      (Functor.associator LA FD GD).inv ≫ Functor.whiskerRight lambdaF.hom GD ≫
      (Functor.associator TF LB GD).hom ≫ Functor.whiskerLeft TF lambdaG.hom
  let nu : LA ⟶ TF ⋙ TG ⋙ LA :=
    (Functor.leftUnitor LA).inv ≫ Functor.whiskerRight ut LA ≫
      (Functor.associator TF TG LA).hom
  have heq : mu = nu := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    intro X
    let Y := (towerComplex F).obj X
    let Z := (towerComplex G).obj Y
    let v := ((a.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app X
    let fF := (towerFactors F).hom.app X
    let fG := (towerFactors G).hom.app Y
    have hc := conjugateUnit FD GD u (thetaA.hom.app X) (thetaB.hom.app Y)
      (thetaA.hom.app Z)
      (lambdaF.hom.app (DerivedCategory.Q.obj X) ≫ LB.map fF)
      (lambdaG.hom.app (DerivedCategory.Q.obj Y) ≫ LA.map fG)
      (F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
        DerivedCategory.Q.map ((canonicalKappa F).hom.app X))
      (G.mapDerivedCategoryFactors.hom.app (roosF.obj Y) ≫
        DerivedCategory.Q.map ((canonicalKappa G).hom.app Y))
      (by simpa only [Category.assoc] using hF X)
      (by simpa only [Category.assoc] using hG Y)
    have hchain : u.app (DerivedCategory.Q.obj (roosF.obj X)) ≫
        GD.map (F.mapDerivedCategoryFactors.hom.app (roosF.obj X) ≫
          DerivedCategory.Q.map ((canonicalKappa F).hom.app X)) ≫
        G.mapDerivedCategoryFactors.hom.app (roosF.obj Y) ≫
        DerivedCategory.Q.map ((canonicalKappa G).hom.app Y) =
        DerivedCategory.Q.map (roosF.map v) := by
      dsimp only [GD]
      rw [Functor.map_comp]
      have hn := G.mapDerivedCategoryFactors.hom.naturality
        ((canonicalKappa F).hom.app X)
      dsimp only [Functor.comp_map] at hn
      simp only [Category.assoc]
      dsimp only [Y, Functor.comp_obj] at hn ⊢
      rw [reassoc_of% hn]
      have hu := localizedUnit a (roosF.obj X)
      change u.app _ ≫ G.mapDerivedCategory.map _ ≫
        G.mapDerivedCategoryFactors.hom.app _ = _ at hu
      rw [reassoc_of% hu]
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg DerivedCategory.Q.map (chainUnit a X)
    have hn := lambdaG.hom.naturality fF
    dsimp only [Functor.comp_map] at hn
    simp only [Functor.map_comp, Category.assoc] at hc
    dsimp only [GD, Y, Functor.comp_obj] at hc hn
    rw [reassoc_of% hn] at hc
    have hc' :
        (u.app (LA.obj (DerivedCategory.Q.obj X)) ≫
          GD.map (lambdaF.hom.app (DerivedCategory.Q.obj X)) ≫
          lambdaG.hom.app (TF.obj (DerivedCategory.Q.obj X))) ≫
          LA.map (TG.map fF ≫ fG) ≫ thetaA.hom.app Z =
        thetaA.hom.app X ≫ DerivedCategory.Q.map (roosF.map v) := by
      dsimp only [GD, Y] at hchain
      simp only [Functor.map_comp, Category.assoc] at hchain
      rw [hchain] at hc
      dsimp only [GD, TF, TG]
      rw [LA.map_comp]
      simpa only [Category.assoc] using hc
    have ht : ut.app (DerivedCategory.Q.obj X) ≫ TG.map fF ≫ fG =
        DerivedCategory.Q.map v := by
      have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      exact localizedUnit (a.whiskerRight ℕᵒᵖ) X
    have htheta := thetaA.hom.naturality v
    dsimp only [Functor.comp_map] at htheta
    have hi : IsIso (LA.map (TG.map fF ≫ fG) ≫ thetaA.hom.app Z) := by
      dsimp only [fF, fG]
      infer_instance
    apply (cancel_mono (LA.map (TG.map fF ≫ fG) ≫ thetaA.hom.app Z)).mp
    change mu.app (DerivedCategory.Q.obj X) ≫ _ =
      nu.app (DerivedCategory.Q.obj X) ≫ _
    dsimp only [mu, nu, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj]
    simp only [FD, GD, TF, TG, Functor.id_obj,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [← LA.map_comp_assoc]
    change _ = LA.map (ut.app (DerivedCategory.Q.obj X) ≫ TG.map fF ≫ fG) ≫ _
    rw [ht]
    simpa only [FD, GD, TF, TG, Functor.id_obj, Functor.comp_obj, Category.assoc] using
      hc'.trans htheta.symm
  have h := congr_app heq M
  dsimp only [mu, nu, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj] at h
  simpa only [FD, GD, TF, TG, Functor.comp_obj, Functor.id_obj, Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc] using h

end DerivedCalculation

/-- Adjunction units commute with the canonical product and signed Roos comparisons,
and with their normalized total-derived-limit comparison, including every strict
augmentation. All comparisons and their characterizing equations are conclusions
bundled by `Coherence`.

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Tags 09BN and 09BP;
prop-sf-pf-coherence, open-factor base-change paragraph
(blueprint: lem-sf-roos-adjunction-unit-coherence).

Proof plan:
1. On each product projection, the composite comparison followed by that projection
   is GF(pr_n) followed after the unit, hence u_(M_n) pr_n by naturality. Product
   uniqueness proves product_unit. This applies in each complex degree.
2. Use lem-weil-strict-roos-comparison and
   lem-cbc-exact-product-functor-strict-limit with their signed coordinates. On each
   coordinate followed by each product projection, the composite is GF(r_i,n) u.
   Unit naturality identifies this with u r_i,n. Product and biproduct uniqueness
   give chain_unit, with the same positive comparison on both signed summands.
3. Take the normalized natural Roos comparisons thetaA, thetaB and conjugate the
   two canonical kappa maps as in lem-cbc-exact-product-functor-strict-limit. Substitute
   into the composite lambda, cancel the middle theta, and use naturality of the
   localized unit from def-weil-exact-derived-adjunction. Step 2 and naturality of
   thetaA identify the result with LA(u_M). Composing with LA(u_M inverse) gives
   derived_unit. All equalities are natural on the actual derived categories.
4. For gamma, the normalized augmentation of lem-weil-strict-roos-comparison is
   (gamma,0). Step 2 gives (u gamma,0), which equals GF(gamma) u_P by naturality.
   The same theta transports this equality to the actual augmented derived map.
   Composing the coordinate units with their inverses gives identity on each
   product projection and both signed summands, including the augmentation. -/
theorem roosAdjunctionUnitCoherence
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max uD vD s}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (S : Sheaf K RingCat.{max uD vD s})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S)]
    (F : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uD vD s} S)
    (G : ringedSiteModules.{max uD vD s} S ⥤ ringedSiteModules.{max uC vC r} R)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) [IsIso a.unit]
    (_hphiF : ∀ M : ℕ → ringedSiteModules.{max uC vC r} R, IsIso (piComparison F M))
    (_hphiG : ∀ M : ℕ → ringedSiteModules.{max uD vD s} S, IsIso (piComparison G M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ⥤
      DerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ lim ⋙
      DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) (.up ℤ))) :
    Nonempty (Coherence F G a LA LB etaA etaB) := by
  classical
  have := preservesProducts F _hphiF
  have := preservesProducts G _hphiG
  obtain ⟨TA, eA, hTA, _⟩ := strictRoosDerivation.{uC, vC, r, wA} J R _hR
  obtain ⟨TB, eB, hTB, _⟩ := strictRoosDerivation.{uD, vD, s, wB} K S _hS
  obtain ⟨thetaA, hthetaA⟩ := normalizedTheta LA etaA _hLA TA eA hTA
  obtain ⟨thetaB, hthetaB⟩ := normalizedTheta LB etaB _hLB TB eB hTB
  obtain ⟨lambdaF, hlambdaF⟩ := descendComparison F LA LB thetaA thetaB (canonicalKappa F)
  obtain ⟨lambdaG, hlambdaG⟩ := descendComparison G LB LA thetaB thetaA (canonicalKappa G)
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : ∀ X, IsIso ((a.whiskerRight ℕᵒᵖ).unit.app X) := by
    intro X
    have : ∀ n, IsIso (((a.whiskerRight ℕᵒᵖ).unit.app X).app n) := by
      intro n
      simpa only [Adjunction.whiskerRight_unit_app_app] using
        (inferInstanceAs (IsIso (a.unit.app (X.obj n))))
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (a.whiskerRight ℕᵒᵖ).unit := NatIso.isIso_of_isIso_app _
  have : IsIso (towerAdjunction a).unit := by
    change IsIso (exactDerivedAdjunctionUniverses (a.whiskerRight ℕᵒᵖ)).unit
    exact localizedUnitIso (a.whiskerRight ℕᵒᵖ)
  let tunit : 𝟭 _ ≅ towerDerived F ⋙ towerDerived G :=
    asIso (towerAdjunction a).unit
  have hcancel (M : DerivedCategory.{wA}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)) :
      (exactDerivedAdjunctionUniverses a).unit.app (LA.obj M) ≫
          G.mapDerivedCategory.map (lambdaF.hom.app M) ≫
          lambdaG.hom.app ((towerDerived F).obj M) ≫ LA.map (tunit.inv.app M) =
        𝟙 (LA.obj M) := by
    rw [reassoc_of% (derivedUnitCalculation a LA LB thetaA thetaB lambdaF lambdaG
      hlambdaF hlambdaG M)]
    change LA.map (tunit.hom.app M) ≫ LA.map (tunit.inv.app M) = _
    rw [← LA.map_comp, Iso.hom_inv_id_app, LA.map_id]
    rfl
  refine ⟨{
    thetaA := thetaA
    thetaB := thetaB
    normalizationA := fun I _ _ ↦ hthetaA I
    normalizationB := fun I _ _ ↦ hthetaB I
    kappaF := canonicalKappa F
    kappaG := canonicalKappa G
    kappaF_coordinates := kappa_coordinates F
    kappaG_coordinates := kappa_coordinates G
    lambdaF := lambdaF
    lambdaG := lambdaG
    lambdaF_normalization := hlambdaF
    lambdaG_normalization := hlambdaG
    product_unit := ?_
    chain_unit := chainUnit a
    towerUnit := tunit
    towerUnit_hom := rfl
    derived_unit := hcancel
    augmentation := ?_ }⟩
  · intro M
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π]
    rw [← G.map_comp, piComparison_comp_π]
    erw [Pi.map_π]
    exact (a.unit.naturality (Pi.π M n)).symm
  · intro X P gamma hgamma
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let Gc := G.mapHomologicalComplex (.up ℤ)
    let Y := (towerComplex F).obj X
    let Z := (towerComplex G).obj Y
    let gammaF : ∀ n : ℕ, Fc.obj P ⟶ Y.asFunctor.obj (op n) :=
      fun n ↦ Fc.map (gamma n)
    let gammaGF : ∀ n : ℕ, Gc.obj (Fc.obj P) ⟶ Z.asFunctor.obj (op n) :=
      fun n ↦ Gc.map (gammaF n)
    have hgF n : gammaF (n + 1) ≫
        Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = gammaF n := by
      change Fc.map (gamma (n + 1)) ≫
        Fc.map (X.asFunctor.map (homOfLE (Nat.le_succ n)).op) = Fc.map (gamma n)
      rw [← Fc.map_comp, hgamma]
    have hgGF n : gammaGF (n + 1) ≫
        Z.asFunctor.map (homOfLE (Nat.le_succ n)).op = gammaGF n := by
      change Gc.map (gammaF (n + 1)) ≫
        Gc.map (Y.asFunctor.map (homOfLE (Nat.le_succ n)).op) = Gc.map (gammaF n)
      rw [← Gc.map_comp, hgF]
    let b := roosAugment gamma hgamma
    let bF := roosAugment gammaF hgF
    let bGF := roosAugment gammaGF hgGF
    have hbF : Fc.map b ≫ (canonicalKappa F).hom.app X = bF :=
      augmentationMapped F gamma hgamma hgF
    have hbGF : Gc.map bF ≫ (canonicalKappa G).hom.app Y = bGF :=
      augmentationMapped G gammaF hgF hgGF
    have hmap : Gc.map (Fc.map b) ≫
        Gc.map ((canonicalKappa F).hom.app X) ≫ (canonicalKappa G).hom.app Y = bGF := by
      rw [← Gc.map_comp_assoc, hbF, hbGF]
    have hbunit : b ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app (roosF.obj X) ≫
        Gc.map ((canonicalKappa F).hom.app X) ≫ (canonicalKappa G).hom.app Y =
        (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫ bGF := by
      have hn := (a.mapHomologicalComplex (.up ℤ)).unit.naturality b
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      rw [reassoc_of% hn]
      exact congrArg (fun z ↦ (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫ z) hmap
    refine ⟨b, bGF, augmentationSigned gamma hgamma,
      augmentationSigned gammaGF hgGF, hbunit, ?_, ?_⟩
    · intro p
      rw [hbunit]
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [augmentationSigned gammaGF hgGF]
      have hpi : (a.mapHomologicalComplex (.up ℤ)).unit.app P ≫ Pi.lift gammaGF =
          Pi.lift (fun n ↦ gamma n ≫
            (a.mapHomologicalComplex (.up ℤ)).unit.app (X.asFunctor.obj (op n))) := by
        apply Pi.hom_ext
        intro n
        rw [Category.assoc, Pi.lift_π]
        erw [Pi.lift_π]
        exact ((a.mapHomologicalComplex (.up ℤ)).unit.naturality (gamma n)).symm
      apply biprod.hom_ext
      · simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.lift_fst]
        exact congrArg (fun z ↦ z.f (p + 1)) hpi
      · simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.lift_snd]
        exact comp_zero
    · let f := DerivedCategory.Q.map b ≫ thetaA.inv.app X
      have hn := (exactDerivedAdjunctionUniverses a).unit.naturality f
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      change (exactDerivedAdjunctionUniverses a).unit.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategory.map f) ≫ _ = f
      dsimp only [Functor.comp_obj] at hn
      rw [← reassoc_of% hn]
      simp only [hcancel, Category.comp_id]

end CategoryTheory.RoosAdjunctionUnit
