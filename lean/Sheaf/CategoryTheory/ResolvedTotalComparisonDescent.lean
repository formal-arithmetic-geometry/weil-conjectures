/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.InjectiveFiniteTotalDerivedComparison

/-! # Naturality and descent of resolved cosimplicial totals

Source: Stacks Project, derived.tex, Tags 0141 (functorial injective resolutions and
remark-match), 05TH (injective-acyclic) and 015J (two-ss-complex-functor).
(blueprint: lem-sfb-resolved-total-comparison-descent).

Nonnegative complexes use natural indices; extension by zero gives objects of the ordinary
unbounded derived category. The comparisons in the statement are characterized by the
finite-sum inclusions and the actual right-derived unit. No choice of an arbitrary
comparison map or resolution functor is part of the hypotheses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA uB vB wA wB

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex₂

namespace CategoryTheory.ResolvedTotal

variable (A : Type uA) [Category.{vA} A] [Abelian A]

/-- Alternating finite total, with differential δ + (-1)^n d on column n.
Source: Stacks 0133 and 015J
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
def totalFunctor : CosimplicialObject (CochainComplex A ℕ) ⥤ CochainComplex A ℕ :=
  alternatingCofaceMapComplex (CochainComplex A ℕ) ⋙
    HomologicalComplex₂.totalFunctor A (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)

/-- The same finite total, extended by zero in negative degrees.
Source: Stacks 0133 (blueprint: lem-sfb-resolved-total-comparison-descent). -/
def integerTotal : CosimplicialObject (CochainComplex A ℕ) ⥤ CochainComplex A ℤ :=
  totalFunctor A ⋙ ComplexShape.embeddingUpNat.extendFunctor A

variable {A}
variable {B : Type uB} [Category.{vB} B] [Abelian B] (F : A ⥤ B) [F.Additive]

/-- Apply F to every column, preserving every simplex operator, and then take the finite total.
Source: Stacks 015J (blueprint: lem-sfb-resolved-total-comparison-descent). -/
def mappedTotal : CosimplicialObject (CochainComplex A ℕ) ⥤ CochainComplex B ℕ :=
  (CosimplicialObject.whiskering _ _).obj (F.mapHomologicalComplex (ComplexShape.up ℕ)) ⋙
    totalFunctor B

/-- The mapped finite total extended by zero, before localization.
Source: Stacks 015J (blueprint: lem-sfb-resolved-total-comparison-descent). -/
def mappedIntegerTotal : CosimplicialObject (CochainComplex A ℕ) ⥤ CochainComplex B ℤ :=
  mappedTotal F ⋙ ComplexShape.embeddingUpNat.extendFunctor B

/-- Extend a finite-total comparison, using the canonical compatibility with extension by zero.
Source: Stacks 015J (blueprint: lem-sfb-resolved-total-comparison-descent). -/
def extendComparison
    (β : totalFunctor A ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ≅ mappedTotal F)
    (J : CosimplicialObject (CochainComplex A ℕ)) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((integerTotal A).obj J) ≅
      (mappedIntegerTotal F).obj J :=
  ((totalFunctor A).obj J).mapExtendIso ComplexShape.embeddingUpNat F ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor B).mapIso (β.app J)

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
  [PreservesFiniteLimits F]

/-- The actual right-derived unit on a complex, transported from the homotopy category to Q.
Source: Stacks 05TH; the recorded derived-category convention uses this ordinary unit.
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
def derivedUnit (E : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj E) :=
  ((DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E)).inv ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj E) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).app E).hom

/-- An augmented, columnwise quasi-isomorphic nonnegative injective replacement.
Source: Stacks 0141 and remark-match
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
structure Replacement (K : CosimplicialObject (CochainComplex A ℕ)) where
  /-- The strict replacement diagram. -/
  diagram : CosimplicialObject (CochainComplex A ℕ)
  /-- The strict augmentation from K. -/
  augmentation : K ⟶ diagram
  /-- Each column augmentation is a quasi-isomorphism. -/
  quasiIso : ∀ n : SimplexCategory, QuasiIso (augmentation.app n)
  /-- Every term in every column is injective. -/
  injective : ∀ (n : SimplexCategory) (q : ℕ), Injective ((diagram.obj n).X q)

/-- A finite augmentation-preserving zigzag through injective replacements of the same K.
Source: Stacks 0141, common-resolution comparison
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
inductive AugmentedZigzag {K : CosimplicialObject (CochainComplex A ℕ)} :
    Replacement K → Replacement K → Type (max uA vA)
  | nil (R : Replacement K) : AugmentedZigzag R R
  | forward {R S U : Replacement K} (h : R.diagram ⟶ S.diagram)
      (comm : R.augmentation ≫ h = S.augmentation) (tail : AugmentedZigzag S U) :
      AugmentedZigzag R U
  | backward {R S U : Replacement K} (h : S.diagram ⟶ R.diagram)
      (comm : S.augmentation ≫ h = R.augmentation) (tail : AugmentedZigzag S U) :
      AugmentedZigzag R U

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary derived unit, as a natural transformation on complexes. -/
private def unitNat :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := derivedUnit F
  naturality {E E'} g := by
    have h₁ := (DerivedCategory.quotientCompQhIso B).inv.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map g)
    have h₂ := F.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient _ _).map g)
    have h₃ := (DerivedCategory.quotientCompQhIso A).hom.naturality g
    dsimp at h₁ h₂ h₃
    dsimp only [Functor.comp_map]
    simp only [derivedUnit, Category.assoc, ← F.rightDerivedFunctor.map_comp]
    simp only [Iso.app_inv, Iso.app_hom]
    rw [reassoc_of% h₁, reassoc_of% h₂]
    simp only [← F.rightDerivedFunctor.map_comp, ← h₃]

omit [IsGrothendieckAbelian.{vB} B] [PreservesFiniteLimits F] in
private lemma unit_isIso (E : CochainComplex A ℤ) [E.IsKInjective] :
    IsIso ((unitNat F).app E) := by
  have h : (unitNat F).app E = (F.rightDerivedFunctorObjQIso E).inv := by
    simp [unitNat, derivedUnit, Functor.rightDerivedFunctorObjQIso]
  rw [h]
  infer_instance

/-- The unit after the canonical map/extension identification. -/
private def nonnegativeUnit :
    F.mapHomologicalComplex (.up ℕ) ⋙ ComplexShape.embeddingUpNat.extendFunctor B ⋙
        DerivedCategory.Q ⟶
      ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q ⋙
        F.rightDerivedFunctor :=
  (Functor.isoWhiskerRight (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso F).symm
      DerivedCategory.Q).hom ≫
    Functor.whiskerLeft (ComplexShape.embeddingUpNat.extendFunctor A) (unitNat F)

omit [IsGrothendieckAbelian.{vB} B] [PreservesFiniteLimits F] in
private lemma nonnegativeUnit_isIso (E : CochainComplex A ℕ)
    [CochainComplex.IsKInjective (E.extend ComplexShape.embeddingUpNat)] :
    IsIso ((nonnegativeUnit F).app E) := by
  have := unit_isIso F (E.extend ComplexShape.embeddingUpNat)
  change IsIso (DerivedCategory.Q.map
    (E.mapExtendIso ComplexShape.embeddingUpNat F).inv ≫
      (unitNat F).app (E.extend ComplexShape.embeddingUpNat))
  infer_instance

/-- The same natural unit after finite totalization. -/
private def totalUnit
    (β : totalFunctor A ⋙ F.mapHomologicalComplex (.up ℕ) ≅ mappedTotal F) :
    mappedIntegerTotal F ⋙ DerivedCategory.Q ⟶
      integerTotal A ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerRight (Functor.isoWhiskerRight β.symm
      (ComplexShape.embeddingUpNat.extendFunctor B)) DerivedCategory.Q).hom ≫
    Functor.whiskerLeft (totalFunctor A) (nonnegativeUnit F)

omit [IsGrothendieckAbelian.{vB} B] [PreservesFiniteLimits F] in
private lemma totalUnit_isIso
    (β : totalFunctor A ⋙ F.mapHomologicalComplex (.up ℕ) ≅ mappedTotal F)
    (J : CosimplicialObject (CochainComplex A ℕ))
    [((integerTotal A).obj J).IsKInjective] : IsIso ((totalUnit F β).app J) := by
  have : CochainComplex.IsKInjective
      (((totalFunctor A).obj J).extend ComplexShape.embeddingUpNat) :=
    (inferInstance : ((integerTotal A).obj J).IsKInjective)
  have := nonnegativeUnit_isIso F ((totalFunctor A).obj J)
  change IsIso ((DerivedCategory.Q.mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor B).mapIso (β.app J))).inv ≫
      (nonnegativeUnit F).app ((totalFunctor A).obj J))
  infer_instance

/-- Transport through an invertible component of a natural transformation. -/
private def transportIso {C : Type*} [Category C] {D : Type*} [Category D]
    {P M : C ⥤ D} (σ : M ⟶ P) {X Y : C} (u : X ⟶ Y)
    [IsIso (P.map u)] [IsIso (σ.app Y)] : P.obj X ≅ M.obj Y :=
  asIso (P.map u) ≪≫ (asIso (σ.app Y)).symm

private lemma transportIso_naturality
    {C : Type*} [Category C] {D : Type*} [Category D]
    {P M : C ⥤ D} (σ : M ⟶ P) {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    [IsIso (P.map u)] [IsIso (P.map v)]
    [IsIso (σ.app Y)] [IsIso (σ.app Y')] (sq : u ≫ g = f ≫ v) :
    (transportIso σ u).hom ≫ M.map g = P.map f ≫ (transportIso σ v).hom := by
  apply (cancel_mono (σ.app Y')).1
  simp only [transportIso, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, σ.naturality g, IsIso.inv_hom_id, Category.comp_id]
  simp only [IsIso.inv_hom_id_assoc, ← P.map_comp, sq]

/-- Every augmented leg remains a quasi-isomorphism after applying F and finite totalization.
Source: Stacks 05TH and 015J
(blueprint: lem-sfb-resolved-total-comparison-descent).

Proof (step 5 of the node): two-out-of-three makes h columnwise a quasi-isomorphism.
The injective finite-total comparison, applied to h and to the identity of its source,
gives bounded-below injective totals. Invert naturality of the derived unit on these
totals. Thus QF(T(h)) is conjugate to RF(QT(h)) and is invertible. Naturality of the
summand-preserving finite-total comparison makes QT(Fh) invertible too. Cohomology
factors through Q (def-weil-abstract-derived-category), so T(Fh) is a quasi-isomorphism.
This uses lem-sfb-injective-finite-total-derived-comparison and
sk-def-sfb-derived-categories, without asserting that F preserves arbitrary quasi-isomorphisms. -/
theorem mapped_leg_quasiIso
    {K : CosimplicialObject (CochainComplex A ℕ)} (R S : Replacement K)
    (h : R.diagram ⟶ S.diagram) (comm : R.augmentation ≫ h = S.augmentation) :
    QuasiIso ((mappedTotal F).map h) := by
  classical
  let d := Classical.choice (injective_finite_total_derived_comparison F)
  let β : totalFunctor A ⋙ F.mapHomologicalComplex (.up ℕ) ≅ mappedTotal F :=
    NatIso.ofComponents d.beta (fun g ↦ d.beta_natural _ _ g)
  have hcol (n : SimplexCategory) : QuasiIso (h.app n) := by
    have := R.quasiIso n
    have hc : QuasiIso (R.augmentation.app n ≫ h.app n) := by
      rw [← NatTrans.comp_app, comm]
      exact S.quasiIso n
    exact quasiIso_of_comp_left (R.augmentation.app n) (h.app n)
  have : QuasiIso ((totalFunctor A).map h) :=
    d.total_quasiIso _ _ h hcol S.injective
  have : QuasiIso ((integerTotal A).map h) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
      inferInstance
  have : CochainComplex.IsKInjective ((integerTotal A).obj R.diagram) :=
    d.total_kInjective _ R.injective
  have : CochainComplex.IsKInjective ((integerTotal A).obj S.diagram) :=
    d.total_kInjective _ S.injective
  have := totalUnit_isIso F β R.diagram
  have := totalUnit_isIso F β S.diagram
  have hn := (totalUnit F β).naturality h
  have heq : DerivedCategory.Q.map ((mappedIntegerTotal F).map h) =
      (totalUnit F β).app R.diagram ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map ((integerTotal A).map h)) ≫
          inv ((totalUnit F β).app S.diagram) := by
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp
  have hQ : IsIso (DerivedCategory.Q.map ((mappedIntegerTotal F).map h)) := by
    rw [heq]
    infer_instance
  exact (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).1
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hQ)

/-- The localized isomorphism of one augmented leg, obtained from its actual total map.
Source: Stacks 05TH and 015J
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
def legIso {K : CosimplicialObject (CochainComplex A ℕ)} (R S : Replacement K)
    (h : R.diagram ⟶ S.diagram) (comm : R.augmentation ≫ h = S.augmentation) :
    DerivedCategory.Q.obj ((mappedIntegerTotal F).obj R.diagram) ≅
      DerivedCategory.Q.obj ((mappedIntegerTotal F).obj S.diagram) :=
  haveI : QuasiIso ((mappedIntegerTotal F).map h) :=
    (HomologicalComplex.quasiIso_extendMap_iff ((mappedTotal F).map h)
      ComplexShape.embeddingUpNat).2 (mapped_leg_quasiIso F R S h comm)
  asIso (DerivedCategory.Q.map ((mappedIntegerTotal F).map h))

/-- Evaluate a finite augmented zigzag by its localized arrows, inverting backward legs.
Source: Stacks 0141 and 05TH
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
def zigzagIso {K : CosimplicialObject (CochainComplex A ℕ)} {R S : Replacement K}
    (p : AugmentedZigzag R S) :
    DerivedCategory.Q.obj ((mappedIntegerTotal F).obj R.diagram) ≅
      DerivedCategory.Q.obj ((mappedIntegerTotal F).obj S.diagram) :=
  match p with
  | .nil _ => Iso.refl _
  | .forward h comm tail => legIso F _ _ h comm ≪≫ zigzagIso tail
  | .backward h comm tail => (legIso F _ _ h comm).symm ≪≫ zigzagIso tail

/-- The four strict common-resolution legs are columnwise quasi-isomorphisms, and their
mapped finite totals are quasi-isomorphisms.
Source: Stacks 0141 (remark-match), 05TH and 015J
(blueprint: lem-sfb-resolved-total-comparison-descent).

Proof (steps 4 and 5): postcomposition with I preserves the simplex identities. Naturality
of η gives I(u)η_K = η_J u and I(w)η_K = η_N w. Two-out-of-three gives the columnwise
quasi-isomorphisms I(u), I(w); the η legs already have that property. The five diagrams
J, I(J), I(K), I(N), N have augmentations u, η_J u, η_K, η_N w, w, all columnwise
quasi-isomorphisms into termwise injective columns. Apply mapped_leg_quasiIso to each leg,
using the inverse-unit argument of step 5. No existence of I beyond the given I is assumed. -/
theorem common_resolution_legs
    {K : CosimplicialObject (CochainComplex A ℕ)} (R S : Replacement K)
    (I : CochainComplex A ℕ ⥤ CochainComplex A ℕ)
    (η : 𝟭 (CochainComplex A ℕ) ⟶ I)
    (hη : ∀ E : CochainComplex A ℕ, QuasiIso (η.app E))
    (hI : ∀ (E : CochainComplex A ℕ) (q : ℕ), Injective ((I.obj E).X q)) :
    (∀ n : SimplexCategory,
      QuasiIso ((Functor.whiskerLeft R.diagram η).app n) ∧
      QuasiIso ((Functor.whiskerRight R.augmentation I).app n) ∧
      QuasiIso ((Functor.whiskerRight S.augmentation I).app n) ∧
      QuasiIso ((Functor.whiskerLeft S.diagram η).app n)) ∧
    QuasiIso ((mappedTotal F).map (Functor.whiskerLeft R.diagram η)) ∧
    QuasiIso ((mappedTotal F).map (Functor.whiskerRight R.augmentation I)) ∧
    QuasiIso ((mappedTotal F).map (Functor.whiskerRight S.augmentation I)) ∧
    QuasiIso ((mappedTotal F).map (Functor.whiskerLeft S.diagram η)) := by
  let U : Replacement K :=
    ⟨K ⋙ I, Functor.whiskerLeft K η, fun n ↦ hη (K.obj n),
      fun n q ↦ hI (K.obj n) q⟩
  let RI : Replacement K :=
    ⟨R.diagram ⋙ I, R.augmentation ≫ Functor.whiskerLeft R.diagram η,
      fun n ↦ by
        have := R.quasiIso n
        have := hη (R.diagram.obj n)
        change QuasiIso (R.augmentation.app n ≫ η.app (R.diagram.obj n))
        infer_instance,
      fun n q ↦ hI (R.diagram.obj n) q⟩
  let SI : Replacement K :=
    ⟨S.diagram ⋙ I, S.augmentation ≫ Functor.whiskerLeft S.diagram η,
      fun n ↦ by
        have := S.quasiIso n
        have := hη (S.diagram.obj n)
        change QuasiIso (S.augmentation.app n ≫ η.app (S.diagram.obj n))
        infer_instance,
      fun n q ↦ hI (S.diagram.obj n) q⟩
  have hR : U.augmentation ≫ Functor.whiskerRight R.augmentation I =
      RI.augmentation := by
    apply NatTrans.ext
    funext n
    exact (η.naturality (R.augmentation.app n)).symm
  have hS : U.augmentation ≫ Functor.whiskerRight S.augmentation I =
      SI.augmentation := by
    apply NatTrans.ext
    funext n
    exact (η.naturality (S.augmentation.app n)).symm
  refine ⟨?_, mapped_leg_quasiIso F R RI _ rfl,
    mapped_leg_quasiIso F U RI _ hR, mapped_leg_quasiIso F U SI _ hS,
    mapped_leg_quasiIso F S SI _ rfl⟩
  intro n
  have hmap {J : CosimplicialObject (CochainComplex A ℕ)} (R : Replacement J) :
      QuasiIso ((Functor.whiskerRight R.augmentation I).app n) := by
    have := hη (J.obj n)
    have := hη (R.diagram.obj n)
    have := R.quasiIso n
    have : QuasiIso (η.app (J.obj n) ≫ I.map (R.augmentation.app n)) := by
      rw [← η.naturality (R.augmentation.app n)]
      simp only [Functor.id_map]
      infer_instance
    change QuasiIso (I.map (R.augmentation.app n))
    exact quasiIso_of_comp_left (η.app (J.obj n)) (I.map (R.augmentation.app n))
  exact ⟨hη _, hmap R, hmap S, hη _⟩

/-- The specified four-leg common-resolution comparison, as a product of localized maps.
Source: Stacks 0141 (remark-match)
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
def commonResolutionIso
    {K : CosimplicialObject (CochainComplex A ℕ)} (R S : Replacement K)
    (I : CochainComplex A ℕ ⥤ CochainComplex A ℕ)
    (η : 𝟭 (CochainComplex A ℕ) ⟶ I)
    (hη : ∀ E : CochainComplex A ℕ, QuasiIso (η.app E))
    (hI : ∀ (E : CochainComplex A ℕ) (q : ℕ), Injective ((I.obj E).X q)) :
    DerivedCategory.Q.obj ((mappedIntegerTotal F).obj R.diagram) ≅
      DerivedCategory.Q.obj ((mappedIntegerTotal F).obj S.diagram) :=
  haveI : QuasiIso ((mappedIntegerTotal F).map (Functor.whiskerLeft R.diagram η)) :=
    (HomologicalComplex.quasiIso_extendMap_iff ((mappedTotal F).map
      (Functor.whiskerLeft R.diagram η)) ComplexShape.embeddingUpNat).2
      (common_resolution_legs F R S I η hη hI).2.1
  haveI : QuasiIso ((mappedIntegerTotal F).map (Functor.whiskerRight R.augmentation I)) :=
    (HomologicalComplex.quasiIso_extendMap_iff ((mappedTotal F).map
      (Functor.whiskerRight R.augmentation I)) ComplexShape.embeddingUpNat).2
      (common_resolution_legs F R S I η hη hI).2.2.1
  haveI : QuasiIso ((mappedIntegerTotal F).map (Functor.whiskerRight S.augmentation I)) :=
    (HomologicalComplex.quasiIso_extendMap_iff ((mappedTotal F).map
      (Functor.whiskerRight S.augmentation I)) ComplexShape.embeddingUpNat).2
      (common_resolution_legs F R S I η hη hI).2.2.2.1
  haveI : QuasiIso ((mappedIntegerTotal F).map (Functor.whiskerLeft S.diagram η)) :=
    (HomologicalComplex.quasiIso_extendMap_iff ((mappedTotal F).map
      (Functor.whiskerLeft S.diagram η)) ComplexShape.embeddingUpNat).2
      (common_resolution_legs F R S I η hη hI).2.2.2.2
  asIso (DerivedCategory.Q.map
      ((mappedIntegerTotal F).map (Functor.whiskerLeft R.diagram η))) ≪≫
    (asIso (DerivedCategory.Q.map
      ((mappedIntegerTotal F).map (Functor.whiskerRight R.augmentation I)))).symm ≪≫
    asIso (DerivedCategory.Q.map
      ((mappedIntegerTotal F).map (Functor.whiskerRight S.augmentation I))) ≪≫
    (asIso (DerivedCategory.Q.map
      ((mappedIntegerTotal F).map (Functor.whiskerLeft S.diagram η)))).symm

/-- The strict derived-image morphism transported to two resolved total models.
Source: Stacks 05TH, inverse derived-unit naturality
(blueprint: lem-sfb-resolved-total-comparison-descent). -/
def resolvedMap
    (χ : ∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K),
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj ((integerTotal A).obj K)) ≅
        DerivedCategory.Q.obj ((mappedIntegerTotal F).obj R.diagram))
    {K L : CosimplicialObject (CochainComplex A ℕ)} (R : Replacement K)
    (S : Replacement L) (f : K ⟶ L) :
    DerivedCategory.Q.obj ((mappedIntegerTotal F).obj R.diagram) ⟶
      DerivedCategory.Q.obj ((mappedIntegerTotal F).obj S.diagram) :=
  (χ K R).inv ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map ((integerTotal A).map f)) ≫
    (χ L S).hom

set_option backward.isDefEq.respectTransparency false in
/-- Naturality, common-resolution descent, and all choice compatibilities for resolved totals.
Source: Stacks Project, derived.tex Tags 0141 (remark-match), 05TH and 015J.
(blueprint: lem-sfb-resolved-total-comparison-descent).

Proof:
1. The finite-total comparison β sends each F of a summand inclusion to the corresponding
   inclusion. Check naturality on these inclusions (finite biproduct extensionality).
2. On a bounded-below injective complex the derived unit α is invertible. Invert
   RF(Qh)α_E = α_E'QF(h) to obtain QF(h)ρ_E = ρ_E'RF(Qh), where ρ = α⁻¹.
   Use lem-sfb-injective-finite-total-derived-comparison and sk-def-sfb-derived-categories.
3. Define χ_u = RF(QT(u))ρ_T(J)Qβ_J and c_u = RF(Qu)ρ_J, in Lean composition order.
   Totalization respects gu = vf. Substitute the naturality equation from step 2 and
   then naturality of β. This gives both displayed strict-square equations. Functor
   laws give the identity and composition clauses for the transported derived maps.
4. Apply common_resolution_legs to the four specified strict arrows; its proof uses
   naturality of η, two-out-of-three and the given injectivity of I(E), including I(K).
5. Apply mapped_leg_quasiIso to any augmented leg between injective replacements.
   Its localized map is χ_b χ_a⁻¹, by step 3 with f = id. A backward arrow gives
   the inverse. Multiplying along any finite zigzag cancels all intermediate χ's.
6. The four-leg product therefore equals χ_w χ_u⁻¹, independently of I and of the
   augmented zigzag. Cancellation also gives e_u,u = id and e_w,z e_u,w = e_u,z.
7. For two strict lifts g, g' of the same f, both composites in the final choice
   naturality square equal χ_v' RF(QT(f)) χ_u⁻¹, proving compatibility. -/
theorem resolved_total_comparison_descent :
    ∃ (β : totalFunctor A ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ≅ mappedTotal F)
      (χ : ∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K),
        F.rightDerivedFunctor.obj (DerivedCategory.Q.obj ((integerTotal A).obj K)) ≅
          DerivedCategory.Q.obj ((mappedIntegerTotal F).obj R.diagram))
      (c : ∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K)
        (n : SimplexCategory),
        F.rightDerivedFunctor.obj
            (DerivedCategory.Q.obj ((K.obj n).extend ComplexShape.embeddingUpNat)) ≅
          DerivedCategory.Q.obj
            ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (R.diagram.obj n)).extend
              ComplexShape.embeddingUpNat))),
    (∀ (J : CosimplicialObject (CochainComplex A ℕ)) (n q : ℕ),
      F.map (HomologicalComplex₂.ιTotal ((alternatingCofaceMapComplex _).obj J)
          (ComplexShape.up ℕ) n q (n + q) rfl) ≫ (β.app J).hom.f (n + q) =
        (HomologicalComplex₂.ιTotal ((alternatingCofaceMapComplex _).obj
          (J ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)))
            (ComplexShape.up ℕ) n q (n + q) rfl)) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K),
      (χ K R).hom ≫ (DerivedCategory.Q.mapIso (extendComparison F β R.diagram)).inv ≫
          derivedUnit F ((integerTotal A).obj R.diagram) =
        F.rightDerivedFunctor.map
          (DerivedCategory.Q.map ((integerTotal A).map R.augmentation))) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K)
      (n : SimplexCategory),
      (c K R n).hom ≫ DerivedCategory.Q.map
          ((R.diagram.obj n).mapExtendIso ComplexShape.embeddingUpNat F).inv ≫
          derivedUnit F ((R.diagram.obj n).extend ComplexShape.embeddingUpNat) =
        F.rightDerivedFunctor.map (DerivedCategory.Q.map
          (HomologicalComplex.extendMap (R.augmentation.app n) ComplexShape.embeddingUpNat))) ∧
    (∀ (K L : CosimplicialObject (CochainComplex A ℕ))
      (R : Replacement K) (S : Replacement L) (f : K ⟶ L)
      (g : R.diagram ⟶ S.diagram), R.augmentation ≫ g = f ≫ S.augmentation →
      (χ K R).hom ≫ DerivedCategory.Q.map ((mappedIntegerTotal F).map g) =
          F.rightDerivedFunctor.map (DerivedCategory.Q.map ((integerTotal A).map f)) ≫
            (χ L S).hom ∧
      (∀ n : SimplexCategory,
        (c K R n).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.extendMap
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (g.app n))
              ComplexShape.embeddingUpNat) =
          F.rightDerivedFunctor.map (DerivedCategory.Q.map
            (HomologicalComplex.extendMap (f.app n) ComplexShape.embeddingUpNat)) ≫
              (c L S n).hom)) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K),
      resolvedMap F χ R R (𝟙 K) = 𝟙 _) ∧
    (∀ (K L N : CosimplicialObject (CochainComplex A ℕ))
      (R : Replacement K) (S : Replacement L) (U : Replacement N) (f : K ⟶ L) (g : L ⟶ N),
      resolvedMap F χ R U (f ≫ g) = resolvedMap F χ R S f ≫ resolvedMap F χ S U g) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R S : Replacement K)
      (I : CochainComplex A ℕ ⥤ CochainComplex A ℕ)
      (η : 𝟭 (CochainComplex A ℕ) ⟶ I)
      (hη : ∀ E : CochainComplex A ℕ, QuasiIso (η.app E))
      (hI : ∀ (E : CochainComplex A ℕ) (q : ℕ), Injective ((I.obj E).X q)),
      commonResolutionIso F R S I η hη hI = (χ K R).symm ≪≫ χ K S) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R S : Replacement K)
      (p : AugmentedZigzag R S), zigzagIso F p = (χ K R).symm ≪≫ χ K S) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K),
      (χ K R).symm ≪≫ χ K R = Iso.refl _) ∧
    (∀ (K : CosimplicialObject (CochainComplex A ℕ)) (R S U : Replacement K),
      ((χ K R).symm ≪≫ χ K S) ≪≫ ((χ K S).symm ≪≫ χ K U) =
        (χ K R).symm ≪≫ χ K U) ∧
    (∀ (K L : CosimplicialObject (CochainComplex A ℕ))
      (R R' : Replacement K) (S S' : Replacement L) (f : K ⟶ L)
      (g : R.diagram ⟶ S.diagram) (g' : R'.diagram ⟶ S'.diagram),
      R.augmentation ≫ g = f ≫ S.augmentation →
      R'.augmentation ≫ g' = f ≫ S'.augmentation →
      DerivedCategory.Q.map ((mappedIntegerTotal F).map g) ≫
          ((χ L S).symm ≪≫ χ L S').hom =
        ((χ K R).symm ≪≫ χ K R').hom ≫
          DerivedCategory.Q.map ((mappedIntegerTotal F).map g')) := by
  classical
  let d := Classical.choice (injective_finite_total_derived_comparison F)
  let β : totalFunctor A ⋙ F.mapHomologicalComplex (.up ℕ) ≅ mappedTotal F :=
    NatIso.ofComponents d.beta (fun g ↦ d.beta_natural _ _ g)
  have htot (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K) :
      QuasiIso ((integerTotal A).map R.augmentation) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
      (d.total_quasiIso _ _ _ R.quasiIso R.injective)
  have hu (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K) :
      IsIso ((totalUnit F β).app R.diagram) := by
    have : CochainComplex.IsKInjective ((integerTotal A).obj R.diagram) :=
      d.total_kInjective _ R.injective
    exact totalUnit_isIso F β R.diagram
  let χ (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K) :=
    have := htot K R
    have := hu K R
    have : IsIso ((integerTotal A ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor).map
        R.augmentation) := by
      dsimp only [Functor.comp_map]
      infer_instance
    transportIso (totalUnit F β) R.augmentation
  let c (K : CosimplicialObject (CochainComplex A ℕ)) (R : Replacement K)
      (n : SimplexCategory) :=
    have := R.quasiIso n
    have : QuasiIso (HomologicalComplex.extendMap (R.augmentation.app n)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
        inferInstance
    have : CochainComplex.IsKInjective
        ((R.diagram.obj n).extend ComplexShape.embeddingUpNat) :=
      d.column_kInjective _ R.injective n
    have := nonnegativeUnit_isIso F (R.diagram.obj n)
    have : IsIso ((ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q ⋙
        F.rightDerivedFunctor).map (R.augmentation.app n)) := by
      change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap (R.augmentation.app n) ComplexShape.embeddingUpNat)))
      infer_instance
    transportIso (nonnegativeUnit F) (R.augmentation.app n)
  have hn (K L : CosimplicialObject (CochainComplex A ℕ))
      (R : Replacement K) (S : Replacement L) (f : K ⟶ L) (g : R.diagram ⟶ S.diagram)
      (sq : R.augmentation ≫ g = f ≫ S.augmentation) :
      (χ K R).hom ≫ DerivedCategory.Q.map ((mappedIntegerTotal F).map g) =
        F.rightDerivedFunctor.map (DerivedCategory.Q.map ((integerTotal A).map f)) ≫
          (χ L S).hom := by
    have := htot K R
    have := htot L S
    have := hu K R
    have := hu L S
    have : IsIso ((integerTotal A ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor).map
        R.augmentation) := by
      dsimp only [Functor.comp_map]
      infer_instance
    have : IsIso ((integerTotal A ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor).map
        S.augmentation) := by
      dsimp only [Functor.comp_map]
      infer_instance
    exact transportIso_naturality (totalUnit F β) _ _ _ _ sq
  have he {K : CosimplicialObject (CochainComplex A ℕ)} (R S : Replacement K)
      (g : R.diagram ⟶ S.diagram) (sq : R.augmentation ≫ g = S.augmentation) :
      legIso F R S g sq = (χ K R).symm ≪≫ χ K S := by
    apply Iso.ext
    have h := hn K K R S (𝟙 K) g (by simpa using sq)
    simp only [Functor.map_id, Category.id_comp] at h
    apply (cancel_epi (χ K R).hom).1
    simpa [legIso, Category.assoc] using h
  refine ⟨β, χ, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J n q
    exact d.beta_summand J n q (n + q) rfl
  · intro K R
    have := htot K R
    have := hu K R
    change (χ K R).hom ≫ _ = _
    dsimp only [χ, transportIso, Iso.trans_hom, asIso_hom, Iso.symm_hom]
    have heq : (totalUnit F β).app R.diagram =
        (DerivedCategory.Q.mapIso (extendComparison F β R.diagram)).inv ≫
          derivedUnit F ((integerTotal A).obj R.diagram) := by
      change DerivedCategory.Q.map (HomologicalComplex.extendMap (β.app R.diagram).inv
          ComplexShape.embeddingUpNat) ≫
          DerivedCategory.Q.map (((totalFunctor A).obj R.diagram).mapExtendIso
            ComplexShape.embeddingUpNat F).inv ≫
          derivedUnit F ((integerTotal A).obj R.diagram) = _
      simp only [extendComparison, Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp,
        Category.assoc]
      rfl
    simp only [Category.assoc]
    rw [← heq]
    simp
  · intro K R n
    have := R.quasiIso n
    have : QuasiIso (HomologicalComplex.extendMap (R.augmentation.app n)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
        inferInstance
    have : CochainComplex.IsKInjective
        ((R.diagram.obj n).extend ComplexShape.embeddingUpNat) :=
      d.column_kInjective _ R.injective n
    have := nonnegativeUnit_isIso F (R.diagram.obj n)
    change (c K R n).hom ≫ _ = _
    have heq : (nonnegativeUnit F).app (R.diagram.obj n) =
        DerivedCategory.Q.map
          ((R.diagram.obj n).mapExtendIso ComplexShape.embeddingUpNat F).inv ≫
            derivedUnit F ((R.diagram.obj n).extend ComplexShape.embeddingUpNat) := rfl
    dsimp only [c, transportIso, Iso.trans_hom, asIso_hom, Iso.symm_hom]
    rw [Category.assoc, ← heq]
    simp
  · intro K L R S f g sq
    refine ⟨hn K L R S f g sq, ?_⟩
    intro n
    have := R.quasiIso n
    have := S.quasiIso n
    have : QuasiIso (HomologicalComplex.extendMap (R.augmentation.app n)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
        inferInstance
    have : QuasiIso (HomologicalComplex.extendMap (S.augmentation.app n)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
        inferInstance
    have : CochainComplex.IsKInjective
        ((R.diagram.obj n).extend ComplexShape.embeddingUpNat) :=
      d.column_kInjective _ R.injective n
    have : CochainComplex.IsKInjective
        ((S.diagram.obj n).extend ComplexShape.embeddingUpNat) :=
      d.column_kInjective _ S.injective n
    have := nonnegativeUnit_isIso F (R.diagram.obj n)
    have := nonnegativeUnit_isIso F (S.diagram.obj n)
    have : IsIso ((ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q ⋙
        F.rightDerivedFunctor).map (R.augmentation.app n)) := by
      change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap (R.augmentation.app n) ComplexShape.embeddingUpNat)))
      infer_instance
    have : IsIso ((ComplexShape.embeddingUpNat.extendFunctor A ⋙ DerivedCategory.Q ⋙
        F.rightDerivedFunctor).map (S.augmentation.app n)) := by
      change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap (S.augmentation.app n) ComplexShape.embeddingUpNat)))
      infer_instance
    exact transportIso_naturality (nonnegativeUnit F) _ _ _ _
      (congrArg (fun t ↦ t.app n) sq)
  · intro K R
    simp [resolvedMap]
  · intro K L N R S U f g
    simp [resolvedMap, Functor.map_comp, Category.assoc]
  · intro K R S I η hη hI
    let U : Replacement K :=
      ⟨K ⋙ I, Functor.whiskerLeft K η, fun n ↦ hη (K.obj n),
        fun n q ↦ hI (K.obj n) q⟩
    let RI : Replacement K :=
      ⟨R.diagram ⋙ I, R.augmentation ≫ Functor.whiskerLeft R.diagram η,
        fun n ↦ by
          have := R.quasiIso n
          have := hη (R.diagram.obj n)
          change QuasiIso (R.augmentation.app n ≫ η.app (R.diagram.obj n))
          infer_instance,
        fun n q ↦ hI (R.diagram.obj n) q⟩
    let SI : Replacement K :=
      ⟨S.diagram ⋙ I, S.augmentation ≫ Functor.whiskerLeft S.diagram η,
        fun n ↦ by
          have := S.quasiIso n
          have := hη (S.diagram.obj n)
          change QuasiIso (S.augmentation.app n ≫ η.app (S.diagram.obj n))
          infer_instance,
        fun n q ↦ hI (S.diagram.obj n) q⟩
    have hR : U.augmentation ≫ Functor.whiskerRight R.augmentation I =
        RI.augmentation := by
      apply NatTrans.ext
      funext n
      exact (η.naturality (R.augmentation.app n)).symm
    have hS : U.augmentation ≫ Functor.whiskerRight S.augmentation I =
        SI.augmentation := by
      apply NatTrans.ext
      funext n
      exact (η.naturality (S.augmentation.app n)).symm
    change legIso F R RI _ rfl ≪≫ (legIso F U RI _ hR).symm ≪≫
      legIso F U SI _ hS ≪≫ (legIso F S SI _ rfl).symm = _
    rw [he, he, he, he]
    apply Iso.ext
    simp
  · intro K R S p
    induction p with
    | nil R => apply Iso.ext; simp [zigzagIso]
    | forward g sq tail ih =>
      change legIso F _ _ g sq ≪≫ zigzagIso F tail = _
      rw [he, ih]
      apply Iso.ext
      simp
    | backward g sq tail ih =>
      change (legIso F _ _ g sq).symm ≪≫ zigzagIso F tail = _
      rw [he, ih]
      apply Iso.ext
      simp
  · intro K R
    apply Iso.ext
    simp
  · intro K R S U
    apply Iso.ext
    simp
  · intro K L R R' S S' f g g' sq sq'
    have h := hn K L R S f g sq
    have h' := hn K L R' S' f g' sq'
    apply (cancel_epi (χ K R).hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← h']

end CategoryTheory.ResolvedTotal
