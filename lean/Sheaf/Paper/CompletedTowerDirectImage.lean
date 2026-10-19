/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q08 and Q31
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedTowerDerivedLimitFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Total direct image of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1276;
Stacks Project, Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

private theorem inverse_square_iff {C : Type*} [Category* C]
    {A B D E F G : C} (e : B ≅ D) (p : A ≅ F) (k : F ≅ G) (q : D ≅ E)
    (a : A ⟶ B) (b : G ⟶ E) :
    b ≫ q.inv ≫ e.inv = k.inv ≫ p.inv ≫ a ↔
      a ≫ e.hom ≫ q.hom = p.hom ≫ k.hom ≫ b := by
  constructor
  · intro h
    have hh := congrArg (fun z ↦ p.hom ≫ k.hom ≫ z ≫ e.hom ≫ q.hom) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id] using hh.symm
  · intro h
    have hh := congrArg (fun z ↦ k.inv ≫ p.inv ≫ z ≫ q.inv ≫ e.inv) h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using hh.symm

private theorem levelwise_preservesKInjective
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj R).PreservesKInjectiveComplexes := by
  let : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj L) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj L) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  exact (adj.whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The completed coefficient direct-image structure map adjoint to c_f.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedCoefficientDirectImageMap :
    pbcAdicCompletion Y d ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (pbcAdicCompletion X d) :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app (pbcAdicCompletion Y d) ≫
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (completedCoefficientMap f d)

/-- Sectionwise module direct image with the completed coefficient action.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedModuleDirectImage :
    pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := reductionModuleRing Y (pbcAdicCompletion Y d))
    (R := reductionModuleRing X (pbcAdicCompletion X d))
    ⟨Functor.whiskerRight (completedCoefficientDirectImageMap f d).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Sectionwise completed direct image is additive.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: direct image applies the same underlying maps to sections on base-changed objects.
Addition of linear maps is sectionwise, so direct image preserves addition. -/
@[instance]
theorem completedModuleDirectImage_additive : (completedModuleDirectImage f d).Additive := by
  constructor
  intro M N g h
  rfl

/-- Levelwise direct image, retaining every tower transition and module map.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedTowerModuleDirectImage :
    pbcTowers X (pbcAdicCompletion X d) ⥤ pbcTowers Y (pbcAdicCompletion Y d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completedModuleDirectImage f d)

/-- Levelwise direct image is additive.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: check equality of natural transformations at each level and apply additivity
of the module direct image there. -/
@[instance]
theorem completedTowerModuleDirectImage_additive :
    (completedTowerModuleDirectImage f d).Additive := by
  unfold completedTowerModuleDirectImage
  infer_instance

/-- The unbounded total derived completed-coefficient module direct image.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedDerivedDirectImage :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) ⥤
      DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) :=
  (completedModuleDirectImage f d).rightDerivedFunctor

/-- Total right derived levelwise direct image, computed on K-injective strict towers.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedTowerDirectImage :
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) ⥤
      DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) :=
  (completedTowerModuleDirectImage f d).rightDerivedFunctor

private theorem completedCoefficient_isIso :
    IsIso (completedCoefficientMap f d) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  let e (W : Scheme.{u}) : proEtaleCoefficientTower W Q ≅ adicLisseRingSystem W d.ideal :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun f ↦ (NatTrans.ofOpSequence
        (F := proEtaleCoefficientTower W Q) (G := adicLisseRingSystem W d.ideal)
        (fun _ ↦ 𝟙 _) (fun n ↦ by
          simp [proEtaleCoefficientTower, Q, adicLisseRingSystem])).naturality f)
  let b (W : Scheme.{u}) := e W ≪≫ pbcConstantSystemComparison W d
  let c (W : Scheme.{u}) := HasLimit.isoOfNatIso (b W)
  let L := proEtaleSheafInverseImage f CommRingCat.{u + 1}
  let := (proEtale_profinite_coefficient_inverse_image Q).2.1 X Y f
  let t := L.mapIso (c Y).symm ≪≫ asIso (proEtaleProfiniteComparison f Q) ≪≫ c X
  suffices h : completedCoefficientMap f d = t.hom by
    rw [h]
    infer_instance
  apply limit.hom_ext
  rintro ⟨n⟩
  dsimp only [completedCoefficientMap, t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [limit.lift_π, Category.assoc]
  dsimp only [c]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp only [asIso_hom]
  rw [reassoc_of% (proEtale_profinite_coefficient_inverse_image Q).2.2.1 X Y f (op n)]
  rw [← Category.assoc, ← Category.assoc, ← L.map_comp]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc]
  dsimp only [b, e, Iso.trans_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, proEtaleConstantComparison]
  simp only [completedCoefficientComponent, completedFiniteCoefficientMap, Category.assoc,
    L, pbcConstantSystemComparison, pbcAdicProjection, Q, Iso.trans_inv,
    NatTrans.comp_app, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    Iso.refl_inv, Functor.map_comp]
  dsimp only [proEtaleCoefficientTower, Functor.comp_obj, Functor.ofOpSequence_obj]
  simp only [Iso.refl_hom, Category.id_comp]
  change L.map (pbcAdicProjection Y d n) ≫
      L.map (pbcLevelConstantComparison Y d n).inv ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison X d n).hom =
    L.map (pbcAdicProjection Y d n) ≫
      L.map (pbcLevelConstantComparison Y d n).inv ≫
      L.map (𝟙 (adicLisseConstantRing Y
        (A ⧸ d.ideal ^ (n + 1)))) ≫
      proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison X d n).hom
  rw [L.map_id, Category.id_comp]

/-- Sectionwise completed direct image preserves all limits.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: module direct image is right adjoint to inverse image followed by scalar
extension along c_f. Right adjoints preserve limits; the comparison is induced by
the direct images of the limit projections. -/
@[instance]
theorem completedModuleDirectImage_preservesLimits :
    PreservesLimits (completedModuleDirectImage f d) := by
  let := completedCoefficient_isIso f d
  let adj := proEtaleRingModuleAdjunction f (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))
  exact adj.rightAdjoint_preservesLimits

/-- Restrict the existing limit-preservation instance to the small tower index universe.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits). -/
instance completedModuleDirectImage_preservesSmallestLimits :
    PreservesLimitsOfSize.{0, 0} (completedModuleDirectImage f d) :=
  preservesSmallestLimits_of_preservesLimits (completedModuleDirectImage f d)

/-- The projection-induced ordinary limit comparison is natural in strict towers.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: compose both maps with every target limit projection. Both composites are
direct image applied to the corresponding component of the same tower morphism.
The target limit projections are jointly monomorphic. -/
theorem completedDirectImageLimit_naturality
    {M N : pbcTowers X (pbcAdicCompletion X d)} (h : M ⟶ N) :
    (completedModuleDirectImage f d).map (lim.map h) ≫
        (preservesLimitIso (completedModuleDirectImage f d) N).hom =
      (preservesLimitIso (completedModuleDirectImage f d) M).hom ≫
        lim.map ((completedTowerModuleDirectImage f d).map h) := by
  exact (preservesLimitNatIso (completedModuleDirectImage f d)).hom.naturality h

/-- The ordinary limit comparison, fixed by the universal limit projections.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageLimitIso :
    (lim : pbcTowers X (pbcAdicCompletion X d) ⥤
      pbcModules X (pbcAdicCompletion X d)) ⋙ completedModuleDirectImage f d ≅
    completedTowerModuleDirectImage f d ⋙
      (lim : pbcTowers Y (pbcAdicCompletion Y d) ⥤
        pbcModules Y (pbcAdicCompletion Y d)) :=
  NatIso.ofComponents (fun M ↦ preservesLimitIso (completedModuleDirectImage f d) M)
    (fun h ↦ completedDirectImageLimit_naturality f d h)

/-- Limit preserves K-injective complexes because constant strict towers are exact.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: map a homotopy from an acyclic source across the constant-limit adjunction.
The constant tower of an acyclic complex is acyclic by levelwise exactness, so
K-injectivity annihilates the resulting Hom group. Transport the null-homotopy back. -/
@[instance]
theorem completedTowerLimit_preservesKInjective (T : Scheme.{u}) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d)).PreservesKInjectiveComplexes := by
  exact (constLimAdj : completedTowerConstant d T ⊣ lim).preservesKInjectiveComplexes

/-- Completed levelwise direct image preserves K-injective strict towers.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the completed coefficient structure map is flat by the constant-to-completed
comparison and its finite reductions. Thus the levelwise left adjoint is exact.
Apply the exact-adjoint K-injective criterion to the strict tower adjunction. -/
@[instance]
theorem completedTowerDirectImage_preservesKInjective :
    (completedTowerModuleDirectImage f d).PreservesKInjectiveComplexes := by
  let := completedCoefficient_isIso f d
  let L := proEtaleRingModulePullback f (pbcAdicCompletion Y d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))
  let adj : L ⊣ completedModuleDirectImage f d :=
    proEtaleRingModuleAdjunction f (pbcAdicCompletion Y d)
      (pbcAdicCompletion X d) (asIso (completedCoefficientMap f d))
  exact @levelwise_preservesKInjective _ _ _ _ _ _ L (completedModuleDirectImage f d)
    (proEtaleRingModulePullback_additive f _ _ (asIso (completedCoefficientMap f d)))
    (completedModuleDirectImage_additive f d)
    (proEtaleRingModulePullback_preservesFiniteLimits f _ _
      (asIso (completedCoefficientMap f d)))
    (proEtaleRingModulePullback_preservesFiniteColimits f _ _
      (asIso (completedCoefficientMap f d))) adj

/-- Module direct image with the actual finite quotient coefficient ring.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedFiniteModuleDirectImage (n : ℕ) :=
  proEtaleRingModuleDirectImage f ((pbcAdicRings Y d).obj (op n))
    ((pbcAdicRings X d).obj (op n))
    (asIso (completedFiniteCoefficientMap f d n))

/-- The finite quotient direct image obtained by total right derivation.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
abbrev completedFiniteDerivedDirectImage (n : ℕ) :=
  (completedFiniteModuleDirectImage f d n).rightDerivedFunctor

private theorem completedCoefficient_projection (n : ℕ) :
    completedCoefficientMap f d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap f d n := by
  exact limit.lift_π _ (op n)

/-- Restriction commutes with ordinary direct image by identity on underlying sections.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the square of completed structure maps and finite projections commutes by the
component construction of c_f. The two module actions therefore agree. Identity on
sections is a natural linear isomorphism and sectionwise faithfulness proves uniqueness. -/
theorem completedRestrictionDirectImageIso_exists (n : ℕ) :
    ∃! e : pbcRestrict (pbcAdicProjection X d n) ⋙ completedModuleDirectImage f d ≅
        completedFiniteModuleDirectImage f d n ⋙ pbcRestrict (pbcAdicProjection Y d n),
      ∀ (M : pbcModules X ((pbcAdicRings X d).obj (op n))) (U : Y.ProEtᵒᵖ)
        (x : ((pbcRestrict (pbcAdicProjection X d n) ⋙
          completedModuleDirectImage f d).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  let := completedCoefficient_isIso f d
  obtain ⟨e, he, _⟩ := proEtaleRingRestrictionDirectImage_existsUnique f
    (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
    (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
    (pbcAdicProjection Y d n) (pbcAdicProjection X d n)
    (asIso (completedCoefficientMap f d)) (asIso (completedFiniteCoefficientMap f d n))
    (completedCoefficient_projection f d n)
  refine ⟨e.symm, ?_, ?_⟩
  · intro M U x
    have h := he M U ((e.inv.app M).val.app U x)
    have hi := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
    exact h.symm.trans hi
  · intro e' he'
    apply Iso.ext
    ext M U x
    exact (he' M U x).trans (by
      have h := he M U ((e.inv.app M).val.app U x)
      have hi := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
      change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
      exact (h.symm.trans hi).symm)

/-- The uniquely section-normalized restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedRestrictionDirectImageIso (n : ℕ) :
    pbcRestrict (pbcAdicProjection X d n) ⋙ completedModuleDirectImage f d ≅
      completedFiniteModuleDirectImage f d n ⋙ pbcRestrict (pbcAdicProjection Y d n) :=
  (completedRestrictionDirectImageIso_exists f d n).exists.choose

/-- The total right-derived comparison on a completed-coefficient cochain complex.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageComplexUnit
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    DerivedCategory.Q.obj
        (((completedModuleDirectImage f d).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (completedDerivedDirectImage f d).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((completedModuleDirectImage f d).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (completedModuleDirectImage f d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (completedDerivedDirectImage f d).map ((DerivedCategory.quotientCompQhIso _).hom.app C)

/-- The total right-derived comparison on a finite-coefficient cochain complex.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedFiniteDirectImageComplexUnit (n : ℕ)
    (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :
    DerivedCategory.Q.obj
        (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (completedFiniteDerivedDirectImage f d n).obj (DerivedCategory.Q.obj C) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    DerivedCategory.Qh.map
      (((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors (.up ℤ)).inv.app C) ≫
    (completedFiniteModuleDirectImage f d n).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj C) ≫
    (completedFiniteDerivedDirectImage f d n).map
      ((DerivedCategory.quotientCompQhIso _).hom.app C)

-- Compare the explicit scalar-restriction implementations of the same functors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived coefficient comparison is fixed by the ordinary identity comparison
and the universal right-derived units. This normalization prevents an arbitrary
natural isomorphism from being substituted in the projection-formula construction.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: finite module inverse image is exact, and direct images of injective finite
module sheaves are acyclic after scalar restriction. Derive the sectionwise comparison
using such resolutions. The universal right-derived units give the displayed equation
on complexes, and the universal derived property gives uniqueness and invertibility. -/
theorem completedDerivedRestrictionDirectImageIso_exists (n : ℕ) :
    ∃! e : pbcDerivedRestrict (pbcAdicProjection X d n) ⋙ completedDerivedDirectImage f d ≅
        completedFiniteDerivedDirectImage f d n ⋙
          pbcDerivedRestrict (pbcAdicProjection Y d n),
      ∀ C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ,
        completedDirectImageComplexUnit f d
            (((pbcRestrict (pbcAdicProjection X d n)).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (completedDerivedDirectImage f d).map
            ((pbcRestrict (pbcAdicProjection X d n)).mapDerivedCategoryFactors.inv.app C) ≫
          e.hom.app (DerivedCategory.Q.obj C) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (completedRestrictionDirectImageIso f d n).hom (.up ℤ)).app C) ≫
          (pbcRestrict (pbcAdicProjection Y d n)).mapDerivedCategoryFactors.inv.app
            (((completedFiniteModuleDirectImage f d n).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (pbcDerivedRestrict (pbcAdicProjection Y d n)).map
            (completedFiniteDirectImageComplexUnit f d n C) := by
  let := completedCoefficient_isIso f d
  let RX := pbcRestrict (pbcAdicProjection X d n)
  let RY := pbcRestrict (pbcAdicProjection Y d n)
  let F := completedModuleDirectImage f d
  let G := completedFiniteModuleDirectImage f d n
  let comm := completedCoefficient_projection f d n
  let cR := asIso (completedCoefficientMap f d)
  let cS := asIso (completedFiniteCoefficientMap f d n)
  let i := proEtaleRingRestrictionDirectImage f
    (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
    (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
    (pbcAdicProjection Y d n) (pbcAdicProjection X d n) cR cS comm
  have hi : i = (completedRestrictionDirectImageIso f d n).symm := by
    suffices h : i.symm = completedRestrictionDirectImageIso f d n from
      congrArg Iso.symm h
    apply (completedRestrictionDirectImageIso_exists f d n).unique
    · intro M U x
      have he := (Classical.choose_spec
        (proEtaleRingRestrictionDirectImage_existsUnique f
          (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
          (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
          (pbcAdicProjection Y d n) (pbcAdicProjection X d n) cR cS comm)).1
      have h := he M U ((i.inv.app M).val.app U x)
      have h' := congrArg (fun t ↦ t.val.app U x) (i.inv_hom_id_app M)
      change (i.hom.app M).val.app U ((i.inv.app M).val.app U x) = x at h'
      exact h.symm.trans h'
    · exact (completedRestrictionDirectImageIso_exists f d n).exists.choose_spec
  obtain ⟨e, he, hue⟩ := proEtaleRingRestrictionDerivedDirectImage_existsUnique f
    (pbcAdicCompletion Y d) ((pbcAdicRings Y d).obj (op n))
    (pbcAdicCompletion X d) ((pbcAdicRings X d).obj (op n))
    (pbcAdicProjection Y d n) (pbcAdicProjection X d n) cR cS comm
  have hn (e' : G.rightDerivedFunctor ⋙ RY.mapDerivedCategory ≅
      RX.mapDerivedCategory ⋙ F.rightDerivedFunctor)
      (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :=
    inverse_square_iff (e'.app (DerivedCategory.Q.obj C))
      (RY.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex (.up ℤ)).obj C))
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (completedRestrictionDirectImageIso f d n).symm (.up ℤ)).app C))
      (F.rightDerivedFunctor.mapIso (RX.mapDerivedCategoryFactors.app C))
      (RY.mapDerivedCategory.map (completedFiniteDirectImageComplexUnit f d n C))
      (completedDirectImageComplexUnit f d
        ((RX.mapHomologicalComplex (.up ℤ)).obj C))
  have uF (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
      completedDirectImageComplexUnit f d C =
        proEtaleRingDirectImageDerivedUnit f _ _ cR C := by
    have hid : ((completedModuleDirectImage f d).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app C = 𝟙 _ := rfl
    dsimp only [completedDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit]
    rw [hid]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have uG (C : CochainComplex (pbcModules X ((pbcAdicRings X d).obj (op n))) ℤ) :
      completedFiniteDirectImageComplexUnit f d n C =
        proEtaleRingDirectImageDerivedUnit f _ _ cS C := by
    have hid : ((completedFiniteModuleDirectImage f d n).mapHomotopyCategoryFactors
        (.up ℤ)).inv.app C = 𝟙 _ := rfl
    dsimp only [completedFiniteDirectImageComplexUnit, proEtaleRingDirectImageDerivedUnit]
    rw [hid]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  refine ⟨e.symm, ?_, ?_⟩
  · intro C
    apply (hn e C).2
    have heC := he C
    change RY.mapDerivedCategory.map
        (proEtaleRingDirectImageDerivedUnit f _ _ cS C) ≫
        e.hom.app (DerivedCategory.Q.obj C) ≫
        F.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.hom.app C) =
      RY.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app C) ≫
        proEtaleRingDirectImageDerivedUnit f _ _ cR
          ((RX.mapHomologicalComplex (.up ℤ)).obj C) at heC
    simpa only [hi, uF, uG, Functor.mapIso_hom, Iso.app_hom] using heC
  · intro e' he'
    have hh : e'.symm = e := hue e'.symm (by
      intro C
      have h := (hn e'.symm C).1 (he' C)
      change RY.mapDerivedCategory.map
          (proEtaleRingDirectImageDerivedUnit f _ _ cS C) ≫
          e'.symm.hom.app (DerivedCategory.Q.obj C) ≫
          F.rightDerivedFunctor.map (RX.mapDerivedCategoryFactors.hom.app C) =
        RY.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj C) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app C) ≫
          proEtaleRingDirectImageDerivedUnit f _ _ cR
            ((RX.mapHomologicalComplex (.up ℤ)).obj C)
      simpa only [hi, uF, uG, Functor.mapIso_hom, Iso.app_hom] using h)
    exact congrArg Iso.symm hh

/-- The canonical derived restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDerivedRestrictionDirectImageIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicProjection X d n) ⋙ completedDerivedDirectImage f d ≅
      completedFiniteDerivedDirectImage f d n ⋙
        pbcDerivedRestrict (pbcAdicProjection Y d n) :=
  (completedDerivedRestrictionDirectImageIso_exists f d n).exists.choose

/-- The finite projection-formula arrow is the scalar-adjunction mate of direct image
of the reduction unit, followed by the canonical restriction/direct-image comparison.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageProjectionFormula (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (pbcDerivedExtend (pbcAdicProjection Y d n)).obj
        ((completedDerivedDirectImage f d).obj K) ⟶
      (completedFiniteDerivedDirectImage f d n).obj
        ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K) :=
  ((pbcDerivedScalarAdjunction (pbcAdicProjection Y d n)).homEquiv _ _).symm
    ((completedDerivedDirectImage f d).map
      ((pbcDerivedScalarAdjunction (pbcAdicProjection X d n)).unit.app K) ≫
      (completedDerivedRestrictionDirectImageIso f d n).hom.app
        ((pbcDerivedExtend (pbcAdicProjection X d n)).obj K))

/-- Perfectness of each quotient makes this specified projection-formula arrow an
isomorphism, functorial in the input.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: a finite projective resolution of A/I^(n+1) reduces the assertion to the free
rank-one projection formula. It is the identity there. Finite sums, shifts, cones and
retracts preserve invertibility. The mate construction is natural in K throughout. -/
theorem completedDirectImageProjectionFormula_properties (d : AdicCoefficientDatum A) :
    (∀ (n : ℕ) (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))),
      IsIso (completedDirectImageProjectionFormula f d n K)) ∧
    ∀ (n : ℕ) (K L : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
      (h : K ⟶ L),
      (pbcDerivedExtend (pbcAdicProjection Y d n)).map
          ((completedDerivedDirectImage f d).map h) ≫
        completedDirectImageProjectionFormula f d n L =
      completedDirectImageProjectionFormula f d n K ≫
        (completedFiniteDerivedDirectImage f d n).map
          ((pbcDerivedExtend (pbcAdicProjection X d n)).map h) := by
  sorry

/-- Exact tower evaluation preserves K-injectives by its exact left adjoint.
Source: blueprint order 1276, proof step 2 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: the left adjoint puts V at levels at most n and zero above n, with identity
transitions. It is exact levelwise. Apply the exact-adjoint K-injective criterion,
or tower_evaluation_isKInjective, to every complex of strict towers. -/
@[instance]
theorem completedEvaluation_preservesKInjective (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (n : ℕ) :
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T R)).obj
      (op n)).PreservesKInjectiveComplexes := by
  constructor
  intro I hI
  exact tower_evaluation_isKInjective (pbcModules T R) I (op n)

/-- The ordinary evaluation/direct-image comparison is identity at every object and map.
Source: blueprint order 1276, proof step 2 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDirectImageEvaluationIso (n : ℕ) :
    completedTowerModuleDirectImage f d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj (op n) ≅
      (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n) ⋙
        completedModuleDirectImage f d :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Canonical evaluation comparison, retaining the universal right-derived units.
Source: blueprint order 1276, proof step 2 (blueprint: prop-weil-pbc-direct-image-limits). -/
def completedDerivedDirectImageEvaluationIso (n : ℕ) :
    completedTowerDirectImage f d ⋙ pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
      pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ completedDerivedDirectImage f d :=
  (Functor.isoWhiskerLeft (completedTowerDirectImage f d)
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
      (op n)).rightDerivedFunctorIsoMapDerivedCategory).symm ≪≫
    (Functor.rightDerivedFunctorCompIso (completedTowerModuleDirectImage f d)
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
        (op n))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (completedDirectImageEvaluationIso f d n) ≪≫
    Functor.rightDerivedFunctorCompIso
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj (op n))
      (completedModuleDirectImage f d) ≪≫
    Functor.isoWhiskerRight
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n)).rightDerivedFunctorIsoMapDerivedCategory (completedDerivedDirectImage f d)

/-- Derived tower evaluation commutes with total levelwise direct image.
Source: blueprint order 1276 (blueprint: prop-weil-pbc-direct-image-limits).
Proof: evaluation is exact and preserves K-injectives because its left adjoint is
exact. Evaluate a K-injective tower resolution. Both sides are then the same levelwise
direct-image complex. Their universal derived units determine the natural comparison. -/
theorem completedTowerDirectImage_evaluation (n : ℕ) :
    Nonempty (completedTowerDirectImage f d ⋙
      pbcTowerEvaluation Y (pbcAdicCompletion Y d) n ≅
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ⋙ completedDerivedDirectImage f d) := by
  exact ⟨completedDerivedDirectImageEvaluationIso f d n⟩

end AlgebraicGeometry.Scheme
