/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W6
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # The Roos fibre computes total derived inverse limit when products are exact

Source: Stacks Project, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-exact-products-roos-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w g
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory
namespace ExactProductsRoos
variable {B : Type u} [Category.{v} B] [Abelian B]
  [HasCountableProducts B]

/-- The degreewise product of the levels of a strict tower of complexes.
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def product : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex B ℤ where
  obj X := ∏ᶜ (fun n : ℕ ↦ X.asFunctor.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))
  map_id _ := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Limits.Pi.map_π, Category.id_comp]
    exact Category.comp_id _
  map_comp _ _ := by simp [Limits.Pi.map_comp_map]

/-- The endomorphism with coordinates x_n minus t_n(x_(n+1)).
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def difference : product (B := B) ⟶ product where
  app X := towerTransitionEndomorphism
    (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  naturality X Y f := by
    dsimp only [product]
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality
      (homOfLE (Nat.le_succ n)).op).symm

/-- Canonical Roos model map. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def arrowMap {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) :
    Arrow.mk (-difference.app X) ⟶ Arrow.mk (-difference.app Y) where
  left := product.map f
  right := product.map f
  w := by
    change product.map f ≫ (-difference.app Y) = (-difference.app X) ≫ product.map f
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp] using
      congrArg Neg.neg (difference.naturality f)

/-- The functorial mapping fibre of minus the Roos difference map.
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def fibre : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex B ℤ where
  obj X := CochainComplex.mappingCocone (-difference.app X)
  map f := (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) (arrowMap f))⟦(-1 : ℤ)⟧'
  map_id X := by
    have h : arrowMap (𝟙 X) = 𝟙 (Arrow.mk (-difference.app X)) := by
      apply Arrow.hom_ext <;> exact product.map_id X
    rw [h, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
    exact (shiftFunctor _ (-1 : ℤ)).map_id _
  map_comp f k := by
    have h : arrowMap (f ≫ k) = arrowMap f ≫ arrowMap k := by
      apply Arrow.hom_ext <;> exact product.map_comp f k
    rw [h, HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
    exact (shiftFunctor _ (-1 : ℤ)).map_comp _ _

variable [HasLimitsOfShape ℕᵒᵖ B]

/-- The ordinary strict inverse limit, applied termwise.
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
abbrev ordinary : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex B ℤ :=
  (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)

/-- The ordinary limit inclusion into the product of the levels.
Source: Stacks Tag 0941 (blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def inclusion : ordinary (B := B) ⟶ product where
  app X := Limits.Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n)) (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)
  naturality X Y f := by
    apply Limits.Pi.hom_ext
    intro n
    dsimp only [product]
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc,
      Limits.Pi.lift_π]
    exact (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).naturality f

/-- The specified Roos maps satisfy the displayed equation. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
theorem inclusion_difference (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    inclusion.app X ≫ difference.app X = 0 := by
  change (Limits.Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)) ≫
      towerTransitionEndomorphism _ = 0
  apply Limits.Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift,
    Category.assoc, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
    Limits.Pi.lift_π, Limits.Pi.lift_π_assoc, zero_comp, sub_eq_zero]
  ext p
  exact (limit.w (X.X p) (homOfLE (Nat.le_succ n)).op).symm

/-- The specified Roos maps satisfy the displayed equation. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
theorem comparison_condition (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain (ordinary.obj X) (product.obj X) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (inclusion.app X ≫ (-difference.app X)) = 0 := by
  rw [Preadditive.comp_neg, inclusion_difference, neg_zero]
  simp

/-- Canonical Roos model map. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def comparisonApp (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    ordinary.obj X ⟶ fibre.obj X :=
  CochainComplex.mappingCocone.lift (-difference.app X) (inclusion.app X) 0
    (comparison_condition X)

set_option backward.isDefEq.respectTransparency false in
/-- The specified Roos maps satisfy the displayed equation. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
theorem comparisonApp_f (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ) :
    (comparisonApp X).f p = (inclusion.app X).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (-difference.app X) p (p + (-1))
        (by change p + (-1) + 1 = p; omega) := by
  simp only [comparisonApp, CochainComplex.mappingCocone.lift,
    CochainComplex.mappingCocone.liftCocycle, CochainComplex.mappingCocone.liftCochain,
    CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.inr, CochainComplex.HomComplex.Cochain.zero_comp,
    add_zero, CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ p _ _ (p + (-1)) (by omega),
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.assoc]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from ordinary inverse limit to the Roos fibre, with zero second
coordinate. Source: Stacks Tag 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison). -/
@[reducible]
def comparison : ordinary (B := B) ⟶ fibre where
  app := comparisonApp
  naturality X Y f := by
    ext p : 1
    dsimp only [HomologicalComplex.comp_f]
    rw [comparisonApp_f, comparisonApp_f]
    dsimp only [fibre]
    rw [CochainComplex.shiftFunctor_map_f']
    rw [Category.assoc,
      HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f]
    simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun h ↦ h.f p ≫
      HomologicalComplex.homotopyCofiber.inlX (-difference.app Y) p (p + (-1))
        (by change p + (-1) + 1 = p; omega)) (inclusion.naturality f)

variable [HasDerivedCategory.{w} B]

private theorem comparison_quasiIso (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    [∀ p, Injective (I.X p)] : QuasiIso (comparison.app I) := by
  obtain ⟨h, hS⟩ := complexRoos_shortExact I
  let S := ShortComplex.mk (inclusion.app I) (-difference.app I)
    (by rw [Preadditive.comp_neg, inclusion_difference, neg_zero])
  have hs : S.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk _ _ h) _ hS
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by change 𝟙 _ ≫ inclusion.app I = inclusion.app I ≫ 𝟙 _; simp) (by
        change 𝟙 _ ≫ (-difference.app I) = difference.app I ≫ (-𝟙 _)
        simp only [Category.id_comp, Preadditive.comp_neg, Category.comp_id])
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hs (comparison_condition I)

section QuasiIsoHelpers

universe u₁ v₁
variable {B : Type u₁} [Category.{v₁} B] [Abelian B] [HasDerivedCategory B]
  {X Y X' Y' : CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
  (α : Arrow.mk f ⟶ Arrow.mk g)
set_option backward.isDefEq.respectTransparency false in
private theorem coneMap_quasiIso [QuasiIso α.left] [QuasiIso α.right] :
    QuasiIso (CochainComplex.mappingCone.map f g α.left α.right α.w.symm) := by
  let t := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap f g α.left α.right α.w.symm)
  have ht : IsIso t.hom₃ := Pretriangulated.isIso₃_of_isIso₁₂ t
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g)
    (by change IsIso (DerivedCategory.Q.map α.left)
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance)
    (by change IsIso (DerivedCategory.Q.map α.right)
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).1 ht

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory B] in
private theorem coneArrowMap_eq : HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α =
      CochainComplex.mappingCone.map f g α.left α.right α.w.symm := by
  ext n : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f,
      Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero,
      ]
    change _ = (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _ (n + 1) (n + 1) n (by omega) (by omega)]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v]
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_desc_f]
    change _ = (CochainComplex.mappingCone.inr f).f n ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl

variable {B : Type u₁} [Category.{v₁} B] [Abelian B]
  [HasCountableProducts B] [HasExactLimitsOfShape (Discrete ℕ) B]
private theorem productMap_quasiIso (F G : ℕ → CochainComplex B ℤ) (f : ∀ n, F n ⟶ G n)
    [∀ n, QuasiIso (f n)] : QuasiIso (Limits.Pi.map f) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor B (.up ℤ) i
  have (n : ℕ) : IsIso (H.map (f n)) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (f n) i).1 inferInstance
  have he : H.map (Limits.Pi.map f) ≫ piComparison H G =
      piComparison H F ≫ Limits.Pi.map (fun n ↦ H.map (f n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      piComparison_comp_π_assoc, ← H.map_comp]
  have : IsIso (H.map (Limits.Pi.map f) ≫ piComparison H G) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (Limits.Pi.map f)) (piComparison H G)

end QuasiIsoHelpers

variable [HasExactLimitsOfShape (Discrete ℕ) B]

omit [HasLimitsOfShape ℕᵒᵖ B] in
private theorem fibreMap_quasiIso {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ}
    (f : X ⟶ Y) [QuasiIso f] : QuasiIso (fibre.map f) := by
  have (n : ℕ) : QuasiIso
      ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp inferInstance (op n)
  have hp : QuasiIso (product.map f) := by
    change QuasiIso (Limits.Pi.map (fun n : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)))
    exact productMap_quasiIso _ _ _
  have hc : QuasiIso (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
      (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) (arrowMap f)) := by
    rw [coneArrowMap_eq]
    exact coneMap_quasiIso _ _ (arrowMap f)
  exact (CochainComplex.quasiIso_shift_iff _ _).2 hc

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ B)]

/-- With exact countable products the explicit Roos fibre computes every total derived
inverse limit whose comparison is invertible on K-injective towers. The isomorphism
carries the actual zero-second-coordinate ordinary-limit inclusion to that comparison.

Source: Stacks Project, Tags 0940 and 0941
(blueprint: lem-weil-pbc-exact-products-roos-comparison).
Proof: resolve strict tower complexes functorially by K-injective complexes with injective
terms. Their transitions split, so the Roos short complex is short exact, and its kernel
inclusion into the fibre is a quasi-isomorphism. Exact products and the cone triangle
make the fibre functor preserve quasi-isomorphisms. Apply the fibre to the resolution,
invert the kernel comparison there, and use the given derived-limit comparison. Naturality
of these three maps gives a natural isomorphism. Their naturality squares cancel the
resolution map and yield the normalization on every original tower complex. -/
theorem comparisonIso
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : ordinary ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (η.app I)) :
    ∃ e : fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF,
      Functor.whiskerRight comparison DerivedCategory.Q ≫ e.hom = η := by
  let F := CochainComplex.kInjectiveResolutionFunctor.{g} (ℕᵒᵖ ⥤ B)
  let q := CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ B)
  let α := Functor.whiskerRight q (fibre ⋙ DerivedCategory.Q)
  have hi (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (α.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ B) X).2
    have : QuasiIso (fibre.map (q.app X)) := fibreMap_quasiIso (q.app X)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let β := Functor.whiskerLeft F (Functor.whiskerRight comparison DerivedCategory.Q)
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (β.app X) := by
    have : QuasiIso (comparison.app (F.obj X)) := comparison_quasiIso _
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let δ := Functor.whiskerRight q DerivedCategory.Q
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (δ.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ B) X).2
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ℕᵒᵖ ⥤ B) _).2 inferInstance
  have : IsIso δ := NatIso.isIso_of_isIso_app _
  let ε := Functor.whiskerLeft F η
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (ε.app X) := hI _ inferInstance
  have : IsIso ε := NatIso.isIso_of_isIso_app _
  let γ : F ⋙ ordinary ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso ε ≪≫ (Functor.associator F DerivedCategory.Q RF).symm ≪≫
      Functor.isoWhiskerRight (asIso δ).symm RF
  let e : fibre ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso α ≪≫ (Functor.associator F fibre DerivedCategory.Q) ≪≫
      (asIso β).symm ≪≫ γ
  refine ⟨e, ?_⟩
  apply NatTrans.ext
  funext X
  change DerivedCategory.Q.map (comparison.app X) ≫ e.hom.app X = η.app X
  have hq : IsIso (DerivedCategory.Q.map (q.app X)) := inferInstanceAs (IsIso (δ.app X))
  have hc : IsIso (DerivedCategory.Q.map (comparison.app (F.obj X))) :=
    inferInstanceAs (IsIso (β.app X))
  dsimp only [e, γ, α, β, δ, ε, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom]
  simp only [Functor.comp_map, NatIso.isIso_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.id_comp]
  change DerivedCategory.Q.map (comparison.app X) ≫
    DerivedCategory.Q.map (fibre.map (q.app X)) ≫
      inv (DerivedCategory.Q.map (comparison.app (F.obj X))) ≫
        η.app (F.obj X) ≫ RF.map (inv (DerivedCategory.Q.map (q.app X))) = _
  rw [← DerivedCategory.Q.map_comp_assoc, ← comparison.naturality,
    DerivedCategory.Q.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have hn := η.naturality (q.app X)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← RF.map_comp, IsIso.hom_inv_id, RF.map_id]
  exact Category.comp_id _

end ExactProductsRoos
end CategoryTheory
