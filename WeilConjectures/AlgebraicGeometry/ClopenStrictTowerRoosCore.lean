/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.PUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherenceSupplement
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all Mathlib.CategoryTheory.Sites.CompatibleSheafification
import all Mathlib.CategoryTheory.Limits.Types.Products
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Exactness, products and normalized module gluing for strict clopen towers

Source: Stacks Project, Tags 04TS, 07KC and 08TC, finite-clopen application
(blueprint: lem-pur-clopen-strict-tower-roos-core).

This module contains the exact restriction data and the proved product, normalized
module-gluing and generic signed-comparison lemmas used by the strict tower interface.
All constructions are the original sectionwise and strict Roos constructions.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

set_option autoImplicit false
set_option Elab.async false
-- These type-scanning linters are costly on the fully specified gluing identities.
-- The theorem hypotheses use Finite, and the proofs retain ordinary kernel checking.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
universe t u v w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme.ProEt
namespace ClopenRoos

/-- The module universe contains the small site; the ring universe is independent.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev Modules (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u}) :=
  ringedSiteModules.{max v (t + 1)} R

/-- Mathlib's abelian structure, using the published small-site transports explicitly.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
instance modulesAbelian (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u}) :
    Abelian (Modules.{t, u, v} X R) :=
  letI : HasSheafify (topology X) AddCommGrpCat.{max v (t + 1)} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, v} X
  letI : (topology X).WEqualsLocallyBijective AddCommGrpCat.{max v (t + 1)} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, v} X
  SheafOfModules.instAbelian R

/-- The existing strict-tower encoding, with all unbounded cochain degrees.
Source: Stacks 08TC (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev Towers (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u}) :=
  CochainComplex (ℕᵒᵖ ⥤ Modules.{t, u, v} X R) ℤ

/-- The restricted ring with its component site explicit in the type.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev restrictedRing {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) : Sheaf (topology Y) RingCat.{u} :=
  (clopenRingRestriction j).obj R

/-- The recorded module restriction with the component sites explicit.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev restriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    Modules.{t, u, v} X R ⥤ Modules.{t, u, v} Y (restrictedRing j R) :=
  clopenModuleRestriction.{t, u, max v (t + 1)} j R

/-- Additivity of the recorded restriction, with explicit site universes.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
instance restrictionAdditive {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) : (restriction.{t, u, v} j R).Additive :=
  clopenModuleRestriction_additive.{t, u, max v (t + 1)} j R

/-- Ordinary restriction applied in every degree.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev complexRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :=
  (restriction.{t, u, v} j R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of the differentials, tower transitions and strict tower maps.
Source: Stacks 04TS (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev towerRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (restriction.{t, u, v} j R)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The specified negative inclusion into the shifted mapping fibre.
Source: Stacks 014E, 011G (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
def boundary {A : Type v} [Category.{u} A] [Abelian A] [HasCountableProducts A]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : roosP C ⟶ (roosF.obj C)⟦(1 : ℤ)⟧ :=
  -(CochainComplex.mappingCone.inr (roosU C)) ≫
    (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (neg_add_cancel 1)).inv.app _

/-- Restriction to an open site is additive exact.
Source: Stacks 04TS, 015F (blueprint: lem-pur-clopen-strict-tower-roos-core).
Proof: kernels and cokernels on the localized site are restrictions of the original
kernels and cokernels. Restriction is precomposition and commutes with the relevant
sheafification, proving exactness. This is the restriction used in steps 4 and 6. -/
theorem restriction_exact {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (restriction.{t, u, v} j R) ∧
      PreservesFiniteColimits (restriction.{t, u, v} j R) := by
  have : PreservesColimits (restriction.{t, u, v} j R) :=
    (pieceAdjunction.{t, u, max v (t + 1)} j R).leftAdjoint_preservesColimits
  exact ⟨clopenRestriction_preservesFiniteLimits.{t, u, max v (t + 1)} j R,
    inferInstance⟩

/-- The finite-limit part of exact open restriction. Source: Stacks 04TS
(blueprint: lem-pur-clopen-strict-tower-roos-core). -/
instance restrictionLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteLimits (restriction.{t, u, v} j R) :=
  (restriction_exact.{t, u, v} j R).1

/-- The finite-colimit part of exact open restriction. Source: Stacks 04TS
(blueprint: lem-pur-clopen-strict-tower-roos-core). -/
instance restrictionColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) :
    PreservesFiniteColimits (restriction.{t, u, v} j R) :=
  (restriction_exact.{t, u, v} j R).2

/-- The canonical product comparison, with its target written in strict-tower notation.
Source: Stacks 07KC, 08TC (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
def productComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u}) (C : Towers.{t, u, v} X R) :
    (complexRestriction.{t, u, v} j R).obj (roosP C) ⟶
      roosP ((towerRestriction.{t, u, v} j R).obj C) :=
  piComparison (complexRestriction.{t, u, v} j R)
    (fun n : ℕ ↦ C.asFunctor.obj (op n))

/-- The canonical derived restriction and its localization comparison are Mathlib's
exact-functor construction. Source: Stacks 015F
(blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev derivedRestriction {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) RingCat.{u})
    [HasDerivedCategory.{d} (Modules.{t, u, v} X R)]
    [HasDerivedCategory.{d} (Modules.{t, u, v} Y (restrictedRing j R))] :
    DerivedCategory.{d} (Modules.{t, u, v} X R) ⥤
      DerivedCategory.{d} (Modules.{t, u, v} Y (restrictedRing j R)) :=
  (restriction.{t, u, v} j R).mapDerivedCategory

/-- The chosen derived localization, retaining its actual image on chain maps.
Source: Stacks 05RU (blueprint: lem-pur-clopen-strict-tower-roos-core). -/
abbrev localization (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
    [HasDerivedCategory.{d} (Modules.{t, u, v} X R)] :=
  DerivedCategory.Q.{d} (C := Modules.{t, u, v} X R)

section ProductExactness

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

private theorem module_product_epi (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u})
    (F H : ℕ → Modules.{t, u, v} X R) (f : ∀ n, F n ⟶ H n)
    [∀ n, Epi (f n)] : Epi (Limits.Pi.map f) := by
  let T := SheafOfModules.toSheaf.{max v (t + 1)} R ⋙
    sheafCompose (topology X) (CategoryTheory.forget AddCommGrpCat.{max v (t + 1)})
  have hlocal (n : ℕ) : Sheaf.IsLocallySurjective (T.map (f n)) := by
    let g := (SheafOfModules.toSheaf R).map (f n)
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max v (t + 1)} g).mpr
        inferInstance
    change Sheaf.IsLocallySurjective
      ((sheafCompose (topology X)
        (CategoryTheory.forget AddCommGrpCat.{max v (t + 1)})).map g)
    infer_instance
  have : Sheaf.IsLocallySurjective (T.map (Limits.Pi.map f)) := by
    constructor
    intro U s
    obtain ⟨K, V, a, hcov, _, hweak⟩ :=
      exists_affine_weaklyContractible_covering_family X U
    apply (topology X).superset_covering
      (S := Sieve.ofArrows V a) _ (Precoverage.generate_mem_toGrothendieck hcov)
    apply (Sieve.generate_le_iff _ _).mpr
    intro W g hg
    obtain ⟨k⟩ := hg
    let E := SheafOfModules.evaluation.{max v (t + 1)} R (op (V k)) ⋙
      CategoryTheory.forget _
    have hs (n : ℕ) : Function.Surjective (E.map (f n)) := by
      change Function.Surjective ((T.map (f n)).hom.app (op (V k)))
      exact large_section_surjective (C := X.ProEt) (J := topology X) (W := V k)
        (hW := hweak k) (T.obj (F n)) (T.obj (H n)) (T.map (f n))
    exact map_product_surjective E F H f hs
      ((T.obj (∏ᶜ H)).obj.map (a k).op s)
  exact T.epi_of_epi_map inferInstance

private theorem module_countable_exactCore (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) : CountableAB4Star (Modules.{t, u, v} X R) := by
  let A := Modules.{t, u, v} X R
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms := by
    constructor
    intro F H f hf
    have (n : ℕ) : Epi (f.app ⟨n⟩) := inferInstance
    let a : (∏ᶜ (fun n : ℕ ↦ F.obj ⟨n⟩)) ≅ limit F :=
      HasLimit.isoOfNatIso (Discrete.natIso (fun _ ↦ Iso.refl _))
    let b : (∏ᶜ (fun n : ℕ ↦ H.obj ⟨n⟩)) ≅ limit H :=
      HasLimit.isoOfNatIso (Discrete.natIso (fun _ ↦ Iso.refl _))
    have h : Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ b.hom =
        a.hom ≫ lim.map f := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp [a, b, Category.assoc]
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) := module_product_epi X R _ _ _
    have : Epi (a.hom ≫ lim.map f) := h ▸ inferInstance
    exact epi_of_epi a.hom (lim.map f)
  have : HasExactLimitsOfShape (Discrete ℕ) A :=
    hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat A

end ProductExactness

private theorem zero_category_equivalenceCore (A : Type*) [Category A] [HasZeroObject A]
    [HasZeroMorphisms A] (hA : ∀ M : A, IsZero M) :
    Nonempty (A ≌ Discrete PUnit) := by
  apply (equiv_punit_iff_unique A).mpr
  exact ⟨⟨0⟩, fun M N ↦ (hA M).unique_to N⟩

private theorem empty_modules_zeroCore (X : Scheme.{t}) [IsEmpty X]
    (R : Sheaf (topology X) RingCat.{u}) (M : Modules.{t, u, v} X R) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  let : IsEmpty U.unop.left := ⟨fun x ↦ (inferInstance : IsEmpty X).false (U.unop.hom x)⟩
  have h := isTerminalSectionsOfIsEmpty (SheafOfModules.toSheaf R |>.obj M) U.unop
  have : Subsingleton (M.val.obj U) := AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (isZero_zero AddCommGrpCat)
      (h.uniqueUpToIso (isZero_zero AddCommGrpCat).isTerminal))
  exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true

private theorem boundary_coordinates {A : Type v} [Category.{u} A] [Abelian A]
    [HasCountableProducts A] (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (boundary C).f p ≫ (roosχ C p).hom = -biprod.inl := by
  simp only [boundary, roosχ, HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply,
    Iso.trans_hom, Category.assoc, Preadditive.neg_comp]
  congr 1
  simp only [shiftFunctorCompIsoId, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    HomologicalComplex.comp_f, CochainComplex.shiftFunctorAdd'_hom_app_f',
    CochainComplex.shiftFunctorZero_inv_app_f, Functor.comp_obj, Functor.id_obj,
    CochainComplex.shiftFunctorObjXIso]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom]
  simp only [eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
  simp only [CochainComplex.mappingCone.inr]
  simp only [← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.comp_id]
  simp only [Category.assoc]
  change HomologicalComplex.homotopyCofiber.inrX (roosU C) p ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU C) p (p + 1) rfl).hom ≫
      (biprod.braiding _ _).hom = biprod.inl
  rw [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]
  apply biprod.hom_ext <;> simp [biprod.braiding_hom, Category.assoc]

section GenericComparison

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]

private theorem comparison_projection (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosProj C) ≫ roosProductComparison F C =
      roosAdditiveComparison F C ≫ roosProj ((roosTowerAction F).obj C) := by
  apply HomologicalComplex.hom_ext
  intro k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change ((F.mapHomologicalComplex (.up ℤ)).map (roosProj C) ≫
    roosProductComparison F C).f (p + 1) =
    (roosAdditiveComparison F C ≫ roosProj ((roosTowerAction F).obj C)).f (p + 1)
  simpa only [HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, roosProj_f] using (comparison_snd F C p).symm

private theorem comparison_evaluation (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosEval C n) =
      roosAdditiveComparison F C ≫ roosEval ((roosTowerAction F).obj C) n := by
  let H := F.mapHomologicalComplex (.up ℤ)
  change H.map (roosProj C ≫ Pi.π _ n) =
    roosAdditiveComparison F C ≫ roosProj ((roosTowerAction F).obj C) ≫ Pi.π _ n
  rw [H.map_comp]
  rw [← Category.assoc, ← comparison_projection F C, Category.assoc]
  change _ = H.map (roosProj C) ≫ piComparison H _ ≫ Pi.π
    (fun n : ℕ ↦ H.obj (C.asFunctor.obj (op n))) n
  rw [piComparison_comp_π]

private theorem comparison_boundary (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (boundary C) ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
        (roosAdditiveComparison F C)⟦(1 : ℤ)⟧' =
      roosProductComparison F C ≫ boundary ((roosTowerAction F).obj C) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply (cancel_mono (roosχ ((roosTowerAction F).obj C) p).hom).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    CochainComplex.shiftFunctor_map_f', Category.comp_id, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
    CochainComplex.shiftFunctor_obj_X']
  rw [Category.id_comp]
  rw [roosAdditiveComparison_coordinates, ← Category.assoc, ← F.map_comp,
    boundary_coordinates, F.map_neg, Preadditive.neg_comp]
  rw [boundary_coordinates, Preadditive.comp_neg]
  congr 1
  apply biprod.hom_ext <;> simp only [Category.assoc, biprod.map_fst,
    biprod.map_snd, Functor.biprodComparison_fst_assoc,
    Functor.biprodComparison_snd_assoc, biprod.inl_fst_assoc, biprod.inl_snd_assoc]
  · rw [← Category.assoc, ← F.map_comp, biprod.inl_fst, F.map_id, Category.id_comp]
    simp only [biprod.inl_fst, Category.comp_id]
  · rw [← Category.assoc, ← F.map_comp, biprod.inl_snd, F.map_zero, zero_comp]
    simp only [biprod.inl_snd, comp_zero]

private theorem comparison_transition_genericCore (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosU C) ≫ roosProductComparison F C =
      roosProductComparison F C ≫ roosU ((roosTowerAction F).obj C) := by
  exact productComparison_u F C

private def comparison_isoCore [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ roosTowerAction F ⋙ roosF := by
  have (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (roosAdditiveComparison F C) :=
    roosAdditiveComparison_isIso F C
  exact NatIso.ofComponents (fun C ↦ asIso (roosAdditiveComparison F C))
    (fun f ↦ roosAdditiveComparison_natural F f)

private theorem comparison_iso_coordinatesCore [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    ((comparison_isoCore F).hom.app C).f (p + 1) ≫
        (roosχ ((roosTowerAction F).obj C) p).hom =
      F.map (roosχ C p).hom ≫ F.biprodComparison _ _ ≫
        biprod.map ((roosProductComparison F C).f p)
          ((roosProductComparison F C).f (p + 1)) :=
  roosAdditiveComparison_coordinates F C p

private theorem comparison_iso_projectionCore [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosProj C) ≫ roosProductComparison F C =
      (comparison_isoCore F).hom.app C ≫ roosProj ((roosTowerAction F).obj C) :=
  comparison_projection F C

private theorem comparison_iso_evaluationCore [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (roosEval C n) =
      (comparison_isoCore F).hom.app C ≫ roosEval ((roosTowerAction F).obj C) n :=
  comparison_evaluation F C n

private theorem comparison_iso_boundaryCore [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (boundary C) ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((comparison_isoCore F).hom.app C)⟦(1 : ℤ)⟧' =
      roosProductComparison F C ≫ boundary ((roosTowerAction F).obj C) :=
  comparison_boundary F C

private theorem comparison_iso_localizedCore [PreservesLimitsOfShape (Discrete ℕ) F]
    {D : Type*} [Category D] (Q : CochainComplex B ℤ ⥤ D)
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Q.map ((F.mapHomologicalComplex (.up ℤ)).map (roosProj C)) ≫
        Q.map (roosProductComparison F C) =
      (Q.mapIso ((comparison_isoCore F).app C)).hom ≫
        Q.map (roosProj ((roosTowerAction F).obj C)) ∧
    (∀ n, Q.map ((F.mapHomologicalComplex (.up ℤ)).map (roosEval C n)) =
      (Q.mapIso ((comparison_isoCore F).app C)).hom ≫
        Q.map (roosEval ((roosTowerAction F).obj C) n)) ∧
    Q.map ((F.mapHomologicalComplex (.up ℤ)).map (boundary C) ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app _ ≫
        ((comparison_isoCore F).hom.app C)⟦(1 : ℤ)⟧') =
      Q.map (roosProductComparison F C) ≫
        Q.map (boundary ((roosTowerAction F).obj C)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Q.map_comp _ _).symm.trans
      ((congrArg Q.map (comparison_iso_projectionCore F C)).trans (Q.map_comp _ _))
  · intro n
    exact (congrArg Q.map (comparison_iso_evaluationCore F C n)).trans (Q.map_comp _ _)
  · exact (congrArg Q.map (comparison_iso_boundaryCore F C)).trans (Q.map_comp _ _)

end GenericComparison

attribute [local irreducible] comparison_isoCore roosF roosAdditiveComparison roosχ
  DerivedCategory.Q

set_option backward.defeqAttrib.useBackward false

private theorem pushforward_countable_limitsCore
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.pushforward.{v} φ) := by
  let V := SheafOfModules.forget.{v} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.pushforward.{v} φ ⋙ V) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      ((SheafOfModules.forget.{v} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{v}).obj F.op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℕ) V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ V

private theorem restriction_countable_limitsCore {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (restriction.{t, u, v} j R) := by
  exact pushforward_countable_limitsCore (𝟙 _)

private theorem complexRestriction_countable_limitsCore {X Y : Scheme.{t}} (j : Y ⟶ X)
    [IsOpenImmersion j] (R : Sheaf (topology X) RingCat.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (complexRestriction.{t, u, v} j R) := by
  have := restriction_countable_limitsCore.{t, u, v} j R
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro p
  change PreservesLimitsOfShape (Discrete ℕ)
    (HomologicalComplex.eval (Modules.{t, u, v} X R) (.up ℤ) p ⋙ restriction j R)
  infer_instance

private def productSectionsCore (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
    (C : Towers.{t, u, v} X R) (p : ℤ) (U : X.ProEt) :
    ((roosP C).X p).val.obj (op U) ≃+
      ∀ n : ℕ, (((C.X p).obj (op n)).val.obj (op U)) :=
  let E := HomologicalComplex.eval (Modules.{t, u, v} X R) (.up ℤ) p ⋙
    SheafOfModules.evaluation R (op U)
  (PreservesProduct.iso E (fun n : ℕ ↦ C.asFunctor.obj (op n)) ≪≫
    ModuleCat.piIsoPi (fun n : ℕ ↦ E.obj (C.asFunctor.obj (op n)))).toLinearEquiv.toAddEquiv

private theorem productSections_projectionCore (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (C : Towers.{t, u, v} X R)
    (p : ℤ) (U : X.ProEt) (x) (n : ℕ) :
    productSectionsCore X R C p U x n =
      ((Pi.π (fun n : ℕ ↦ C.asFunctor.obj (op n)) n).f p).val.app (op U) x := by
  let E := HomologicalComplex.eval (Modules.{t, u, v} X R) (.up ℤ) p ⋙
    SheafOfModules.evaluation R (op U)
  have h := ModuleCat.piIsoPi_hom_ker_subtype
    (fun n : ℕ ↦ E.obj (C.asFunctor.obj (op n))) n
  have hh := congrArg (fun f ↦ piComparison E (fun n : ℕ ↦ C.asFunctor.obj (op n)) ≫ f) h
  rw [piComparison_comp_π] at hh
  exact congrArg (fun f ↦ f x) hh

attribute [local irreducible] productSectionsCore

private def transposeAddEquivCore {J K : Type*} (P : J → K → Type*)
    [∀ i k, Add (P i k)] : (∀ i k, P i k) ≃+ ∀ k i, P i k :=
  { Equiv.piComm P with map_add' := fun _ _ ↦ rfl }

attribute [local instance] piPreadditive

private theorem transposeAddEquiv_applyCore {J K : Type*} (P : J → K → Type*)
    [∀ i k, Add (P i k)] (x : ∀ i k, P i k) (k : K) (i : J) :
    transposeAddEquivCore P x k i = x i k := rfl

attribute [local irreducible] transposeAddEquivCore

private def reindexAddEquiv {J : Type*} {K : Type*} (e : J ≃ K)
    (P : K → Type*) [∀ i, Add (P i)] : (∀ j, P (e j)) ≃+ ∀ i, P i :=
  { Equiv.piCongrLeft P e with
    map_add' := by
      intro x y
      funext i
      obtain ⟨a, rfl⟩ := e.surjective i
      simp [Equiv.piCongrLeft_apply_apply] }

private theorem reindexAddEquiv_apply {J : Type*} {K : Type*} (e : J ≃ K)
    (P : K → Type*) [∀ i, Add (P i)] (x : ∀ j, P (e j)) (a : J) :
    reindexAddEquiv e P x (e a) = x a := Equiv.piCongrLeft_apply_apply P e x a

private theorem map_cancel_iso {C D E : Type*}
    [Category C] [Category D] [Category E] {F G : C ⥤ D}
    (H : D ⥤ E) [H.Full] [H.Faithful] (α : F ⋙ H ≅ G ⋙ H) (X : C) :
    H.map ((Functor.fullyFaithfulCancelRight H α).hom.app X) = α.hom.app X := by
  rw [Functor.fullyFaithfulCancelRight_hom_app, H.map_preimage]

private def reindexRestriction {J K : Type*} (e : J ≃ K) (B : K → Type*)
    [∀ k, Category (B k)] : (∀ k, B k) ⥤ ∀ j, B (e j) :=
  Functor.pi' (fun j ↦ Pi.eval B (e j))

private def descendIso {C D E : Type*}
    [Category C] [Category D] [Category E] {F G : C ⥤ D}
    (H : D ⥤ E) [H.Full] [H.Faithful] (α : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  Functor.fullyFaithfulCancelRight H α

private theorem descendIso_map {C D E : Type*}
    [Category C] [Category D] [Category E] {F G : C ⥤ D}
    (H : D ⥤ E) [H.Full] [H.Faithful] (α : F ⋙ H ≅ G ⋙ H) (X : C) :
    H.map ((descendIso H α).hom.app X) = α.hom.app X :=
  map_cancel_iso H α X

attribute [local irreducible] descendIso reindexAddEquiv

private theorem reindexed_equivalence {A : Type*} [Category A]
    {J K : Type*} (e : J ≃ K) (B : K → Type*) [∀ k, Category (B k)]
    (F : ∀ k, A ⥤ B k) (G₀ : (∀ j, B (e j)) ⥤ A)
    (η₀ : 𝟭 A ≅ (Functor.pi' (fun j ↦ F (e j))) ⋙ G₀)
    (ε₀ : G₀ ⋙ (Functor.pi' (fun j ↦ F (e j))) ≅ 𝟭 _)
    (h₁ : ∀ M, (Functor.pi' (fun j ↦ F (e j))).map (η₀.hom.app M) ≫
      ε₀.hom.app ((Functor.pi' (fun j ↦ F (e j))).obj M) = 𝟙 _)
    (h₂ : ∀ M, η₀.hom.app (G₀.obj M) ≫ G₀.map (ε₀.hom.app M) = 𝟙 _) :
    ∃ ε : (reindexRestriction e B ⋙ G₀) ⋙ Functor.pi' F ≅ 𝟭 _,
      (∀ M, (Functor.pi' F).map (η₀.hom.app M) ≫ ε.hom.app ((Functor.pi' F).obj M) = 𝟙 _) ∧
      (∀ M, η₀.hom.app ((reindexRestriction e B ⋙ G₀).obj M) ≫
        (reindexRestriction e B ⋙ G₀).map (ε.hom.app M) = 𝟙 _) ∧
      (∀ M a, ε.hom.app M (e a) = ε₀.hom.app ((reindexRestriction e B).obj M) a) := by
  let P := Functor.pi' F
  let S := reindexRestriction e B
  have : S.Full := inferInstanceAs (Pi.equivalenceOfEquiv B e).inverse.Full
  have : S.Faithful := inferInstanceAs (Pi.equivalenceOfEquiv B e).inverse.Faithful
  let η : 𝟭 A ≅ P ⋙ (S ⋙ G₀) := η₀
  let ε : (S ⋙ G₀) ⋙ Functor.pi' F ≅ 𝟭 _ :=
    descendIso S (Functor.isoWhiskerLeft S ε₀)
  have hε (M) (a) : ε.hom.app M (e a) = ε₀.hom.app (S.obj M) a := by
    exact congrFun (descendIso_map (F := (S ⋙ G₀) ⋙ P) (G := 𝟭 _)
      S (Functor.isoWhiskerLeft S ε₀) M) a
  refine Exists.intro ε (And.intro ?_ (And.intro ?_ hε))
  · intro M
    apply S.map_injective
    funext a
    change (P.map (η₀.hom.app M)) (e a) ≫ ε.hom.app (P.obj M) (e a) = 𝟙 _
    rw [hε]
    exact congrFun (h₁ M) a
  · intro M
    change η₀.hom.app (G₀.obj (S.obj M)) ≫ G₀.map (S.map (ε.hom.app M)) = 𝟙 _
    rw [show S.map (ε.hom.app M) = ε₀.hom.app (S.obj M) from funext (hε M)]
    exact h₂ (S.obj M)

private theorem normalized_module_gluingCore
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hv : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) RingCat.{u})
    (hr : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ (G : (∀ i, Modules.{t, u, v} (Y i) (restrictedRing (j i) R)) ⥤ Modules.{t, u, v} X R)
      (η : 𝟭 _ ≅ Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R) ⋙ G)
      (ε : G ⋙ Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R) ≅ 𝟭 _),
      G.Additive ∧
      (∀ M, (Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R)).map (η.hom.app M) ≫
        ε.hom.app ((Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R)).obj M) = 𝟙 _) ∧
      (∀ M, η.hom.app (G.obj M) ≫ G.map (ε.hom.app M) = 𝟙 _) ∧
      ∃ σ : ∀ M U, (G.obj M).val.obj (op U) ≃+
        (∀ i, (M i).val.obj (op (clopenTestPiece (j i) U))),
        (∀ M U (a : R.obj.obj (op U)) x i,
          σ M U (a • x) i = R.obj.map (clopenTestInclusion (j i) U).op a • σ M U x i) ∧
        (∀ M (U V : X.ProEt) (f : V ⟶ U) x i,
          σ M V ((G.obj M).val.map f.op x) i =
            (M i).val.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j i)).map f).op
              (σ M U x i)) ∧
        (∀ M N (f : M ⟶ N) U x i,
          σ N U ((G.map f).val.app (op U) x) i =
            (f i).val.app (op (clopenTestPiece (j i) U)) (σ M U x i)) ∧
        (∀ M U x i, σ ((Functor.pi' (fun i ↦ restriction (j i) R)).obj M) U
          ((η.hom.app M).val.app (op U) x) i =
            M.val.map (clopenTestInclusion (j i) U).op x) ∧
        (∀ M i (W : (Y i).ProEt) x,
          ((ε.hom.app M) i).val.app (op W) x =
            (M i).val.map (clopenDiagonal (j i) W).op
              (σ M ((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale (j i))).obj W) x i)) := by
  let e : Shrink.{0} I ≃ I := (equivShrink.{0} I).symm
  let B (i : I) := Modules.{t, u, v} (Y i) (restrictedRing (j i) R)
  let S := reindexRestriction e B
  have hS : S.Additive := ⟨rfl⟩
  have : S.Full := inferInstanceAs (Pi.equivalenceOfEquiv B e).inverse.Full
  have : S.Faithful := inferInstanceAs (Pi.equivalenceOfEquiv B e).inverse.Faithful
  have hd' : Pairwise (fun a b ↦ Disjoint (Set.range (j (e a))) (Set.range (j (e b)))) :=
    fun a b hab ↦ hd (fun h ↦ hab (e.injective h))
  have hv' : ∀ x : X, ∃ a, x ∈ Set.range (j (e a)) := by
    intro x
    obtain ⟨i, hi⟩ := hv x
    obtain ⟨a, rfl⟩ := e.surjective i
    exact ⟨a, hi⟩
  obtain ⟨G₀, η₀, ε₀, _, _, hadd, _, _, _, _, h₁, h₂,
    ⟨σ₀, hs, hr₀, hm, hu, he⟩, _⟩ :=
    clopen_ringed_module_gluing.{t, u, v, 0, max v (t + 1), max v (t + 1), 0, 0}
      X (Shrink.{0} I) (fun a ↦ Y (e a)) (fun a ↦ j (e a)) hd' hv' R hr
  have : G₀.Additive := ⟨hadd _ _ _ _⟩
  let P := Functor.pi' (fun i ↦ restriction.{t, u, v} (j i) R)
  let G := S ⋙ G₀
  let η : 𝟭 _ ≅ P ⋙ G := η₀
  obtain ⟨ε, htriangle₁, htriangle₂, hε⟩ :=
    reindexed_equivalence e B (fun i ↦ restriction.{t, u, v} (j i) R)
      G₀ η₀ ε₀ h₁ h₂
  let σ (M : ∀ i, B i) (U : X.ProEt) :=
    (σ₀ (S.obj M) U).trans
      (reindexAddEquiv e (fun i ↦ (M i).val.obj (op (clopenTestPiece (j i) U))))
  have hσ (M : ∀ i, B i) (U : X.ProEt) (x) (a : Shrink.{0} I) :
      σ M U x (e a) = σ₀ (S.obj M) U x a := by
    change reindexAddEquiv e
      (fun i ↦ (M i).val.obj (op (clopenTestPiece (j i) U)))
        (σ₀ (S.obj M) U x) (e a) = _
    exact reindexAddEquiv_apply e
      (fun i ↦ (M i).val.obj (op (clopenTestPiece (j i) U))) (σ₀ (S.obj M) U x) a
  refine Exists.intro G (Exists.intro η (Exists.intro ε ?_))
  refine ⟨inferInstance, htriangle₁, htriangle₂, σ, ?_, ?_, ?_, ?_, ?_⟩
  · intro M U a x i
    obtain ⟨b, rfl⟩ := e.surjective i
    exact (hσ M U (a • x) b).trans ((hs (S.obj M) U a x b).trans
      (congrArg (fun z ↦ R.obj.map (clopenTestInclusion (j (e b)) U).op a • z)
        (hσ M U x b).symm))
  · intro M U V f x i
    obtain ⟨b, rfl⟩ := e.surjective i
    exact (hσ M V ((G.obj M).val.map f.op x) b).trans
      ((hr₀ (S.obj M) U V f x b).trans
        (congrArg (fun z ↦ (M (e b)).val.map
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (j (e b))).map f).op z)
            (hσ M U x b).symm))
  · intro M N f U x i
    obtain ⟨b, rfl⟩ := e.surjective i
    exact (hσ N U ((G.map f).val.app (op U) x) b).trans
      ((hm (S.obj M) (S.obj N) (S.map f) U x b).trans
        (congrArg (fun z ↦ (f (e b)).val.app (op (clopenTestPiece (j (e b)) U)) z)
          (hσ M U x b).symm))
  · intro M U x i
    obtain ⟨b, rfl⟩ := e.surjective i
    trans σ₀ (S.obj (P.obj M)) U ((η.hom.app M).val.app (op U) x) b
    · exact hσ (P.obj M) U _ b
    · exact hu M U x b
  · intro M i W x
    obtain ⟨a, rfl⟩ := e.surjective i
    exact (congrArg (fun f ↦ f.val.app (op W) x) (hε M a)).trans
      ((he (S.obj M) a W x).trans
        (congrArg (fun z ↦ (M (e a)).val.map (clopenDiagonal (j (e a)) W).op z)
          (hσ M _ x a).symm))


end ClopenRoos
end AlgebraicGeometry.Scheme.ProEt
