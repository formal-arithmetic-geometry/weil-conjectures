/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
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
import all WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import all WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
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
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
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

set_option backward.defeqAttrib.useBackward true

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

private def comparison_isoCore [PreservesLimitsOfShape (Discrete ℕ) F] :
    roosF ⋙ F.mapHomologicalComplex (.up ℤ) ≅ roosTowerAction F ⋙ roosF := by
  have (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (roosAdditiveComparison F C) :=
    roosAdditiveComparison_isIso F C
  exact NatIso.ofComponents (fun C ↦ asIso (roosAdditiveComparison F C))
    (fun f ↦ roosAdditiveComparison_natural F f)

end GenericComparison

attribute [local irreducible] comparison_isoCore roosF roosAdditiveComparison roosχ
  DerivedCategory.Q

set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] productSectionsCore

attribute [local instance] piPreadditive

attribute [local irreducible] transposeAddEquivCore

private def descendIso {C D E : Type*}
    [Category C] [Category D] [Category E] {F G : C ⥤ D}
    (H : D ⥤ E) [H.Full] [H.Faithful] (α : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  Functor.fullyFaithfulCancelRight H α

attribute [local irreducible] descendIso reindexAddEquiv

end ClopenRoos
end AlgebraicGeometry.Scheme.ProEt
