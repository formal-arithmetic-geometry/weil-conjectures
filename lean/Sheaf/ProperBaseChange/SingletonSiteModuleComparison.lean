/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q22 and Q78
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Module comparison for the punctual ringed site

Source: Stacks Project, sites.tex, Tag 00X9 (the punctual topos), and
sites-modules.tex, Tags 03DA, 03EK and 03CZ (blueprint:
lem-weil-pbc-singleton-site-module-comparison).

The punctual-site constructions are retained from the previously published module.
The comparison predicates now specify local pure tensors, naturality, universal
left-derived counits, and the adjunction-unit square. Derived morphisms use the standard
universe u+1; no existence of a localization in universe 0 is asserted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

/-- The one-object category used for the punctual site.

Source: Stacks Project, sites.tex, Tag 00X9 (blueprint:
lem-weil-pbc-singleton-site-module-comparison).
-/
abbrev singletonSite : Type := Discrete PUnit

/-- The punctual topology: its only covering sieve is the maximal sieve.

Source: Stacks Project, sites.tex, Tag 00X9 (blueprint:
lem-weil-pbc-singleton-site-module-comparison).
-/
def singletonTopology : GrothendieckTopology singletonSite := ⊥

/-- The constant ring sheaf on the punctual site.

Source: Stacks Project, sites.tex, Tag 00X9 (blueprint:
lem-weil-pbc-singleton-site-module-comparison).
-/
noncomputable def singletonRingSheaf (R : Type u) [CommRing R] :
    Sheaf singletonTopology CommRingCat.{u} :=
  { obj := (Functor.const singletonSiteᵒᵖ).obj (CommRingCat.of R)
    property := Presheaf.isSheaf_bot _ }

/-- The value of the constant ring sheaf at the unique object.

Source: Stacks Project, sites.tex, Tag 00X9 (blueprint:
lem-weil-pbc-singleton-site-module-comparison).
-/
abbrev singletonRingValue (R : Type u) [CommRing R] : Type u := R

/-- The sheaf-of-modules category on the punctual ring sheaf (source: Tag 03DA;
blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
abbrev singletonModuleCategory (R : Type u) [CommRing R] :=
    ringedSiteModules.{u} ((sheafCompose singletonTopology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf R))

/-- Evaluation at the unique punctual object (source: Tag 00X9; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable abbrev singletonEvaluation (R : Type u) [CommRing R] :
    singletonModuleCategory R ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation
    ((sheafCompose singletonTopology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf R))
    (op (⟨PUnit.unit⟩ : singletonSite))

/-- Evaluation preserves zero morphisms (source: Tag 03DA; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
instance singletonEvaluationPreservesZeroMorphisms (R : Type u) [CommRing R] :
    (singletonEvaluation R).PreservesZeroMorphisms := by
  constructor
  intro X Y
  rfl

/-- Evaluation is additive (source: Tag 03DA; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
instance singletonEvaluationAdditive (R : Type u) [CommRing R] :
    (singletonEvaluation R).Additive := by
  constructor
  intro X Y f g
  rfl

/-- The constant ring map induced by a homomorphism of rings.

Source: Stacks Project, sites-modules.tex, Tag 03CZ (blueprint:
lem-weil-pbc-singleton-site-module-comparison).
-/
noncomputable def singletonRingMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : singletonRingSheaf R ⟶ singletonRingSheaf S :=
  { hom := { app := fun _ => CommRingCat.ofHom φ
             naturality := by intros; rfl } }

/-- The constant module presheaf, regarded as a module sheaf on the punctual site.

Source: Stacks Project, sites-modules.tex, Tags 03DA and 03CZ (blueprint:
lem-weil-pbc-singleton-site-module-comparison).
-/
noncomputable def singletonConstantModuleSheaf (R : Type u) [CommRing R] :
    ModuleCat.{u} (singletonRingValue R) ⥤
      SheafOfModules.{u} ((sheafCompose singletonTopology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf R)) where
  obj M :=
    { val :=
        { obj := fun _ => M
          map := fun f => (ModuleCat.restrictScalars (RingHom.id _)).map (𝟙 M) }
      isSheaf := Presheaf.isSheaf_bot _ }
  map f :=
    { val := { app := fun _ => f } }

/-- Sectionwise sheaf scalar extension object (source: Tag 03EK; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonSheafExtensionObj {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : singletonModuleCategory R) : singletonModuleCategory S :=
  SheafOfModules.changeOfRings.{0, 0, u}
    (R₁ := singletonRingSheaf R) (R₂ := singletonRingSheaf S)
    (singletonRingMap (R := R) (S := S) φ) M

/-- Sectionwise sheaf scalar extension map (source: Tag 03EK; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonSheafExtensionMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M N : singletonModuleCategory R} (f : M ⟶ N) :
    singletonSheafExtensionObj φ M ⟶ singletonSheafExtensionObj φ N :=
  SheafOfModules.changeOfRingsHom.{0, 0, u}
    (R₁ := singletonRingSheaf R) (R₂ := singletonRingSheaf S)
    (singletonRingMap (R := R) (S := S) φ) M f

/-- Restriction of scalars on punctual sheaf modules (source: Tag 03CZ; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonSheafRestriction {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : singletonModuleCategory S ⥤ singletonModuleCategory R :=
  SheafOfModules.restrictScalars
    ((sheafCompose singletonTopology
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (singletonRingMap (R := R) (S := S) φ))

/-- Restriction is additive by the existing Mathlib restriction functor.
Source: Stacks Tag 03CZ (blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable instance singletonRestrictionAdditive {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : (singletonSheafRestriction φ).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars
    ((sheafCompose singletonTopology (forget₂ CommRingCat.{u} RingCat.{u})).map
      (singletonRingMap φ))).Additive

/-- The ordinary extension functor is additive by its tensor/restriction adjunction.
Source: Stacks Tag 03CZ (blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable instance singletonExtendScalarsAdditive {R S : Type u}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).left_adjoint_additive

/-- The ordinary scalar-extension unit map (source: Tag 03CZ; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonOrdinaryUnitMap {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) :
    M ⟶ (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M) := by
  letI : Module R S := Module.compHom S φ
  exact (ModuleCat.ExtendRestrictScalarsAdj.unit φ).app M

/-- The unit is `m ↦ 1 ⊗ m` (source: Tag 03CZ; blueprint:
lem-weil-pbc-singleton-site-module-comparison). -/
def singletonOrdinaryUnitFormula {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  letI : Module R S := Module.compHom S φ
  ∀ (M : ModuleCat.{u} R) (m : M),
    singletonOrdinaryUnitMap φ M m = TensorProduct.tmul R (1 : S) m

/-- The tensor comparison is natural in both variables and sends each local pure tensor
back to that same tensor. Source: Stacks Tag 03EK
(blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
def singletonTensorComparison (R : Type u) [CommRing R] : Prop :=
  ∃ t : ∀ M N : singletonModuleCategory R,
      (singletonEvaluation R).obj ((SheafOfModules.siteSheafTensorRight N).obj M) ≅
        MonoidalCategory.tensorObj ((singletonEvaluation R).obj M)
          ((singletonEvaluation R).obj N),
    (∀ (M N : singletonModuleCategory R) (x : (singletonEvaluation R).obj M)
      (y : (singletonEvaluation R).obj N),
      (t M N).hom (SheafOfModules.siteSheafTensorTmul M N
        (op (⟨PUnit.unit⟩ : singletonSite)) x y) = x ⊗ₜ[R] y) ∧
    (∀ {M M' N N' : singletonModuleCategory R} (f : M ⟶ M') (g : N ⟶ N'),
      (singletonEvaluation R).map
          ((SheafOfModules.siteSheafTensorRight N).map f ≫
            SheafOfModules.siteSheafTensorSecondMap M' g) ≫ (t M' N').hom =
        (t M N).hom ≫ MonoidalCategory.tensorHom
          ((singletonEvaluation R).map f) ((singletonEvaluation R).map g))

/-- The section of a scalar extension represented by `s ⊗ x`.
Source: Stacks Tags 03EK and 03CZ
(blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonExtensionTmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : singletonModuleCategory R) (s : S)
    (x : (singletonEvaluation R).obj M) :
    (singletonEvaluation S).obj (singletonSheafExtensionObj φ M) :=
  (CategoryTheory.toSheafify singletonTopology
    (SheafOfModules.changeOfRingsPresheaf (singletonRingMap φ) M).presheaf).app
      (op (⟨PUnit.unit⟩ : singletonSite)) (s ⊗ₜ[R, φ] x)

/-- Scalar comparison, fixed by pure tensors, unchanged restricted sections, and the
ordinary unit. Source: Stacks Tag 03CZ
(blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
def singletonScalarUnitCompatible {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (E : singletonModuleCategory R ⥤ singletonModuleCategory S)
    (h : ∀ M, E.obj M = singletonSheafExtensionObj φ M)
    (s : E ⋙ singletonEvaluation S ≅ singletonEvaluation R ⋙ ModuleCat.extendScalars φ)
    (r : singletonSheafRestriction φ ⋙ singletonEvaluation R ≅
      singletonEvaluation S ⋙ ModuleCat.restrictScalars φ)
    (a : E ⊣ singletonSheafRestriction φ) : Prop :=
  (∀ (M : singletonModuleCategory R) (b : S) (x : (singletonEvaluation R).obj M),
    (s.hom.app M) ((singletonEvaluation S).map (eqToHom (h M).symm)
      (singletonExtensionTmul φ M b x)) = b ⊗ₜ[R, φ] x) ∧
  (∀ (N : singletonModuleCategory S) (y : (singletonEvaluation S).obj N),
    r.hom.app N y = y) ∧
  (∀ M : singletonModuleCategory R,
    (singletonEvaluation R).map (a.unit.app M) ≫ r.hom.app (E.obj M) ≫
        (ModuleCat.restrictScalars φ).map (s.hom.app M) =
      singletonOrdinaryUnitMap φ ((singletonEvaluation R).obj M))

/-- Derived evaluation with its specified localization comparison. The localization
universe is explicit; no small-Hom assumption is imposed.
Source: Stacks Tag 05RU (blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
def singletonDerivedLocalizationCompatible (R : Type u) [CommRing R]
    (hR : HasDerivedCategory.{u + 1} (singletonModuleCategory R))
    (hM : HasDerivedCategory.{u + 1} (ModuleCat.{u} R)) : Prop :=
  ∃ D : DerivedCategory (singletonModuleCategory R) ≌ DerivedCategory (ModuleCat.{u} R),
    Nonempty (DerivedCategory.Qh ⋙ D.functor ≅
      (singletonEvaluation R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

section DerivedScalars

variable {R S : Type u} [CommRing R] [CommRing S]
  (φ : R →+* S) (E : singletonModuleCategory R ⥤ singletonModuleCategory S) [E.Additive]
  (s : E ⋙ singletonEvaluation S ≅ singletonEvaluation R ⋙ ModuleCat.extendScalars φ)
  (r : singletonSheafRestriction φ ⋙ singletonEvaluation R ≅
    singletonEvaluation S ⋙ ModuleCat.restrictScalars φ)
  [HasDerivedCategory.{u + 1} (singletonModuleCategory R)]
  [HasDerivedCategory.{u + 1} (singletonModuleCategory S)]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u} S)]

/-- The homotopy scalar-extension comparison induced by the given ordinary comparison.
Source: Stacks Tags 03CZ and 05RN
(blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonExtensionHomotopyComparison :
    E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (singletonEvaluation S).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (singletonEvaluation R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso s (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (singletonEvaluation R ⋙ ModuleCat.extendScalars φ))
      (ComplexShape.up ℤ)).symm

/-- The homotopy restriction comparison induced by the given ordinary comparison.
Source: Stacks Tags 03CZ and 05RN
(blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
noncomputable def singletonRestrictionHomotopyComparison :
    (singletonSheafRestriction φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (singletonEvaluation R).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (singletonEvaluation S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (ModuleCat.restrictScalars φ).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso r (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (singletonEvaluation S ⋙ ModuleCat.restrictScalars φ))
      (ComplexShape.up ℤ)).symm

/-- The full derived comparison. Both left derived pairs have their universal counits;
the comparison intertwines those counits and the degreewise scalar comparison.
The restriction comparison is the localization of the ordinary restriction comparison,
and the final equation identifies the two adjunction units at every derived object.
On each K-flat representative the sheaf derived unit is the localized degreewise unit of
the given sheaf adjunction `a`, and the ordinary derived unit is the localized degreewise
`x ↦ 1 ⊗ x`. Thus this records the actual K-flat computation and its normalized unit,
including non-K-flat objects through any K-flat resolution.
Source: Stacks Tags 06YN, 06YS, 06YT, 06YY and 07A6
(blueprint: lem-weil-pbc-singleton-site-module-comparison). -/
def singletonDerivedScalarComparison (a : E ⊣ singletonSheafRestriction φ) : Prop :=
  ∃ (_ : PreservesFiniteLimits (singletonSheafRestriction φ))
    (_ : PreservesFiniteColimits (singletonSheafRestriction φ)),
  ∃ (DR : DerivedCategory (singletonModuleCategory R) ≌ DerivedCategory (ModuleCat.{u} R))
    (DS : DerivedCategory (singletonModuleCategory S) ≌ DerivedCategory (ModuleCat.{u} S))
    (kR : DerivedCategory.Qh ⋙ DR.functor ≅
      (singletonEvaluation R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (kS : DerivedCategory.Qh ⋙ DS.functor ≅
      (singletonEvaluation S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (LS : DerivedCategory (singletonModuleCategory R) ⥤
      DerivedCategory (singletonModuleCategory S))
    (eS : DerivedCategory.Qh ⋙ LS ⟶
      E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (LM : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (eM : DerivedCategory.Qh ⋙ LM ⟶
      (ModuleCat.extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (c : DR.functor ⋙ LM ≅ LS ⋙ DS.functor)
    (b : (singletonSheafRestriction φ).mapDerivedCategory ⋙ DR.functor ≅
      DS.functor ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (aS : LS ⊣ (singletonSheafRestriction φ).mapDerivedCategory)
    (aM : LM ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory),
    LS.IsLeftDerivedFunctor eS
        (HomotopyCategory.quasiIso (singletonModuleCategory R) (ComplexShape.up ℤ)) ∧
    LM.IsLeftDerivedFunctor eM
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) ∧
    (∀ P : CochainComplex (singletonModuleCategory R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (J := singletonTopology) (R := singletonRingSheaf R) P →
      IsIso (eS.app ((HomotopyCategory.quotient _ _).obj P)) ∧
      IsIso (eM.app (((singletonEvaluation R).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)))) ∧
    (∀ H : HomotopyCategory (singletonModuleCategory R) (ComplexShape.up ℤ),
      LM.map (kR.hom.app H) ≫
          eM.app (((singletonEvaluation R).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) =
        c.hom.app (DerivedCategory.Qh.obj H) ≫ DS.functor.map (eS.app H) ≫
          kS.hom.app ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
          DerivedCategory.Qh.map ((singletonExtensionHomotopyComparison φ E s).hom.app H)) ∧
    (∀ H : HomotopyCategory (singletonModuleCategory S) (ComplexShape.up ℤ),
      b.hom.app (DerivedCategory.Qh.obj H) =
        DR.functor.map ((singletonSheafRestriction φ).mapDerivedCategoryFactorsh.hom.app H) ≫
          kR.hom.app (((singletonSheafRestriction φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj H) ≫
          DerivedCategory.Qh.map ((singletonRestrictionHomotopyComparison φ r).hom.app H) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv.app
            (((singletonEvaluation S).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategory.map (kS.inv.app H)) ∧
    (∀ P : CochainComplex (singletonModuleCategory R) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (J := singletonTopology) (R := singletonRingSheaf R) P →
      aS.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          (singletonSheafRestriction φ).mapDerivedCategory.map
            (eS.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (singletonSheafRestriction φ).mapDerivedCategoryFactorsh.hom.app
            ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) =
        DerivedCategory.Qh.map
          ((a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
            ((HomotopyCategory.quotient _ _).obj P))) ∧
    (∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).kFlat P →
      aM.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategory.map
            (eM.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.hom.app
            (((ModuleCat.extendScalars φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) =
        DerivedCategory.Qh.map
          (((ModuleCat.extendRestrictScalarsAdj φ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ _).obj P))) ∧
    (∀ K : DerivedCategory (singletonModuleCategory R),
      DR.functor.map (aS.unit.app K) ≫ b.hom.app (LS.obj K) =
        aM.unit.app (DR.functor.obj K) ≫
          (ModuleCat.restrictScalars φ).mapDerivedCategory.map (c.hom.app K))

end DerivedScalars

/-- Evaluation is the exact tensor equivalence from the punctual ringed site to ordinary
modules. Scalar extension, restriction and their units agree, as do complexes, homotopy
categories, localization, quasi-isomorphisms, K-flatness and normalized derived change of rings.

Source: Stacks, sites.tex Tag 00X9; sites-modules.tex Tags 03DA, 03EK, 03CZ;
sites-cohomology.tex Tags 06YN, 06YS, 06YT, 06YY, 07A6
(blueprint: lem-weil-pbc-singleton-site-module-comparison).

Proof (the ten steps of the DAG):
1. Every presheaf is a sheaf for the bottom topology. Evaluation and the constant presheaf
are inverse by the identity maps at the sole object (def-weil-sheaf-of-modules-category).
2. Kernels, cokernels and direct sums are computed at that object; hence evaluation is exact.
3. The sectionwise tensor presheaf is already a sheaf. Its sheafification unit identifies
its pure tensors with ordinary pure tensors (def-pur-sheaf-tensor-product and
 def-weil-presheaf-modules-sheafification), giving the natural tensor comparison.
4. Restriction changes only the scalar action. Extension has value S tensor_R M.
The adjunction sends a map u to x mapped to u(1 tensor x), with inverse transpose
s tensor x mapped to s v(x); hence the comparison identifies the specified unit.
5. Apply evaluation and the inverse in every degree. The chain-map and homotopy equations
are unchanged, giving the complex and homotopy equivalences.
6. Evaluation identifies kernels, images and quotients, hence cohomology and quasi-isomorphisms.
7. Apply lem-weil-pbc-exact-functor-derived-factorization in both directions and descend
the inverse isomorphisms by the fully faithful localization universal property. Use the
standard localization universe u+1, without imposing a small-Hom condition.
8. Direct sums and tensor products agree under evaluation, including the total-tensor
sign (-1)^p. The two acyclic-tensor tests therefore agree (def-pc-kflat-complex).
9. Resolve by lem-pc-kflat-resolution and apply lem-pur-derived-change-of-rings.
The ordinary and sheaf extension homotopy functors correspond by the degreewise comparison;
universality transports their left derived pairs and their counits. On a K-flat object the
counit is invertible; for a resolution q, compose it with the inverse image of q. This gives
canonical comparisons independent of resolution and compatible with maps.
10. Apply lem-pur-sheaf-ring-derived-coefficient-adjunction. Its normalized unit on a
K-flat representative is the localized degreewise sheaf unit `x ↦ x ⊗ 1`; the ordinary
normalized unit is the localized degreewise ordinary unit. Evaluation preserves this map
and its transpose (step 4).
Naturality transports the normalization from a K-flat resolution to every derived object;
the displayed unit square expresses exactly this compatibility. -/
theorem singleton_site_module_comparison (R : Type u) [CommRing R] :
    ∃ e : singletonModuleCategory R ≌ ModuleCat.{u} R,
      e.functor = singletonEvaluation R ∧
      e.inverse = singletonConstantModuleSheaf (R := R) ∧
      (∀ T : ShortComplex (singletonModuleCategory R),
        T.ShortExact → (T.map e.functor).ShortExact) ∧
      singletonTensorComparison R ∧
      (∃ E : CochainComplex (singletonModuleCategory R) ℤ ≌ CochainComplex (ModuleCat.{u} R) ℤ,
        E.functor = (singletonEvaluation R).mapHomologicalComplex (ComplexShape.up ℤ)) ∧
      (∃ E : HomotopyCategory (singletonModuleCategory R) (ComplexShape.up ℤ) ≌
          HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ),
        E.functor = (singletonEvaluation R).mapHomotopyCategory (ComplexShape.up ℤ)) ∧
      (∀ {K L : CochainComplex (singletonModuleCategory R) ℤ} (f : K ⟶ L),
        QuasiIso f ↔ QuasiIso (((singletonEvaluation R).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)) ∧
      (∃ (hR : HasDerivedCategory.{u + 1} (singletonModuleCategory R))
        (hM : HasDerivedCategory.{u + 1} (ModuleCat.{u} R)),
        singletonDerivedLocalizationCompatible R hR hM) ∧
      (∀ K : CochainComplex (singletonModuleCategory R) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
            (J := singletonTopology) (R := singletonRingSheaf R) K ↔
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).kFlat
            (((singletonEvaluation R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ∧
      (∀ (S : Type u) [CommRing S] (φ : R →+* S),
        ∃ (E : singletonModuleCategory R ⥤ singletonModuleCategory S)
          (h : ∀ M, E.obj M = singletonSheafExtensionObj φ M)
          (_ : ∀ {M N} (f : M ⟶ N), E.map f =
            eqToHom (h M) ≫ singletonSheafExtensionMap φ f ≫ eqToHom (h N).symm)
          (_ : E.Additive)
          (s : E ⋙ singletonEvaluation S ≅ singletonEvaluation R ⋙ ModuleCat.extendScalars φ)
          (r : singletonSheafRestriction φ ⋙ singletonEvaluation R ≅
            singletonEvaluation S ⋙ ModuleCat.restrictScalars φ)
          (a : E ⊣ singletonSheafRestriction φ),
          singletonScalarUnitCompatible φ E h s r a ∧ singletonOrdinaryUnitFormula φ ∧
          ∃ (_ : HasDerivedCategory.{u + 1} (singletonModuleCategory R))
            (_ : HasDerivedCategory.{u + 1} (singletonModuleCategory S))
            (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u} R))
            (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u} S)),
            singletonDerivedScalarComparison φ E s r a) := by
  sorry

end CategoryTheory
