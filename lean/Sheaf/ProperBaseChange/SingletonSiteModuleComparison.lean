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
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.CategoryTheory.NormalizedDerivedAdjunctionTransport
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
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

set_option backward.isDefEq.respectTransparency.types false

private theorem punctualSheafificationUnit_isIso (R : Type u) [CommRing R]
    (P : PresheafOfModules.{u}
      ((singletonRingSheaf R).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{u}
      (R := (sheafCompose singletonTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (singletonRingSheaf R)) (𝟙 _)).unit.app P) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _),
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact isIso_toSheafify singletonTopology (Presheaf.isSheaf_bot _)

private noncomputable def punctualTensorIso (R : Type u) [CommRing R]
    (M N : singletonModuleCategory R) :
    (singletonEvaluation R).obj ((SheafOfModules.siteSheafTensorRight N).obj M) ≅
      MonoidalCategory.tensorObj ((singletonEvaluation R).obj M)
        ((singletonEvaluation R).obj N) := by
  let P := SheafOfModules.siteTensorPresheaf M.val N.val
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (R := (sheafCompose singletonTopology (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (singletonRingSheaf R)) (𝟙 _)).unit.app P
  let : IsIso η := punctualSheafificationUnit_isIso R P
  exact ((PresheafOfModules.evaluation _ (op (⟨PUnit.unit⟩ : singletonSite))).mapIso
    (asIso η)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem punctualTensorComparison (R : Type u) [CommRing R] :
    singletonTensorComparison R := by
  refine ⟨punctualTensorIso R, ?_, ?_⟩
  · intro M N x y
    exact ConcreteCategory.congr_hom
      (Iso.inv_hom_id (punctualTensorIso R M N)) (x ⊗ₜ[R] y)
  · intro M M' N N' f g
    apply (cancel_epi (punctualTensorIso R M N).inv).1
    apply (cancel_mono (punctualTensorIso R M' N').inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id]
    let a := PresheafOfModules.sheafificationAdjunction.{u}
      (R := (sheafCompose singletonTopology
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf R)) (𝟙 _)
    have hn := a.unit.naturality
      ((SheafOfModules.siteTensorRight N.val).map f.val ≫
        SheafOfModules.siteTensorSecondMap M'.val g.val)
    convert congrArg (fun k ↦ k.app (op (⟨PUnit.unit⟩ : singletonSite))) hn.symm
      using 1
    · rfl
    · simp only [Functor.map_comp, PresheafOfModules.comp_app,
        SheafOfModules.siteSheafTensorRight, Functor.comp_map]
      rfl
    · apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      rfl

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def punctualEvaluationMonoidal (R : Type u) [CommRing R] :
    (singletonEvaluation R).Monoidal := by
  let A := (sheafCompose singletonTopology
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf R)
  let a := PresheafOfModules.sheafificationAdjunction.{u} (R := A) (𝟙 _)
  let : ∀ P, IsIso (a.unit.app P) := fun P ↦ punctualSheafificationUnit_isIso R P
  let : IsIso a.unit := NatIso.isIso_of_isIso_app a.unit
  let e := a.toEquivalence
  let : e.functor.Monoidal := by
    change (PresheafOfModules.sheafification.{u} (R := A) (𝟙 _)).Monoidal
    infer_instance
  letI := e.inverseMonoidal
  let V := PresheafOfModules.evaluation.{u} A.obj (op (⟨PUnit.unit⟩ : singletonSite))
  letI : V.Monoidal := Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by intros; simp only [Iso.refl_hom,
        Category.comp_id, Category.id_comp]; rfl
      μIso_hom_natural_right := by intros; simp only [Iso.refl_hom,
        Category.comp_id, Category.id_comp]; rfl
      associativity := by intros; simp; rfl
      left_unitality := by intros; simp; rfl
      right_unitality := by intros; simp; rfl }
  exact Functor.Monoidal.transport
    (NatIso.ofComponents (F := e.inverse ⋙ V) (G := singletonEvaluation R)
      (fun _ ↦ Iso.refl _) (by intros; rfl))

attribute [local irreducible] punctualEvaluationMonoidal

private noncomputable def punctualComponent (R : Type u) [CommRing R]
    (M : singletonModuleCategory R) (X : singletonSiteᵒᵖ) :
    M.val.obj X ≅ ((singletonEvaluation R ⋙ singletonConstantModuleSheaf R).obj M).val.obj X := by
  rcases X with ⟨⟨⟨⟩⟩⟩
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def punctualUnit (R : Type u) [CommRing R] :
    𝟭 (singletonModuleCategory R) ≅ singletonEvaluation R ⋙ singletonConstantModuleSheaf R := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let i := PresheafOfModules.isoMk (punctualComponent R M) (by
      intro X Y f
      rcases X with ⟨⟨⟨⟩⟩⟩
      rcases Y with ⟨⟨⟨⟩⟩⟩
      rw [show f = 𝟙 _ from Subsingleton.elim _ _]
      ext x
      simp)
    exact
      { hom := ⟨i.hom⟩
        inv := ⟨i.inv⟩
        hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
        inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }
  · intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    rcases X with ⟨⟨⟨⟩⟩⟩
    rfl

private noncomputable def punctualEquivalence (R : Type u) [CommRing R] :
    singletonModuleCategory R ≌ ModuleCat.{u} R where
  functor := singletonEvaluation R
  inverse := singletonConstantModuleSheaf R
  unitIso := punctualUnit R
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  functor_unitIso_comp M := by
    change ((punctualUnit R).hom.app M).val.app _ ≫ 𝟙 _ = 𝟙 _
    rfl

private theorem punctualEvaluationIsEquivalence (R : Type u) [CommRing R] :
    (singletonEvaluation R).IsEquivalence := (punctualEquivalence R).isEquivalence_functor

private noncomputable def punctualComplexEquivalence (R : Type u) [CommRing R] :
    CochainComplex (singletonModuleCategory R) ℤ ≌ CochainComplex (ModuleCat.{u} R) ℤ :=
  (punctualEquivalence R).mapHomologicalComplex (.up ℤ)

private theorem punctualComplexEquivalence_functor (R : Type u) [CommRing R] :
    (punctualComplexEquivalence R).functor =
      (singletonEvaluation R).mapHomologicalComplex (.up ℤ) := rfl

attribute [local irreducible] punctualComplexEquivalence

private theorem punctualAcyclic (R : Type u) [CommRing R]
    (K : CochainComplex (singletonModuleCategory R) ℤ) :
    (((singletonEvaluation R).mapHomologicalComplex (.up ℤ)).obj K).Acyclic ↔ K.Acyclic := by
  let : (singletonEvaluation R).IsEquivalence := punctualEvaluationIsEquivalence R
  simp only [HomologicalComplex.acyclic_iff, HomologicalComplex.exactAt_iff]
  exact forall_congr' fun n ↦ (K.sc n).exact_map_iff_of_faithful (singletonEvaluation R)

private theorem moduleKFlat_iff_tensorAcyclic (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K ↔
      ∀ F : CochainComplex (ModuleCat.{u} R) ℤ, F.Acyclic →
        (CochainComplex.mapBifunctor F K (MonoidalCategory.curriedTensor _)).Acyclic := by
  constructor
  · intro h F hF
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at h
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).2 hF)).2
  · intro h
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro F hF
    obtain ⟨F, rfl⟩ := F.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hF
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor F K (MonoidalCategory.curriedTensor _))).2 (h F hF)
    exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso
      (BraidedCategory.braiding _ _) hr, hr⟩

private noncomputable def punctualTotalTensorIso (R : Type u) [CommRing R]
    (K L : CochainComplex (singletonModuleCategory R) ℤ) :
    ((singletonEvaluation R).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor K L (MonoidalCategory.curriedTensor _)) ≅
      CochainComplex.mapBifunctor
        (((singletonEvaluation R).mapHomologicalComplex (.up ℤ)).obj K)
        (((singletonEvaluation R).mapHomologicalComplex (.up ℤ)).obj L)
        (MonoidalCategory.curriedTensor _) := by
  let : (singletonEvaluation R).IsEquivalence := punctualEvaluationIsEquivalence R
  let : (singletonEvaluation R).Monoidal := punctualEvaluationMonoidal R
  exact asIso (HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans (singletonEvaluation R)) (.up ℤ) K L)

attribute [local irreducible] punctualTotalTensorIso

set_option backward.isDefEq.respectTransparency false in
private theorem punctualKFlat (R : Type u) [CommRing R]
    (K : CochainComplex (singletonModuleCategory R) ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients
        (J := singletonTopology) (R := singletonRingSheaf R) K ↔
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
        (((singletonEvaluation R).mapHomologicalComplex (.up ℤ)).obj K) := by
  let : (singletonEvaluation R).IsEquivalence := punctualEvaluationIsEquivalence R
  let ec := punctualComplexEquivalence R
  have he : ec.functor = (singletonEvaluation R).mapHomologicalComplex (.up ℤ) :=
    punctualComplexEquivalence_functor R
  rw [moduleKFlat_iff_tensorAcyclic]
  constructor
  · intro h F hF
    let L := ec.inverse.obj F
    let q : ((singletonEvaluation R).mapHomologicalComplex (.up ℤ)).obj L ≅ F :=
      (eqToIso (congrArg (fun G ↦ G.obj L) he)).symm ≪≫ ec.counitIso.app F
    have hL : L.Acyclic := (punctualAcyclic R L).1
      (fun n ↦ (hF n).of_iso q.symm)
    have ht := (punctualAcyclic R _).2 (h L hL)
    let i := punctualTotalTensorIso R L K ≪≫
      (((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)).mapIso q).app _
    exact fun n ↦ (ht n).of_iso i
  · intro h F hF
    have ht := h _ ((punctualAcyclic R F).2 hF)
    exact (punctualAcyclic R _).1
      (fun n ↦ (ht n).of_iso (punctualTotalTensorIso R F K).symm)

private noncomputable def punctualExtensionPresheaf
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    singletonModuleCategory R ⥤ PresheafOfModules.{u}
      ((singletonRingSheaf S).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) where
  obj M := SheafOfModules.changeOfRingsPresheaf.{0, 0, u} (singletonRingMap φ) M
  map f :=
    { app := fun U ↦ (ModuleCat.extendScalars ((singletonRingMap φ).hom.app U).hom).map
        (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality (singletonRingMap φ) _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars ((singletonRingMap φ).hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars ((singletonRingMap φ).hom.app U).hom).map_comp _ _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def punctualExtensionComparison
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (E : singletonModuleCategory R ⥤ singletonModuleCategory S)
    (h : ∀ M, E.obj M = singletonSheafExtensionObj φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ singletonSheafExtensionMap φ f ≫ eqToHom (h N).symm) :
    E ⋙ singletonEvaluation S ≅ singletonEvaluation R ⋙ ModuleCat.extendScalars φ := by
  let A := (sheafCompose singletonTopology
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf S)
  let a := PresheafOfModules.sheafificationAdjunction.{u} (R := A) (𝟙 _)
  let P := punctualExtensionPresheaf φ
  let T := PresheafOfModules.sheafification.{u} (R := A) (𝟙 _)
  let i : E ≅ P ⋙ T := NatIso.ofComponents (fun M ↦ eqToIso (h M)) (by
    intro M N f
    change E.map f ≫ eqToHom (h N) = eqToHom (h M) ≫ singletonSheafExtensionMap φ f
    rw [hm]
    simp)
  let : ∀ M, IsIso ((Functor.whiskerLeft P a.unit).app M) :=
    fun M ↦ punctualSheafificationUnit_isIso S (P.obj M)
  let : IsIso (Functor.whiskerLeft P a.unit) := NatIso.isIso_of_isIso_app _
  let j := Functor.isoWhiskerRight (asIso (Functor.whiskerLeft P a.unit))
    (PresheafOfModules.evaluation _ (op (⟨PUnit.unit⟩ : singletonSite)))
  exact Functor.isoWhiskerRight i (singletonEvaluation S) ≪≫
    NatIso.ofComponents (fun M ↦ (j.app M).symm) (by
      intro M N f
      exact j.inv.naturality f)

private noncomputable def punctualRestrictionComparison
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    singletonSheafRestriction φ ⋙ singletonEvaluation R ≅
      singletonEvaluation S ⋙ ModuleCat.restrictScalars φ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem punctualExtensionComparison_tmul
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (E : singletonModuleCategory R ⥤ singletonModuleCategory S)
    (h : ∀ M, E.obj M = singletonSheafExtensionObj φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ singletonSheafExtensionMap φ f ≫ eqToHom (h N).symm)
    (M : singletonModuleCategory R) (b : S) (x : (singletonEvaluation R).obj M) :
    ((punctualExtensionComparison φ E h hm).hom.app M)
        ((singletonEvaluation S).map (eqToHom (h M).symm)
          (singletonExtensionTmul φ M b x)) = b ⊗ₜ[R, φ] x := by
  let A := (sheafCompose singletonTopology
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (singletonRingSheaf S)
  let a := PresheafOfModules.sheafificationAdjunction.{u} (R := A) (𝟙 _)
  let P := (punctualExtensionPresheaf φ).obj M
  let : IsIso (a.unit.app P) := punctualSheafificationUnit_isIso S P
  let j : (ModuleCat.extendScalars φ).obj ((singletonEvaluation R).obj M) ≅
      (singletonEvaluation S).obj (singletonSheafExtensionObj φ M) :=
    (PresheafOfModules.evaluation _ (op (⟨PUnit.unit⟩ : singletonSite))).mapIso
      (asIso (a.unit.app P))
  have ht := ConcreteCategory.congr_hom (Iso.hom_inv_id j) (b ⊗ₜ[R, φ] x)
  have heq : (singletonEvaluation S).map (eqToHom (h M).symm) ≫
      (punctualExtensionComparison φ E h hm).hom.app M = j.inv := by
    simp only [punctualExtensionComparison, j, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Iso.symm_hom,
      Functor.mapIso_inv, asIso_inv]
    rw [← Functor.map_comp_assoc]
    simp
    rfl
  have hv := ConcreteCategory.congr_hom heq (singletonExtensionTmul φ M b x)
  refine hv.trans ?_
  convert ht using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
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
9. Apply lem-pur-derived-change-of-rings to obtain the universal sheaf derived pair,
including its counit on K-flat complexes. The normalized derived Hom comparison supplies
its adjunction and its unit formula on every homotopy representative.
10. Transport this universal pair and normalized adjunction through the exact evaluation
equivalences. The ordinary scalar unit square from step 4 gives the transported normalization;
the derived comparison is the corresponding mate. Its counit factorization also transports
the K-flat computation, and its mate-unit identity gives the unit square on every derived object.
-/
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
  classical
  let e := punctualEquivalence R
  let : e.functor.Additive := singletonEvaluationAdditive R
  let : e.inverse.Additive := e.toAdjunction.right_adjoint_additive
  let : (singletonEvaluation R).IsEquivalence := e.isEquivalence_functor
  refine ⟨e, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    exact hT.map_of_exact (singletonEvaluation R)
  · exact punctualTensorComparison R
  · exact ⟨punctualComplexEquivalence R, punctualComplexEquivalence_functor R⟩
  · let F := (singletonEvaluation R).mapHomotopyCategory (.up ℤ)
    let : F.Full := inferInstanceAs
      ((singletonEvaluation R).mapHomotopyCategory (.up ℤ)).Full
    let : F.Faithful := inferInstanceAs
      ((singletonEvaluation R).mapHomotopyCategory (.up ℤ)).Faithful
    let : F.EssSurj := ⟨fun K ↦ by
      obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      let ec := e.mapHomologicalComplex (.up ℤ)
      refine ⟨(HomotopyCategory.quotient _ _).obj (ec.inverse.obj L), ⟨?_⟩⟩
      exact ((singletonEvaluation R).mapHomotopyCategoryFactors (.up ℤ)).app _ ≪≫
        (HomotopyCategory.quotient _ _).mapIso (ec.counitIso.app L)⟩
    let : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
    exact ⟨F.asEquivalence, rfl⟩
  · intro K L f
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
      (singletonEvaluation R)).symm
  · let := HasDerivedCategory.standard (singletonModuleCategory R)
    let := HasDerivedCategory.standard (ModuleCat.{u} R)
    exact ⟨inferInstance, inferInstance,
      e.mapDerivedCategory, ⟨(singletonEvaluation R).mapDerivedCategoryFactorsh⟩⟩
  · exact punctualKFlat R
  · intro S _ φ
    let hR := HasDerivedCategory.standard (singletonModuleCategory R)
    let hS := HasDerivedCategory.standard (singletonModuleCategory S)
    let : (singletonEvaluation S).IsEquivalence := punctualEvaluationIsEquivalence S
    let hRM := HasDerivedCategory.standard (ModuleCat.{u} R)
    let hSM := HasDerivedCategory.standard (ModuleCat.{u} S)
    obtain ⟨E, h, hm, hE, _, _, LS, εS, hLS, _, hcompute⟩ :=
      SheafOfModules.derivedChangeOfRingsIndependentCoefficients (singletonRingMap φ)
    let : E.Additive := hE
    obtain ⟨hUlim, hUcolim, hadj⟩ :=
      SheafOfModules.sheafRingCoefficientOrdinaryAdjunction (singletonRingMap φ)
    let : PreservesFiniteLimits (singletonSheafRestriction φ) := hUlim
    let : PreservesFiniteColimits (singletonSheafRestriction φ) := hUcolim
    obtain ⟨a, ha⟩ := hadj E h hm
    let s := punctualExtensionComparison φ E h hm
    let r := punctualRestrictionComparison φ
    have hu : singletonScalarUnitCompatible φ E h s r a := by
      refine ⟨punctualExtensionComparison_tmul φ E h hm, fun _ _ ↦ rfl, ?_⟩
      intro M
      apply ModuleCat.hom_ext
      ext x
      have hv := ha M (E.obj M) (eqToHom (h M).symm)
        (op (⟨PUnit.unit⟩ : singletonSite)) x
      have hi : a.homEquiv M (E.obj M)
          (eqToHom (h M) ≫ eqToHom (h M).symm) = a.unit.app M := by
        rw [eqToHom_trans, eqToHom_refl, a.homEquiv_id]
      rw [hi] at hv
      change (s.hom.app M) (((a.unit.app M).val.app _) x) = (1 : S) ⊗ₜ[R, φ] x
      exact (congrArg (fun y : (singletonEvaluation S).obj (E.obj M) ↦
        (s.hom.app M) y) hv).trans (punctualExtensionComparison_tmul φ E h hm M 1 x)
    refine ⟨E, h, hm, hE, s, r, a, hu, ?_, hR, hS, hRM, hSM, ?_⟩
    · intro M x
      rfl
    obtain ⟨aS, hhom⟩ := SheafOfModules.sheafRingDerivedHomComparison
      (singletonRingMap φ) E h hm a LS εS hLS
    have hn (H : HomotopyCategory (singletonModuleCategory R) (.up ℤ)) :
        aS.unit.app (DerivedCategory.Qh.obj H) ≫
            (singletonSheafRestriction φ).mapDerivedCategory.map (εS.app H) ≫
            (singletonSheafRestriction φ).mapDerivedCategoryFactorsh.hom.app
              ((E.mapHomotopyCategory (.up ℤ)).obj H) =
          DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app H) := by
      have ht := hhom H ((E.mapHomotopyCategory (.up ℤ)).obj H) (𝟙 _)
      have hiε : εS.app H ≫ DerivedCategory.Qh.map
          (𝟙 ((E.mapHomotopyCategory (.up ℤ)).obj H)) = εS.app H := by
        rw [Functor.map_id]
        exact Category.comp_id _
      rw [hiε, (a.mapHomotopyCategory (.up ℤ)).homEquiv_id H,
        aS.homEquiv_unit] at ht
      let κ := (singletonSheafRestriction φ).mapDerivedCategoryFactorsh.app
        ((E.mapHomotopyCategory (.up ℤ)).obj H)
      have ht' : aS.unit.app (DerivedCategory.Qh.obj H) ≫
          (singletonSheafRestriction φ).mapDerivedCategory.map (εS.app H) =
          DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app H) ≫ κ.inv := by
        convert ht using 1 <;> rfl
      have hh := (Iso.eq_comp_inv κ).1 ht'
      simp only [Category.assoc] at hh
      convert hh using 1
      rfl
    let er := punctualEquivalence R
    let es := punctualEquivalence S
    let : er.functor.Additive := singletonEvaluationAdditive R
    let : es.functor.Additive := singletonEvaluationAdditive S
    let : er.inverse.Additive := er.toAdjunction.right_adjoint_additive
    let : es.inverse.Additive := es.toAdjunction.right_adjoint_additive
    obtain ⟨LM, εM, c, b, aM, hLM, hc, hb, hnM, hunit⟩ :=
      normalizedDerivedAdjunctionTransport er es E (singletonSheafRestriction φ)
        (ModuleCat.extendScalars φ) (ModuleCat.restrictScalars φ)
        a (ModuleCat.extendRestrictScalarsAdj φ) s r hu.2.2 LS εS hLS aS hn
    refine ⟨hUlim, hUcolim, er.mapDerivedCategory, es.mapDerivedCategory,
      (singletonEvaluation R).mapDerivedCategoryFactorsh,
      (singletonEvaluation S).mapDerivedCategoryFactorsh,
      LS, εS, LM, εM, c, b, aS, aM, hLS, hLM, ?_, hc, hb, ?_, ?_, hunit⟩
    · intro P hP
      refine ⟨hcompute P hP, ?_⟩
      let H := (HomotopyCategory.quotient _ _).obj P
      let : IsIso (εS.app H) := hcompute P hP
      have hh := hc H
      change IsIso (εM.app ((er.functor.mapHomotopyCategory (.up ℤ)).obj H))
      rw [← isIso_comp_left_iff (LM.map (er.functor.mapDerivedCategoryFactorsh.hom.app H)), hh]
      infer_instance
    · intro P _
      exact hn ((HomotopyCategory.quotient _ _).obj P)
    · intro P _
      exact hnM ((HomotopyCategory.quotient _ _).obj P)

end CategoryTheory
