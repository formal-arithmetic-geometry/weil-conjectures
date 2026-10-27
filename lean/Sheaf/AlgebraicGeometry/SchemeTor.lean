module


public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Tor sheaves from the actual derived tensor

Source: Stacks Project, Cohomology, Definition 08BP (definition-tor).
(blueprint: def-sfb-scheme-tor)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.SchemeTor

/-- The tensor of degree-zero modules in the shared K-flat derived monoidal category.
Source: Stacks 06YH and 08BP (blueprint: def-sfb-scheme-tor). -/
def tensor {X : Scheme.{u}} (P M : X.Modules) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj P ⊗
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M

/-- The degree minus q homology sheaf of the actual derived tensor.
Source: Stacks 08BP (blueprint: def-sfb-scheme-tor). -/
def obj {X : Scheme.{u}} (q : ℕ) (P M : X.Modules) : X.Modules :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (-(q : ℤ))).obj (tensor P M)

/-- The canonical Tor map, obtained by tensoring maps and then taking homology.
Source: Stacks 08BP and Algebra 00M7 (blueprint: def-sfb-scheme-tor). -/
def map {X : Scheme.{u}} (q : ℕ) {P P' M M' : X.Modules}
    (f : P ⟶ P') (g : M ⟶ M') : obj q P M ⟶ obj q P' M' :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (-(q : ℤ))).map
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map f ⊗ₘ
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map g)

/-- Sections as a module over the actual ring of sections of the open.
Source: Stacks 01HV (blueprint: def-sfb-scheme-tor). -/
def sections {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) : ModuleCat Γ(X, U) :=
  M.val.obj (op U)

/-- Ordinary ring Tor, using the recorded Mathlib left-derived tensor functor.
Source: Stacks 00LY (blueprint: def-sfb-scheme-tor). -/
def ringTor {X : Scheme.{u}} (q : ℕ) (P M : X.Modules) (U : X.Opens) :
    ModuleCat Γ(X, U) :=
  ((Tor' (ModuleCat Γ(X, U)) q).obj (sections P U)).obj (sections M U)

/-- The shared standard derived category, without a second localization.
Source: Stacks 05RU (blueprint: def-sfb-scheme-tor). -/
abbrev derived (X : Scheme.{u}) :=
  @schemeDerivedCategory X (HasDerivedCategory.standard _)

/-- A module in degree zero in the shared derived category.
Source: Stacks 08BP (blueprint: def-sfb-scheme-tor). -/
def single {X : Scheme.{u}} (M : X.Modules) : derived X :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M

/-- Canonical boundary in the second variable, with the signed derived tensor shift.
Source: Stacks 08BP, ensuing exact sequence 
(blueprint: def-sfb-scheme-tor). -/
def boundaryRight {X : Scheme.{u}} (P : X.Modules)
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hS : S.ShortExact) (q : ℕ) : obj (q + 1) P S.X₃ ⟶ obj q P S.X₁ := by
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).1.some
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).2.1.some
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := schemeModule_hasFunctorialFlatResolution X
  exact DerivedCategory.HomologySequence.δ
    ((tensorLeft (single P)).mapTriangle.obj hS.singleTriangle)
    (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega)

/-- Canonical boundary in the first variable, with the signed derived tensor shift.
Source: Stacks 08BP, ensuing exact sequence 
(blueprint: def-sfb-scheme-tor). -/
def boundaryLeft {X : Scheme.{u}} (M : X.Modules)
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hS : S.ShortExact) (q : ℕ) : obj (q + 1) S.X₃ M ⟶ obj q S.X₁ M := by
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).1.some
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).2.1.some
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := schemeModule_hasFunctorialFlatResolution X
  exact DerivedCategory.HomologySequence.δ
    ((tensorRight (single M)).mapTriangle.obj hS.singleTriangle)
    (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega)

/-- Tensor a sheaf complex termwise with a module in degree zero.
Source: Stacks 08BP (blueprint: def-sfb-scheme-tor). -/
def tensorComplex {X : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (M : X.Modules) : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  letI : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).1.some
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).2.1.some
  ((tensorRight (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) M).mapHomologicalComplex
    (.up ℤ)).obj E

/-- K-flatness for the recorded sheaf tensor and its total complex monoidal structure.
Source: Stacks 06YH (blueprint: def-sfb-scheme-tor). -/
def kFlat {X : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) : Prop :=
  letI : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).1.some
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).2.1.some
  letI : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink _
  have (A B : GradedObject ℤ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))) : A.HasTensor B := inferInstance
  (HomologicalComplex.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat E

/-- Localization of a sheaf complex in the same standard derived category.
Source: Stacks 05RU (blueprint: def-sfb-scheme-tor). -/
def localize {X : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) : derived X :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  DerivedCategory.Q.obj E

/-- The actual canonical derived comparison on a specified K-flat resolution.
No comparison is selected from a bare existence theorem.
Source: Stacks 06YH and 08BP (blueprint: def-sfb-scheme-tor). -/
def resolutionIso {X : Scheme.{u}} (P M : X.Modules)
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : E ⟶ (HomologicalComplex.single
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj P)
    [QuasiIso a]
    (hk : kFlat E) :
    tensor P M ≅ localize (tensorComplex E M) := by
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI : MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).1.some
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (SheafOfModules.tensorClosed X.sheaf).2.1.some
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := schemeModule_hasFunctorialFlatResolution X
  letI : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink _
  have (A B : GradedObject ℤ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))) : A.HasTensor B := inferInstance
  change (HomologicalComplex.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat E at hk
  exact tensorIso
    (asIso (DerivedCategory.Q.map a) ≪≫
      (DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).symm.app P).symm
    (Iso.refl _) ≪≫ DerivedCategory.QObjTensorSingleFunctorObjIso E hk M

/-- The induced homology comparison for this precise derived resolution comparison.
Source: Stacks 08BP (blueprint: def-sfb-scheme-tor). -/
def resolutionHomologyIso {X : Scheme.{u}} (P M : X.Modules) (q : ℕ)
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : E ⟶ (HomologicalComplex.single
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj P)
    [QuasiIso a]
    (hk : kFlat E) :
    obj q P M ≅ (tensorComplex E M).homology (-(q : ℤ)) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (-(q : ℤ))).mapIso
      (resolutionIso P M E a hk) ≪≫
    (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (-(q : ℤ))).app _

/-- Tensor a projective resolution with the second section module.
Source: Stacks 00LY (blueprint: def-sfb-scheme-tor). -/
def ringComplex {X : Scheme.{u}} (P M : X.Modules) (U : X.Opens)
    (E : ProjectiveResolution (sections P U)) : ChainComplex (ModuleCat Γ(X, U)) ℕ :=
  ((tensorRight (sections M U)).mapHomologicalComplex (.down ℕ)).obj E.complex

/-- The recorded Tor-to-resolution-homology comparison, with its canonical orientation.
Source: Stacks 00LY (blueprint: def-sfb-scheme-tor). -/
def ringResolutionIso {X : Scheme.{u}} (q : ℕ) (P M : X.Modules) (U : X.Opens)
    (E : ProjectiveResolution (sections P U)) :
    ringTor q P M U ≅ (ringComplex P M U E).homology q :=
  E.isoLeftDerivedObj (tensorRight (sections M U)) q

-- Keep constructed derived maps opaque to downstream statement elaboration.
attribute [irreducible] tensor obj map boundaryRight boundaryLeft
  resolutionIso resolutionHomologyIso ringResolutionIso

end AlgebraicGeometry.SchemeTor
