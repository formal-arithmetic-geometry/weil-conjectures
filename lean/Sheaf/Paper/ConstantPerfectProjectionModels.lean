/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.AugmentedDiagramProjectionMate
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.Paper.RingedSitePerfectProjectionFormula
import Sheaf.Paper.ProjectionMateExact
import Sheaf.SixFunctors.GeometricInverseImageConstantModule
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Projective

/-! # Independent constant perfect models and evaluated strict projections

Source: Stacks Project, sites-cohomology.tex, Tag 0944 and Equation 0B56;
sites-modules.tex, Tag 03EI
(blueprint: lem-sf-cbc-constant-perfect-projection-models).

The model statement applies to every bounded representative and degreewise splitting.
The projection statements give invertibility and identify the evaluated strict-tower mate
with the recorded K-flat projection formula through pinned canonical comparisons.
Natural number n denotes positive level n+1. All derived objects are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w wA wY wX wTY wTX
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantPerfectProjection

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A]

/-- The actual termwise constant realization, including the differentials.
Source: Stacks 03EI (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
abbrev constantComplex (E : CochainComplex (ModuleCat.{u} A) ℤ) :=
  ((commutativeSiteConstantModuleFunctor J A).mapHomologicalComplex (.up ℤ)).obj E

/-- Coordinate evaluation followed by the actual coefficient sheafification unit is linear.
Source: Stacks 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: evaluation is additive and scalar multiplication is pointwise. The ring unit
preserves addition and multiplication, which is the restricted scalar action. -/
theorem finiteFreeCoordinate_linear (m : ℕ) (i : Fin m) (U : Cᵒᵖ) :
    (∀ x y : Fin m → A, (realizationRingUnit J A).app U ((x + y) i) =
      (realizationRingUnit J A).app U (x i) + (realizationRingUnit J A).app U (y i)) ∧
    (∀ (r : A) (x : Fin m → A), (realizationRingUnit J A).app U ((r • x) i) =
      (realizationRingUnit J A).app U r * (realizationRingUnit J A).app U (x i)) := by
  sorry

/-- The coordinate component into the ring unit, with its restricted scalar action.
Source: Stacks 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def finiteFreeCoordinateComponent (m : ℕ) (i : Fin m) (U : Cᵒᵖ) :
    ModuleCat.of A (Fin m → A) ⟶
      ((PresheafOfModules.restrictScalars (realizationRingUnit J A)).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (realizationRing J A))).val).obj U :=
  ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (realizationRingUnit J A)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (realizationRing J A))).val).obj U)
    { toFun := fun x ↦ (realizationRingUnit J A).app U (x i)
      map_add' := (finiteFreeCoordinate_linear J A m i U).1
      map_smul' := (finiteFreeCoordinate_linear J A m i U).2 }

/-- The coordinate components commute with restriction.
Source: Stacks 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: this is naturality of the coefficient-ring sheafification unit at x i. -/
theorem finiteFreeCoordinate_naturality (m : ℕ) (i : Fin m)
    {U V : Cᵒᵖ} (g : U ⟶ V) :
    ((siteConstantModulePresheafGeneral (C := C) A).obj
        (ModuleCat.of A (Fin m → A))).map g ≫
      (ModuleCat.restrictScalars
        (((Functor.const Cᵒᵖ).obj (RingCat.of A)).map g).hom).map
          (finiteFreeCoordinateComponent J A m i V) =
    finiteFreeCoordinateComponent J A m i U ≫
      ((PresheafOfModules.restrictScalars (realizationRingUnit J A)).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (realizationRing J A))).val).map g := by
  sorry

/-- The canonical coordinate map, obtained by the module sheafification adjunction.
Source: Stacks 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def finiteFreeCoordinate (m : ℕ) (i : Fin m) :
    (commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A (Fin m → A)) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (realizationRing J A)) :=
  letI := (realizationRingUnit_locallyBijective J A).1
  letI := (realizationRingUnit_locallyBijective J A).2
  (PresheafOfModules.sheafificationHomEquiv.{u, u, u, u} (realizationRingUnit J A)).symm
    { app := finiteFreeCoordinateComponent J A m i
      naturality := finiteFreeCoordinate_naturality J A m i }

/-- The canonical finite-product comparison has the sheafified coordinate projections.
It includes the empty product when m is zero.
Source: Stacks 00WJ, 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def finiteFreeComparison (m : ℕ) :
    (commutativeSiteConstantModuleFunctor J A).obj (ModuleCat.of A (Fin m → A)) ⟶
      ∏ᶜ fun _ : Fin m ↦ SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J A)) :=
  Pi.lift (finiteFreeCoordinate J A m)

/-- The coordinate comparison is an isomorphism, including in rank zero.
Source: Stacks 00WJ, 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: finite products of constant presheaves are the tuple module. Exact
sheafification preserves that product cone and the coefficient unit. Thus its
canonical product comparison, with exactly the displayed projections, is invertible. -/
theorem finiteFreeComparison_isIso (m : ℕ) : IsIso (finiteFreeComparison J A m) := by
  sorry

attribute [instance] finiteFreeComparison_isIso

/-- Every chosen finite-projective model realizes to a bounded model, and the constant
realizations of every chosen splitting give precisely its strict-perfect package.
Source: Stacks 03EI, 00WJ and 0944
(blueprint: lem-sf-cbc-constant-perfect-projection-models).

Proof (node steps 1--3): finite generation supplies a finite-free surjection in each
nonzero degree, and projectivity splits it; use rank zero outside the bounded interval.
Finite-product preservation of sheafification identifies the constant finite-free module
with the finite power of the ring sheaf, including rank zero. Applying the constant functor
preserves each splitting equation, and composing with these finite-free identifications
produces the specified package; no differential compatibility is required of the splittings.
Exactness and additivity preserve the finite support and descend termwise realization to
the derived category. Apply this derived functor to the chosen representing isomorphism,
and use its canonical complex and degree-zero comparisons. -/
theorem constantPerfectModel
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY} (realizationModules J A)]
    (M : ModuleCat.{u} A) (E : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (ha : E.IsStrictlyGE a) (hb : E.IsStrictlyLE b)
    (hE : ∀ r : ℤ, Module.Projective A (E.X r) ∧ Module.Finite A (E.X r))
    (e : DerivedCategory.Q.obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M) :
    (∀ r : ℤ, r < a ∨ b < r → IsZero ((constantComplex J A E).X r)) ∧
    Nonempty (DerivedCategory.Q.obj (constantComplex J A E) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((commutativeSiteConstantModuleFunctor J A).obj M)) ∧
    Nonempty (ModuleCat.StrictPerfectCoefficientPackage E) ∧
    ∀ s : ModuleCat.StrictPerfectCoefficientPackage E,
      ∃ (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J A))
        (constantComplex J A E)),
        p.N = s.N ∧
        (∀ r : ℤ, HEq (p.i r) ((commutativeSiteConstantModuleFunctor J A).map (s.i r) ≫
          finiteFreeComparison J A (s.N r))) ∧
        (∀ r : ℤ, HEq (p.p r) (inv (finiteFreeComparison J A (s.N r)) ≫
          (commutativeSiteConstantModuleFunctor J A).map (s.p r))) := by
  sorry

open CochainPullback StrictReduction
attribute [local irreducible] augmentedDiagramProjection

section IndependentLocalizations

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
  [HasDerivedCategory.{wY} (realizationModules J A)]
  [HasDerivedCategory.{wX} (realizationModules K A)]
  [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ realizationModules J A)]
  [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ realizationModules K A)]

/-- The underlying coefficient-module tower, retaining all unital algebra transitions.
Source: Stacks 0944, applied independently at every positive level
(blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def coefficientModules (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  B ⋙ forget₂ (CommAlgCat A) (AlgCat A) ⋙ forget₂ (AlgCat A) (ModuleCat A)

/-- The constant coefficient tower uses the actual constant realization of every transition.
Source: Stacks 03CY and 0944
(blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def coefficientTower (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A) :=
  coefficientModules A B ⋙ commutativeSiteConstantModuleFunctor J A

/-- A constant module element as a section, from the actual sheafification unit.
Source: Stacks 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def constantSection (M : ModuleCat.{u} A) (m : M) :
    ((commutativeSiteConstantModuleFunctor J A).obj M).sections :=
  ⟨fun U ↦ (toSheafify J
      ((siteConstantModulePresheafGeneral (C := C) A).obj M).presheaf).app U m,
    fun {_U _V} g ↦ (NatTrans.naturality_apply (toSheafify J
      ((siteConstantModulePresheafGeneral (C := C) A).obj M).presheaf) g m).symm⟩

/-- The actual coefficient unit at one level, determined by the constant section 1.
Source: Stacks 03CY and 0B56
(blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def coefficientUnit (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A) (n : ℕᵒᵖ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (realizationRing J A)) ⟶ (coefficientTower J A B).obj n :=
  ((coefficientTower J A B).obj n).unitHomEquiv.symm
    (constantSection J A ((coefficientModules A B).obj n) (1 : B.obj n))

/-- The specified units commute with all the unital algebra transitions.
Source: Stacks 03CY (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: the constant functor sends each transition to its sheafification. Naturality
of the sheafification unit sends the section 1 to the section of its image, which
is 1 because the transition is a unital algebra map. The unit-section bijection
then gives the equation of module maps. -/
theorem coefficientUnit_naturality (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A)
    {m n : ℕᵒᵖ} (g : m ⟶ n) :
    coefficientUnit J A B m ≫ (coefficientTower J A B).map g =
      coefficientUnit J A B n := by
  sorry

/-- The unital coefficient augmentation as one morphism of strict towers.
Source: Stacks 03CY and 0B56
(blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def coefficientAugmentation (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A) :
    (Functor.const ℕᵒᵖ).obj (𝟙_ (realizationModules J A)) ⟶ coefficientTower J A B where
  app := coefficientUnit J A B
  naturality {_m _n} g := (Category.id_comp _).trans (coefficientUnit_naturality J A B g).symm

/-- Constant scalar generalized element of the constant ring sheaf.
Source: Stacks 0H7J (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def scalarElement (a : A) :
    (constantSheaf J (Type u)).obj PUnit.{u + 1} ⟶
      (sheafCompose J (forget CommRingCat.{u})).obj (realizationRing J A) :=
  (constantSheaf J (Type u)).map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ a)) ≫
    (constantCommuteCompose J (forget CommRingCat.{u})).inv.app (CommRingCat.of A)

/-- The actual pulled-back coefficient tower is the constant tower on the source site.
The equation on every coefficient element characterizes the comparison, rather than
allowing an arbitrary tower isomorphism.
Source: Stacks 0H7J and 00YV
(blueprint: lem-sf-cbc-constant-perfect-projection-models).

Proof (node Step 4): inverse image preserves coproducts of the terminal object, hence
constant sets. Its finite-limit preservation carries addition and scalar operations
through this comparison. The scalar equation fixes the A-action. Lift the resulting
constant-set comparison to modules; its inverse is linear for the same reason. Its
values on constant elements prove naturality for every coefficient transition. Since
these transitions preserve 1, the same comparison preserves the tower augmentation. -/
theorem constantCoefficientPullback
    (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A)
    (f : RingedPullback.{u, u, u, u, u} (realizationRing J A) (realizationRing K A))
    [IsIso f.coefficient] (k : Comparison.{u, u, u, u, u} f)
    (point : f.uInv.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    (hconstant : ∀ a : A, f.uInv.map (scalarElement J A a) ≫
        f.I.ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat.{u})).map f.coefficient =
      point.hom ≫ scalarElement K A a) :
    ∃ v : coefficientTower J A B ⋙ f.L ≅ coefficientTower K A B,
      (∀ (n : ℕᵒᵖ) (b : B.obj n),
        f.L.map (((coefficientTower J A B).obj n).unitHomEquiv.symm
          (constantSection J A ((coefficientModules A B).obj n) b)) ≫ v.hom.app n =
        (moduleUnit f k).hom ≫ ((coefficientTower K A B).obj n).unitHomEquiv.symm
          (constantSection K A ((coefficientModules A B).obj n) b)) ∧
      pulledUnit f.L (moduleUnit f k) (coefficientTower J A B)
          (coefficientAugmentation J A B) ≫ v.hom = coefficientAugmentation K A B := by
  sorry

attribute [local irreducible] coefficientTower coefficientAugmentation
  commutativeSiteConstantModuleFunctor SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
/-- Each evaluation of the specified strict-tower projection is invertible, naturally
in the unbounded input, with independent localization sizes. The explicit identification
with the recorded K-flat projection is stated in constantPerfectProjectionIdentification.
Source: Stacks 0944 and Equation 0B56
(blueprint: lem-sf-cbc-constant-perfect-projection-models).

Proof (node steps 4--7): geometric inverse image preserves constants and their algebra
operations and transitions. Under the constant-ring identification module pullback is
exact. Its exact localization agrees with K-flat derived pullback: compute on a flat-term
K-flat resolution and then apply exact pullback to its quasi-isomorphism. The normalized
reduction/pullback comparison therefore applies to the actual constant algebra tower.
The augmented diagram projection is the published tower-adjunction mate. Evaluation,
with the normalized direct-image comparison, sends it to the ambient adjoint of evaluated
tau followed by reduction of the same counit. This is Equation 0B56 with the canonical
tensor and evaluation comparisons, not a separately chosen map. By constantPerfectModel,
every coefficient is perfect on the target site, so Tag 0944 makes this precise evaluated
arrow invertible for arbitrary unbounded input. The mate is already a natural
transformation, and functorial evaluation preserves naturality. Models and splittings
are chosen separately at each level solely to verify perfectness: neither transition
lifts nor a common bound on lengths or ranks enter the construction. -/
theorem constantPerfectProjectionModels
    (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A)
    (hB : ∀ n : ℕᵒᵖ, DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor _ 0).obj ((coefficientModules A B).obj n)))
    (f : RingedPullback.{u, u, u, u, u} (realizationRing J A) (realizationRing K A))
    [IsIso f.coefficient] [f.V.Additive]
    [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison.{u, u, u, u, u} f)
    (point : f.uInv.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    (hconstant : ∀ a : A, f.uInv.map (scalarElement J A a) ≫
        f.I.ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat.{u})).map f.coefficient =
      point.hom ≫ scalarElement K A a)
    (MY : RingedModel.{u, u, u, wY, wTY} (coefficientTower J A B) (coefficientAugmentation J A B))
    (MX : RingedModel.{u, u, u, wX, wTX} (coefficientTower J A B ⋙ f.L)
      (pulledUnit f.L (moduleUnit f k) (coefficientTower J A B)
        (coefficientAugmentation J A B)))
    (tau : MY.B ⋙ (termwise f.L).mapDerivedCategory.{wTY, wTX, u, u, u + 1, u + 1} ≅
      f.L.mapDerivedCategory.{wY, wX, u, u, u + 1, u + 1} ⋙ MX.B)
    (htau : IsNormalized.{u + 1, u, u + 1, u, wY, wX, wTY, wTX}
      (A := realizationModules J A) (B := realizationModules K A) f.L (coefficientTower J A B)
      (coefficientAugmentation J A B) (moduleUnit f k)
      (flatRepresentatives (realizationRing J A))
      (flatRepresentatives (realizationRing K A)) MY MX k.mu k.naturality tau)
    (P : AugmentedProjectionDirectImage.{u + 1, u, u + 1, u, wX, wY, wTX, wTY}
      f.L f.V f.moduleAdj) :
    ∀ (n : ℕᵒᵖ) (F : DerivedCategory (realizationModules K A)),
      IsIso (((evaluation ℕᵒᵖ (realizationModules J A)).obj n).mapDerivedCategory.map
        ((augmentedDiagramProjection.{u + 1, u, u + 1, u, wX, wY, wTX, wTY}
            (A := realizationModules K A)
            (B := realizationModules J A) f.L f.V f.moduleAdj P MY.B MX.B tau).app F)) := by
  sorry

end IndependentLocalizations

section CanonicalComparisons

set_option backward.isDefEq.respectTransparency true

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}

open SheafOfModules

/-- The existing ordinary direct-sum total tensor on the corner's complexes.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
abbrev totalTensor (Y : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj
    ((curriedTensor Y.mateModules).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

/-- The derived tensor counit is uniquely pinned by the given K-flat comparison.
Source: Stacks 06YS, 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: resolve both complexes by flat-term K-flat complexes. Invert their localized
resolution maps, apply the inverse representative comparison, then map the ordinary
tensor of the resolutions. Comparison maps between resolutions prove independence
and naturality. Naturality with the resolving quasi-isomorphisms proves uniqueness. -/
theorem tensorCochainCounit_existsUnique (Y : RingedTensorCorner.{u, w})
    (a : RingedTensorModel Y) :
    ∃! δ : (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ Y.tensor ⟶
        totalTensor Y ⋙ DerivedCategory.Q,
      ∀ P Q : Y.mateFlat.FullSubcategory,
        a.representative.hom.app (P, Q) ≫ δ.app (P.obj, Q.obj) = 𝟙 _ := by
  sorry

/-- The tensor counit chosen by its uniqueness-determining K-flat equation.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def tensorCochainCounit (Y : RingedTensorCorner.{u, w}) (a : RingedTensorModel Y) :
    (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ Y.tensor ⟶
      totalTensor Y ⋙ DerivedCategory.Q :=
  Classical.choose (tensorCochainCounit_existsUnique Y a).exists

/-- Derived tensor with the specified module concentrated in degree zero.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def tensorWithSingle (Y : RingedTensorCorner.{u, w}) (N : Y.mateModules) :
    Y.mateDerived ⥤ Y.mateDerived :=
  Prod.sectL Y.mateDerived ((DerivedCategory.singleFunctor Y.mateModules 0).obj N) ⋙ Y.tensor

/-- The actual counit component for fixed coefficients; the total/single comparison
is the existing signed complex comparison, rather than a freely chosen identification.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def tensorSingleCounitApp (Y : RingedTensorCorner.{u, w}) (a : RingedTensorModel Y)
    (N : Y.mateModules) (P : CochainComplex Y.mateModules ℤ) :
    (tensorWithSingle Y N).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P) :=
  Y.tensor.map
    (X := (DerivedCategory.Q.obj P, (DerivedCategory.singleFunctor Y.mateModules 0).obj N))
    (Y := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj
      ((HomologicalComplex.single Y.mateModules (.up ℤ) 0).obj N)))
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
      ((DerivedCategory.singleFunctorIsoCompQ Y.mateModules 0).hom.app N)) ≫
    (tensorCochainCounit Y a).app
      (P, (HomologicalComplex.single Y.mateModules (.up ℤ) 0).obj N) ≫
    DerivedCategory.Q.map
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor Y.mateModules) N).hom.app P)

/-- Naturality of the fixed-coefficient tensor counit.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: compose naturality of tensor, of its pinned counit, and of the total/single
comparison. These three squares have exactly the displayed composite as boundary. -/
theorem tensorSingleCounit_naturality (Y : RingedTensorCorner.{u, w})
    (a : RingedTensorModel Y) (N : Y.mateModules)
    {P Q : CochainComplex Y.mateModules ℤ} (g : P ⟶ Q) :
    (tensorWithSingle Y N).map (DerivedCategory.Q.map g) ≫ tensorSingleCounitApp Y a N Q =
      tensorSingleCounitApp Y a N P ≫
        DerivedCategory.Q.map (((tensorRight N).mapHomologicalComplex (.up ℤ)).map g) := by
  sorry

/-- Fixed-coefficient tensor counit as a natural transformation.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def tensorSingleCounit (Y : RingedTensorCorner.{u, w}) (a : RingedTensorModel Y)
    (N : Y.mateModules) :
    DerivedCategory.Q ⋙ tensorWithSingle Y N ⟶
      (tensorRight N).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app := tensorSingleCounitApp Y a N
  naturality {_P _Q} g := tensorSingleCounit_naturality Y a N g

/-- Evaluation of strict reduction is derived tensor, with its comparison pinned by
both counits on every complex, hence in particular on every K-flat representative.
Source: Stacks 06YY, 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: evaluation is exact and computes limits pointwise. The evaluated reduction
counit and the fixed tensor counit compute the same ordinary tensor on flat-term
K-flat complexes. Both are universal left-derived functors; their unique isomorphism
commuting with the counits is the claimed comparison, with no choice of coefficient
resolution retained in its data. -/
theorem reductionTensorComparison_existsUnique (Y : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Y.mateModules)]
    (a : RingedTensorModel Y) (Q : ℕᵒᵖ ⥤ Y.mateModules)
    (q : (Functor.const ℕᵒᵖ).obj (𝟙_ Y.mateModules) ⟶ Q)
    (M : RingedModel.{u, u, u, w, wTY} (R := Y.ring) Q q) (n : ℕᵒᵖ) :
    ∃! γ : M.B ⋙ ((evaluation ℕᵒᵖ Y.mateModules).obj n).mapDerivedCategory ≅
        tensorWithSingle Y (Q.obj n),
      ∀ P : CochainComplex Y.mateModules ℤ,
        γ.hom.app (DerivedCategory.Q.obj P) ≫ tensorSingleCounitApp Y a (Q.obj n) P =
          (evaluationCounit Q q (flatRepresentatives Y.ring) M n.unop).app P := by
  sorry

/-- The evaluation/tensor comparison selected by its universal counit equation.
Source: Stacks 06YY, 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def reductionTensorComparison (Y : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Y.mateModules)]
    (a : RingedTensorModel Y) (Q : ℕᵒᵖ ⥤ Y.mateModules)
    (q : (Functor.const ℕᵒᵖ).obj (𝟙_ Y.mateModules) ⟶ Q)
    (M : RingedModel.{u, u, u, w, wTY} (R := Y.ring) Q q) (n : ℕᵒᵖ) :
    M.B ⋙ ((evaluation ℕᵒᵖ Y.mateModules).obj n).mapDerivedCategory ≅
      tensorWithSingle Y (Q.obj n) :=
  Classical.choose (reductionTensorComparison_existsUnique Y a Q q M n).exists

/-- The ordinary module pullback presentation underlying the recorded K-flat edge.
Source: Stacks 03EL (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
abbrev edgePullback {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :
    RingedPullback.{u, u, u, u, u} Y.ring X.ring where
  uInv := e.inverse
  uPush := e.direct
  adj := e.adjunction
  finiteLimits := e.finiteLimits
  RI := e.inverseRing
  I := e.algebraic
  coefficient := e.ringMap
  L := e.pullback
  hobj := e.object_eq
  hmap := e.map_eq
  V := e.pushforward
  moduleAdj := e.moduleAdjunction

/-- Exact localization and K-flat derived pullback agree by their specified counits.
Source: Stacks 015F, 06YY (blueprint: lem-sf-cbc-constant-perfect-projection-models).
Proof: exact pullback preserves all quasi-isomorphisms. Its localization is therefore
also its universal left-derived functor with the localization factor as counit. The
K-flat edge has the same left-derived universal property; uniqueness gives precisely
this isomorphism and the displayed equation on the whole homotopy category. -/
theorem exactPullbackComparison_existsUnique {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback] :
    ∃! κ : e.left ≅ e.pullback.mapDerivedCategory,
      ∀ H : HomotopyCategory Y.mateModules (.up ℤ),
        κ.hom.app (DerivedCategory.Qh.obj H) ≫
          e.pullback.mapDerivedCategoryFactorsh.hom.app H = e.epsilon.app H := by
  sorry

/-- Canonical exact-versus-K-flat pullback comparison; its counit pins the map.
Source: Stacks 015F, 06YY (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def exactPullbackComparison {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback] :
    e.left ≅ e.pullback.mapDerivedCategory :=
  Classical.choose (exactPullbackComparison_existsUnique e).exists

/-- The right-adjoint comparison is the mate of the pinned pullback comparison.
Its counit equation therefore uses the very same adjunction as the projection formula.
Source: Stacks 07A6 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def projectionRightComparison {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Y.mateModules)]
    [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ X.mateModules)]
    (P : AugmentedProjectionDirectImage e.pullback e.pushforward e.moduleAdjunction) :
    e.right ≅ P.RG :=
  Adjunction.rightAdjointUniq
    (e.derivedAdjunction.ofNatIsoLeft (exactPullbackComparison e)) P.d

/-- K-flat pullback of the degree-zero coefficient, identified with exact module pullback.
Source: Stacks 015F, 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def derivedCoefficientComparison {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    (N : Y.mateModules) :
    e.left.obj ((DerivedCategory.singleFunctor Y.mateModules 0).obj N) ≅
      (DerivedCategory.singleFunctor X.mateModules 0).obj (e.pullback.obj N) :=
  (exactPullbackComparison e).app _ ≪≫ (e.pullback.mapDerivedCategorySingleFunctor 0).app N

/-- The evaluated augmented arrow conjugated by the pinned tensor and adjunction
comparisons. This definition constructs the map before asserting any equality or IsIso.
Source: Stacks 0B56, 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
def evaluatedProjectionInTensor {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Y.mateModules)]
    [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ X.mateModules)]
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    (Q : ℕᵒᵖ ⥤ Y.mateModules) (q : (Functor.const ℕᵒᵖ).obj (𝟙_ Y.mateModules) ⟶ Q)
    (j : e.pullback.obj (𝟙_ Y.mateModules) ≅ 𝟙_ X.mateModules)
    (MY : RingedModel.{u, u, u, w, wTY} (R := Y.ring) Q q)
    (MX : RingedModel.{u, u, u, w, wTX} (R := X.ring) (Q ⋙ e.pullback)
      (pulledUnit e.pullback j Q q))
    (tau : MY.B ⋙ (termwise e.pullback).mapDerivedCategory ≅
      e.pullback.mapDerivedCategory ⋙ MX.B)
    (P : AugmentedProjectionDirectImage e.pullback e.pushforward e.moduleAdjunction)
    (n : ℕᵒᵖ) (F : X.mateDerived) :
    Y.tensor.obj (e.right.obj F, (DerivedCategory.singleFunctor Y.mateModules 0).obj
      (Q.obj n)) ⟶ e.right.obj (X.tensor.obj (F,
        e.left.obj ((DerivedCategory.singleFunctor Y.mateModules 0).obj (Q.obj n)))) :=
  Y.tensor.map
    (X := (e.right.obj F, (DerivedCategory.singleFunctor Y.mateModules 0).obj (Q.obj n)))
    (Y := (P.RG.obj F, (DerivedCategory.singleFunctor Y.mateModules 0).obj (Q.obj n)))
    (Prod.mkHom ((projectionRightComparison e P).hom.app F) (𝟙 _)) ≫
    (reductionTensorComparison Y a Q q MY n).inv.app (P.RG.obj F) ≫
    ((evaluation ℕᵒᵖ Y.mateModules).obj n).mapDerivedCategory.map
      ((augmentedDiagramProjection e.pullback e.pushforward e.moduleAdjunction
        P MY.B MX.B tau).app F) ≫
    (P.beta n).hom.app (MX.B.obj F) ≫
    P.RG.map ((reductionTensorComparison X b (Q ⋙ e.pullback)
      (pulledUnit e.pullback j Q q) MX n).hom.app F ≫
        X.tensor.map
          (X := (F, (DerivedCategory.singleFunctor X.mateModules 0).obj
            (e.pullback.obj (Q.obj n))))
          (Y := (F, e.left.obj ((DerivedCategory.singleFunctor Y.mateModules 0).obj
            (Q.obj n))))
          (Prod.mkHom (𝟙 F) (derivedCoefficientComparison e (Q.obj n)).inv)) ≫
    (projectionRightComparison e P).inv.app
      (X.tensor.obj (F, e.left.obj
        ((DerivedCategory.singleFunctor Y.mateModules 0).obj (Q.obj n))))

/-- A constant ringed site with its chosen K-flat tensor presentation, using the existing
module category and unbounded derived localization. The two sites use one localization
size only in this presentation required by RingedTensorEdge, not a site-size equality.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
abbrev constantTensorCorner [HasDerivedCategory.{w} (realizationModules J A)]
    (T : DerivedCategory (realizationModules J A) ×
      DerivedCategory (realizationModules J A) ⥤ DerivedCategory (realizationModules J A)) :
    RingedTensorCorner.{u, w} where
  site := C
  category := inferInstance
  topology := J
  ring := realizationRing J A
  tensor := T

/-- Additivity of the actual pullback in the constant-site presentation is the field
already supplied by the K-flat edge. This exposes that field to typeclass search
without introducing an additional mathematical hypothesis.
Source: Stacks 03EL (blueprint: lem-sf-cbc-constant-perfect-projection-models). -/
instance constantEdgePullback_additive
    [HasDerivedCategory.{w} (realizationModules J A)]
    [HasDerivedCategory.{w} (realizationModules K A)]
    (TY : DerivedCategory (realizationModules J A) ×
      DerivedCategory (realizationModules J A) ⥤ DerivedCategory (realizationModules J A))
    (TX : DerivedCategory (realizationModules K A) ×
      DerivedCategory (realizationModules K A) ⥤ DerivedCategory (realizationModules K A))
    (e : RingedTensorEdge (constantTensorCorner J A TY) (constantTensorCorner K A TX)) :
    e.pullback.Additive :=
  e.additive

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the actual augmented strict-tower projection is the projection-formula
arrow of Tag 0944, after the pinned tensor, direct-image and exact/K-flat comparisons.
It is invertible for the given perfect algebra coefficients. Neither representatives,
splittings, lifts of transitions nor uniform bounds are parameters of this assertion.
Source: Stacks 0944, Equation 0B56, 03EI
(blueprint: lem-sf-cbc-constant-perfect-projection-models).

Proof (node steps 1--7): constantPerfectModel constructs bounded finite-free retract
representatives with canonical coordinate splitting maps. Its derived representing
isomorphism proves that every constant coefficient is perfect. The scalar equation
makes the pulled coefficient tower the constant tower on the source, by
constantCoefficientPullback, including its augmentation and all algebra transitions.
The counit-pinned exactPullbackComparison identifies the exact localization with Lu^*.
The reductionTensorComparison counit equation identifies evaluated reduction with
K-flat derived tensor; uniqueness on resolving pairs makes this comparison compatible
with the normalized tau. Transpose the evaluated augmented mate using P.beta_counit.
After these comparisons its transpose is (e.tensorComparison a b) followed by the
counit tensor identity, using projectionRightComparison's adjunction mate. Injectivity
of the Hom equivalence gives precisely e.projection, not an arbitrary adjunct.
Apply ringedSitePerfectProjectionFormula to this coefficient and arbitrary unbounded F.
Naturality follows from the natural transformations used to define the conjugated map.
All perfect models were used only separately to check each coefficient's perfectness;
none enter the constructed map or its comparison equations. -/
theorem constantPerfectProjectionIdentification
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (realizationModules J A)]
    [HasDerivedCategory.{w} (realizationModules K A)]
    [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ realizationModules J A)]
    [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ realizationModules K A)]
    (TY : DerivedCategory (realizationModules J A) ×
      DerivedCategory (realizationModules J A) ⥤ DerivedCategory (realizationModules J A))
    (TX : DerivedCategory (realizationModules K A) ×
      DerivedCategory (realizationModules K A) ⥤ DerivedCategory (realizationModules K A))
    (e : RingedTensorEdge (constantTensorCorner J A TY) (constantTensorCorner K A TX))
    [IsIso e.ringMap] [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    (a : RingedTensorModel (constantTensorCorner J A TY))
    (b : RingedTensorModel (constantTensorCorner K A TX))
    (k : Comparison.{u, u, u, u, u} (edgePullback e))
    (point : e.inverse.obj ((constantSheaf J (Type u)).obj PUnit.{u + 1}) ≅
      (constantSheaf K (Type u)).obj PUnit.{u + 1})
    (hconstant : ∀ r : A, e.inverse.map (scalarElement J A r) ≫
        e.algebraic.ringUnderlying.hom ≫
          (sheafCompose K (forget CommRingCat.{u})).map e.ringMap =
      point.hom ≫ scalarElement K A r)
    (B : ℕᵒᵖ ⥤ CommAlgCat.{u} A)
    (hB : ∀ n : ℕᵒᵖ, DerivedCategory.IsPerfectRingComplex
      ((DerivedCategory.singleFunctor _ 0).obj ((coefficientModules A B).obj n)))
    (MY : RingedModel.{u, u, u, w, wTY}
      (R := realizationRing J A) (coefficientTower J A B) (coefficientAugmentation J A B))
    (MX : RingedModel.{u, u, u, w, wTX}
      (R := realizationRing K A) (coefficientTower J A B ⋙ e.pullback)
      (pulledUnit e.pullback (moduleUnit (edgePullback e) k)
        (coefficientTower J A B) (coefficientAugmentation J A B)))
    (tau : MY.B ⋙ (termwise (edgePullback e).L).mapDerivedCategory.{wTY, wTX, u, u, u + 1, u + 1} ≅
      (edgePullback e).L.mapDerivedCategory.{w, w, u, u, u + 1, u + 1} ⋙ MX.B)
    (htau : IsNormalized.{u + 1, u, u + 1, u, w, w, wTY, wTX}
      (A := realizationModules J A) (B := realizationModules K A) (edgePullback e).L
      (coefficientTower J A B)
      (coefficientAugmentation J A B) (moduleUnit (edgePullback e) k)
      (flatRepresentatives (realizationRing J A))
      (flatRepresentatives (realizationRing K A)) MY MX k.mu k.naturality tau)
    (P : AugmentedProjectionDirectImage.{u + 1, u, u + 1, u, w, w, wTX, wTY}
      (edgePullback e).L (edgePullback e).V (edgePullback e).moduleAdj) :
    ∀ (n : ℕᵒᵖ) (F : DerivedCategory (realizationModules K A)),
      evaluatedProjectionInTensor e a b (coefficientTower J A B)
          (coefficientAugmentation J A B) (moduleUnit (edgePullback e) k) MY MX tau P n F =
        e.projection a b F ((DerivedCategory.singleFunctor _ 0).obj
          ((coefficientTower J A B).obj n)) ∧
      IsIso (evaluatedProjectionInTensor e a b (coefficientTower J A B)
        (coefficientAugmentation J A B) (moduleUnit (edgePullback e) k) MY MX tau P n F) := by
  sorry

end CanonicalComparisons

end CategoryTheory.ConstantPerfectProjection
