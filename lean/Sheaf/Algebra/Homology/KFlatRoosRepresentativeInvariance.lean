/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.CategoryTheory.StrictRoosComparison
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Abelian.FunctorCategory

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Invariance of augmented scalar-extension Roos complexes

Source: Stacks Project, Tags 06YS, 06YT, 06YY and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
The tower is indexed by n in N, corresponding to positive level n+1. Its algebra
structure is the natural transformation from the constant ring sheaf R. All tensor
objects use the recorded site tensor. The Roos complex has precisely the coordinates
V^i plus V^(i-1), differential (dx, (1-s)x-dy), and augmentation (p tensor 1, 0).
The helper existence statements uniquely determine maps on every section; no object
is selected from an unnormalized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.KFlatRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

/-- The existing module category of the underlying ring sheaf.
Source: Stacks Tag 03DA (blueprint: lem-pe-kflat-roos-representative-invariance). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- An R-algebra sheaf as an R-module, by the existing restriction of scalars.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def algebraModule {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) : Modules R :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map ι)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

/-- The algebra map has a unique R-linear sheaf map with its original section values.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: the equation on structure maps makes the sectionwise ring homomorphism
R-linear. Ring-map naturality makes these linear maps a sheaf morphism. Conversely,
the displayed value on every section determines every component, hence the map. -/
theorem algebraModuleMap_existsUnique {B B' : Sheaf J CommRingCat.{r}}
    (ι : R ⟶ B) (ι' : R ⟶ B') (f : B ⟶ B') (h : ι ≫ f = ι') :
    ∃! a : algebraModule ι ⟶ algebraModule ι',
      ∀ (U : Cᵒᵖ) (b : B.obj.obj U), a.val.app U b = f.hom.app U b := by
  sorry

/-- The uniquely normalized map of underlying algebra modules.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def algebraModuleMap {B B' : Sheaf J CommRingCat.{r}}
    (ι : R ⟶ B) (ι' : R ⟶ B') (f : B ⟶ B') (h : ι ≫ f = ι') :=
  (algebraModuleMap_existsUnique ι ι' f h).exists.choose

/-- The unit of scalar extension, uniquely specified on all local sections.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: p to p tensor 1 is additive, R-linear and commutes with restrictions;
compose with the module-sheafification unit. It is natural in the input module.
Every component is determined on every section, so this transformation is unique. -/
theorem tensorUnit_existsUnique {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) :
    ∃! η : 𝟭 (Modules R) ⟶ siteSheafTensorRight (algebraModule ι),
      ∀ (M : Modules R) (U : Cᵒᵖ) (p : M.val.obj U),
        (η.app M).val.app U p = siteSheafTensorTmul M (algebraModule ι) U p (1 : B.obj.obj U) := by
  sorry

/-- The actual scalar-extension unit, with the prescribed pure-tensor formula.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def tensorUnit {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) :=
  (tensorUnit_existsUnique ι).exists.choose

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
  (ι : (Functor.const ℕᵒᵖ).obj R ⟶ B)

/-- The module sheaf B_n with its given R-action.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def levelModule (n : ℕ) : Modules R := algebraModule (ι.app (op n))

/-- Compatibility of the algebra structure with the consecutive transition.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: naturality of ι at n+1 to n, followed by the identity law for the constant functor. -/
theorem structure_compatible (n : ℕ) :
    ι.app (op (n + 1)) ≫ B.map (homOfLE (Nat.le_succ n)).op = ι.app (op n) := by
  sorry

/-- The given transition, regarded as an R-module sheaf map.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def levelMap (n : ℕ) : levelModule B ι (n + 1) ⟶ levelModule B ι n :=
  algebraModuleMap (ι.app (op (n + 1))) (ι.app (op n))
    (B.map (homOfLE (Nat.le_succ n)).op) (structure_compatible B ι n)

/-- Termwise scalar extension, restricted back to R-modules.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def level (n : ℕ) : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (siteSheafTensorRight (levelModule B ι n)).mapHomologicalComplex (.up ℤ)

/-- Strict tensor transition induced by the algebra transition.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def transition (P : CochainComplex (Modules R) ℤ) (n : ℕ) :
    (level B ι (n + 1)).obj P ⟶ (level B ι n).obj P :=
  (NatTrans.mapHomologicalComplex (siteSheafTensorRightMap (levelMap B ι n)) (.up ℤ)).app P

variable [HasCountableProducts (Modules R)]

/-- The termwise product V(P) of the scalar-extension tower.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def product (P : CochainComplex (Modules R) ℤ) :=
  ∏ᶜ fun n : ℕ => (level B ι n).obj P

/-- The endomorphism 1-s, whose nth coordinate is pr_n minus t_n pr_(n+1).
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def oneSubShift (P : CochainComplex (Modules R) ℤ) : product B ι P ⟶ product B ι P :=
  Pi.lift (fun n => Pi.π (fun k : ℕ => (level B ι k).obj P) n -
    Pi.π (fun k : ℕ => (level B ι k).obj P) (n + 1) ≫ transition B ι P n)

/-- The two coordinates of L(P) in degree i, in the order used in the node.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosX (P : CochainComplex (Modules R) ℤ) (i : ℤ) :=
  (product B ι P).X i ⊞ (product B ι P).X (i - 1)

/-- The differential (x,y) to (dx,(1-s)x-dy).
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosD (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    roosX B ι P i ⟶ roosX B ι P (i + 1) :=
  biprod.lift (biprod.fst ≫ (product B ι P).d i (i + 1))
    (biprod.fst ≫ (oneSubShift B ι P).f i ≫
      eqToHom (congrArg (product B ι P).X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (product B ι P).d (i - 1) ((i + 1) - 1))

/-- The displayed Roos differential squares to zero.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: the first coordinate is d squared, hence zero. The second is
(1-s)dx-d(1-s)x+d squared y; 1-s is a chain map, so these terms cancel. -/
theorem roosD_sq (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    roosD B ι P i ≫ roosD B ι P (i + 1) = 0 := by
  sorry

/-- The specified Roos complex, with real objects and differential.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roos (P : CochainComplex (Modules R) ℤ) : CochainComplex (Modules R) ℤ :=
  CochainComplex.of (roosX B ι P) (roosD B ι P) (roosD_sq B ι P)

/-- The product of the tensor units in degree i.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def unitProduct (P : CochainComplex (Modules R) ℤ) : P ⟶ product B ι P :=
  Pi.lift (fun n =>
    (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op n))) (.up ℤ)).app P)

/-- The augmentation (unit,0) commutes with differentials.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: tensor units commute with d. The algebra transitions preserve 1, so
(1-s) composed with the product unit is zero, giving the second coordinate. -/
theorem augmentation_comm (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    biprod.lift ((unitProduct B ι P).f i) 0 ≫ (roos B ι P).d i (i + 1) =
      P.d i (i + 1) ≫ biprod.lift ((unitProduct B ι P).f (i + 1)) 0 := by
  sorry

/-- The actual augmentation p to ((p tensor 1)_n,0).
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance). -/
def augmentation (P : CochainComplex (Modules R) ℤ) : P ⟶ roos B ι P :=
  CochainComplex.ofHom (fun i => biprod.lift ((unitProduct B ι P).f i) 0)
    (augmentation_comm B ι P)

/-- The product of a tensor B_n over all levels.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def productMap {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') :
    product B ι P ⟶ product B ι P' :=
  Limits.Pi.map (fun n => (level B ι n).map a)

/-- The diagonal product map commutes with the specified differential.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: tensor naturality makes a tensor B_n commute with transition maps. Thus
its product commutes with 1-s as well as d; multiply the two-by-two matrices. -/
theorem roosMap_comm {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') (i : ℤ) :
    biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)) ≫
        (roos B ι P').d i (i + 1) =
      (roos B ι P).d i (i + 1) ≫
        biprod.map ((productMap B ι a).f (i + 1)) ((productMap B ι a).f ((i + 1) - 1)) := by
  sorry

/-- L(a) applies the product of a tensor B_n to both coordinates.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosMap {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') :
    roos B ι P ⟶ roos B ι P' :=
  CochainComplex.ofHom
    (fun i => biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)))
    (roosMap_comm B ι a)

/-- Strict and derived invariance of the augmented scalar-extension Roos complex.
Source: Stacks Tags 06YS, 06YT, 06YY and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).

Proof:
1. The ringed-site change-of-rings K-flat quasi-isomorphism lemma gives a tensor B_n
   quasi-isomorphism at every level. Restricting scalars preserves cohomology.
   No algebra map is assumed flat or surjective. Tensor naturality gives the
   strict equality L(a) eta_P = eta_P' a.
2. The tower category is abelian levelwise. Apply lem-weil-strict-roos-comparison
   to the resulting tower quasi-isomorphism. The signed interchange (x,y) to
   (-y,x) identifies our complex with Cone(1-s)[-1], compatibly with its maps;
   hence L(a) is a quasi-isomorphism. Equivalently, exact products preserve
   levelwise quasi-isomorphisms, and the cone long exact sequence finishes.
3. Given e, use lem-pc-right-fraction-representation and
   lem-pc-quasi-isomorphisms-multiplicative-system to represent it by a roof
   Z to P, Z to P'. Both arrows are quasi-isomorphisms. Resolve Z by a K-flat
   flat-term W using lem-pc-kflat-resolution; obtain u:W to P and b:W to P'
   with Q(b) Q(u) inverse = e.
4. Set v = Q(L(b)) Q(L(u)) inverse. Apply Q to the strict augmentation
   equations for u and b to obtain the required augmented comparison equation.
   Since v and e are invertible, Q(eta_P) is invertible iff Q(eta_P') is.
   Cohomology factors through Q, so this is equivalent to the asserted
   quasi-isomorphism criterion for both augmentations. -/
theorem representativeInvariance
    [HasExactLimitsOfShape (Discrete ℕ) (Modules R)]
    [HasDerivedCategory.{w} (Modules R)]
    (P P' : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P.X i))
    (hflat' : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (R := R) (P'.X i)) :
    (∀ (a : P ⟶ P'), QuasiIso a →
      QuasiIso (roosMap B ι a) ∧
        augmentation B ι P ≫ roosMap B ι a = a ≫ augmentation B ι P') ∧
    (∀ (e : DerivedCategory.Q.{w}.obj P ≅ DerivedCategory.Q.obj P'),
      ∃ v : DerivedCategory.Q.{w}.obj (roos B ι P) ≅ DerivedCategory.Q.obj (roos B ι P'),
        DerivedCategory.Q.map (augmentation B ι P) ≫ v.hom =
          e.hom ≫ DerivedCategory.Q.map (augmentation B ι P')) ∧
    (Nonempty (DerivedCategory.Q.{w}.obj P ≅ DerivedCategory.Q.obj P') →
      (QuasiIso (augmentation B ι P) ↔ QuasiIso (augmentation B ι P'))) := by
  sorry

end SheafOfModules.KFlatRoos
