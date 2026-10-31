/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Constant quotient-complex and reduction models

Source: Stacks Project, Tags 03EL, 03EK, 015F and 08TC.
(blueprint: def-a1-constant-complex-quotient-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
universe u v r
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

namespace AlgebraicGeometry.ConstantComplexBaseChange

/-- Fix the smallness universe before synthesizing the coefficient sheaf operations.
Source: the small-site size convention
(blueprint: def-a1-constant-complex-quotient-model). -/
instance (priority := 4000) siteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Abelian sheafification in the fixed coefficient size, specializing the recorded instance.
Source: Stacks 03DA (blueprint: def-a1-constant-complex-quotient-model). -/
instance (priority := 4000) siteAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralOperationsAbSheafify.{u, 0} W

/-- The corresponding fixed-size locally bijective criterion.
Source: Stacks 03DA (blueprint: def-a1-constant-complex-quotient-model). -/
instance (priority := 4000) siteAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralOperationsAbLocallyBijective.{u, 0} W

/-- Module sheaves over a commutative coefficient sheaf, with commutativity forgotten.
Source: Stacks 03DA (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev Modules {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    (S : Sheaf J CommRingCat.{r}) :=
  SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)

/-- Sectionwise extension of scalars before sheafification, using the existing tensor.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def extensionPresheaf {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {S S' : Sheaf J CommRingCat.{r}} (c : S ⟶ S') :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S) ⥤
      PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S').obj where
  obj M := SheafOfModules.changeOfRingsPresheaf.{v, u, r} c M
  map {M N} f :=
    { app := fun V ↦ (ModuleCat.extendScalars (c.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{v, u, r} c M f }
  map_id M := by
    ext V : 1
    simp
    rfl
  map_comp f g := by
    ext V : 1
    exact (ModuleCat.extendScalars (c.hom.app V).hom).map_comp _ _

/-- Additivity of the sectionwise tensor functor.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
instance extensionPresheaf_additive {C : Type u} [Category.{v} C]
    [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    {S S' : Sheaf J CommRingCat.{r}} (c : S ⟶ S') : (extensionPresheaf c).Additive where
  map_add {M N} f g := by
    ext V : 1
    have : (ModuleCat.extendScalars (c.hom.app V).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (c.hom.app V).hom).left_adjoint_additive
    simpa only [extensionPresheaf, SheafOfModules.add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (c.hom.app V).hom).map_add
        (f := f.val.app V) (g := g.val.app V)

/-- Sheaf tensor extension of scalars. Its object and map are the existing change of rings.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def extension {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {S S' : Sheaf J CommRingCat.{r}} (c : S ⟶ S') :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S') :=
  extensionPresheaf c ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S').obj)

/-- Additivity of sheaf tensor extension of scalars.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
instance extension_additive {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {S S' : Sheaf J CommRingCat.{r}} (c : S ⟶ S') :
    (extension c).Additive := by
  have : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S').obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  dsimp only [extension]
  infer_instance

/-- The pure tensor section in the sheafified extension, scalar factor written first.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def tensorSection {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} {S S' : Sheaf J CommRingCat.{r}}
    (c : S ⟶ S') (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj S)) (V : Cᵒᵖ) (a : S'.obj.obj V) (m : M.val.obj V) :
    ((extension c).obj M).val.obj V :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S').obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{v, u, r} c M)).app V)
        (a ⊗ₜ[S.obj.obj V, (c.hom.app V).hom] m)

/-- The quotient indexed by n corresponds to the paper's positive index n+1.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev Quotient (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) := R ⧸ I ^ (n + 1)

/-- Consecutive quotient ring homomorphism.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def quotientStep {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    Quotient R I (n + 1) →+* Quotient R I n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- Map of constant ring sheaves induced by a scalar ring map.
Source: Stacks 03CY (blueprint: def-a1-constant-complex-quotient-model). -/
def constantMap (W : Scheme.{u}) {R S : Type u} [CommRing R] [CommRing S]
    (a : R →+* S) : proEtaleConstantRing W R ⟶ proEtaleConstantRing W S :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift a))

/-- Constant quotient map.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def quotientMap (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :=
  constantMap W (Ideal.Quotient.mk (I ^ (n + 1)))

/-- Actual tower of constant quotient ring sheaves.
Source: Stacks 08TC (blueprint: def-a1-constant-complex-quotient-model). -/
def coefficientTower (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology W) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ proEtaleConstantRing W (Quotient R I n))
    (fun n ↦ constantMap W (quotientStep I n))

/-- The completed ring is the inverse limit, without assuming inverse image preserves it.
Source: Stacks 08TC (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev completed (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) :=
  limit (coefficientTower W I)

/-- Constant realization of scalar modules on the original small pro-etale site.
Source: Stacks 03CY (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev constantModules (W : Scheme.{u}) (R : Type u) [CommRing R] :=
  commutativeSiteConstantModuleFunctor.{u + 1, u} (ProEt.topology W) (ULift.{u + 1} R)

/-- The finite-level complex with its original, termwise tensor differential.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def finiteComplex (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} R)) ℤ ⥤
      CochainComplex (proEtaleRingModules W (proEtaleConstantRing W (Quotient R I n))) ℤ :=
  (constantModules W R ⋙ extension.{u + 1, u, u + 1} (quotientMap W I n)).mapHomologicalComplex
    (.up ℤ)

/-- Sections of the constant module, obtained from its actual sheafification unit.
Source: Stacks 03CY (blueprint: def-a1-constant-complex-quotient-model). -/
def constantSection (W : Scheme.{u}) {R : Type u} [CommRing R]
    (N : ModuleCat.{u + 1} (ULift.{u + 1} R)) (V : W.ProEtᵒᵖ) (p : N) :
    ((constantModules W R).obj N).val.obj V := by
  letI : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralOperationsAbLocallyBijective.{u, 0} W
  letI : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralOperationsAbSheafify.{u, 0} W
  letI := (realizationRingUnit_locallyBijective (ProEt.topology W) (ULift.{u + 1} R)).1
  letI := (realizationRingUnit_locallyBijective (ProEt.topology W) (ULift.{u + 1} R)).2
  exact (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      (realizationRingUnit (ProEt.topology W) (ULift.{u + 1} R))).unit.app
        ((siteConstantModulePresheafGeneral.{u + 1, u} (C := W.ProEt) (ULift.{u + 1} R)).obj
          N)).app V) p

/-- A scalar constant section of a constant ring sheaf.
Source: Stacks 03CY (blueprint: def-a1-constant-complex-quotient-model). -/
def ringSection (W : Scheme.{u}) (A : Type u) [CommRing A] (V : W.ProEtᵒᵖ) (a : A) :
    (proEtaleConstantRing W A).obj.obj V :=
  (toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app V ⟨a⟩

/-- A finite-level section a tensor p, using the canonical constant section units.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def finiteSection (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)
    (N : ModuleCat.{u + 1} (ULift.{u + 1} R)) (V : W.ProEtᵒᵖ)
    (a : Quotient R I n) (p : N) :=
  tensorSection.{u + 1, u, u + 1} (quotientMap W I n) ((constantModules W R).obj N) V
    (ringSection W (Quotient R I n) V a) (constantSection W N V p)

/-- Pulling a section uses the canonical geometric adjunction unit.
Source: Stacks 03D2 (blueprint: def-a1-constant-complex-quotient-model). -/
def pulledSection {X Y : Scheme.{u}} (g : X ⟶ Y) (A : Type u) [CommRing A]
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEtᵒᵖ)
    (m : M.val.obj V) :
    ((proEtaleConstantRingPullback A g).obj M).val.obj ((proEtaleBaseChange g).op.obj V) :=
  (((proEtaleConstantRingAdjunction A g).unit.app M).val.app V) m

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Scalar cochain complexes in the coefficient size of the small pro-etale site.
Source: Stacks 03CY (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev ScalarComplex (R : Type u) [CommRing R] :=
  CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} R)) ℤ

/-- Restriction along a commutative ring-sheaf map uses the recorded restriction functor.
Source: Stacks 03CZ (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev restriction (W : Scheme.{u}) {S S' : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (c : S ⟶ S') : proEtaleRingModules W S' ⥤ proEtaleRingModules W S :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)

/-- A finite level viewed over the original constant ring.
Source: Stacks 03CZ (blueprint: def-a1-constant-complex-quotient-model). -/
def finiteOverScalar (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :=
  finiteComplex W I n ⋙ (restriction W (quotientMap W I n)).mapHomologicalComplex (.up ℤ)

/-- The strict semilinear quotient transitions, including their local tensor formula.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
structure FiniteTower (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) where
  step : ∀ n : ℕ, finiteComplex W I (n + 1) ⟶ finiteComplex W I n ⋙
    (restriction W (constantMap W (quotientStep I n))).mapHomologicalComplex (.up ℤ)
  scalarStep : ∀ n : ℕ, finiteOverScalar W I (n + 1) ⟶ finiteOverScalar W I n

/-- Generator formulas identifying the actual quotient transitions.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def FiniteTower.IsNormalized (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    (d : FiniteTower W I) : Prop :=
  (∀ (n : ℕ) (P : ScalarComplex R) (r : ℤ) (V : W.ProEtᵒᵖ)
    (a : (proEtaleConstantRing W (Quotient R I (n + 1))).obj.obj V)
    (p : ((constantModules W R).obj (P.X r)).val.obj V)
    (x : (((finiteComplex W I (n + 1)).obj P).X r).val.obj V),
    HEq x (tensorSection.{u + 1, u, u + 1} (quotientMap W I (n + 1))
      ((constantModules W R).obj (P.X r)) V a p) →
    HEq ((((d.step n).app P).f r).val.app V x)
      (tensorSection.{u + 1, u, u + 1} (quotientMap W I n)
        ((constantModules W R).obj (P.X r)) V
          ((constantMap W (quotientStep I n)).hom.app V a) p)) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (r : ℤ) (V : W.ProEtᵒᵖ)
    (x : (((finiteOverScalar W I (n + 1)).obj P).X r).val.obj V)
    (y : (((finiteComplex W I (n + 1)).obj P).X r).val.obj V),
    HEq x y → HEq ((((d.scalarStep n).app P).f r).val.app V x)
      ((((d.step n).app P).f r).val.app V y))

/-- A genuine strict tower, after restricting its varying coefficients to constant R.
Source: Stacks 08TC (blueprint: def-a1-constant-complex-quotient-model). -/
def FiniteTower.scalarTower (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    (d : FiniteTower W I) :=
  (Functor.ofOpSequence (X := fun n ↦ finiteOverScalar W I n) d.scalarStep).flip

/-- Tensoring the original scalar complex with the actual completed coefficient sheaf.
Source: Stacks 03EK (blueprint: def-a1-constant-complex-quotient-model). -/
def completedComplex (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    (b : proEtaleConstantRing W R ⟶ completed W I) :
    ScalarComplex R ⥤ CochainComplex (proEtaleRingModules W (completed W I)) ℤ :=
  (constantModules W R ⋙ extension.{u + 1, u, u + 1} b).mapHomologicalComplex (.up ℤ)

/-- Finite levels restricted along the actual limit projections.
Source: Stacks 03CZ (blueprint: def-a1-constant-complex-quotient-model). -/
def finiteOverCompleted (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :=
  finiteComplex W I n ⋙
    (restriction W (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex (.up ℤ)

/-- The specified bounded finite-projective representatives, before derived localization.
Source: definition of perfect ring complex
(blueprint: def-a1-constant-complex-quotient-model). -/
def IsBoundedFiniteProjective {R : Type u} [CommRing R] (P : ScalarComplex R) : Prop :=
  ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    ∀ r : ℤ, Module.Projective (ULift.{u + 1} R) (P.X r) ∧
      Module.Finite (ULift.{u + 1} R) (P.X r)

/-- The unreassociated finite reduction, viewed as a complex over the completed ring.
Source: Stacks 03CZ and 03EK
(blueprint: def-a1-constant-complex-quotient-model). -/
def reducedComplex (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    (b : proEtaleConstantRing W R ⟶ completed W I) (n : ℕ) :=
  completedComplex W I b ⋙
    (extension.{u + 1, u, u + 1} (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex
      (.up ℤ) ⋙
    (restriction W (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex (.up ℤ)

/-- Balanced finite reductions, quotient units, and their strict completed-ring tower.
All maps are characterized on local sheaf tensor generators; no splitting is chosen.
Source: Stacks 03EK, 03CZ, 08TC
(blueprint: def-a1-constant-complex-quotient-model). -/
structure ReductionData (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    (d : FiniteTower W I) where
  coefficient : proEtaleConstantRing W R ⟶ completed W I
  reduction : ∀ (n : ℕ) (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    ((extension.{u + 1, u, u + 1} (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex
      (.up ℤ)).obj ((completedComplex W I coefficient).obj P) ≅ (finiteComplex W I n).obj P
  unit : ∀ (n : ℕ) (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    (completedComplex W I coefficient).obj P ⟶
      ((restriction W (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex
        (.up ℤ)).obj (((extension.{u + 1, u, u + 1}
          (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex (.up ℤ)).obj
            ((completedComplex W I coefficient).obj P))
  step : ∀ n : ℕ, finiteOverCompleted W I (n + 1) ⟶ finiteOverCompleted W I n
  reducedStep : ∀ (n : ℕ) (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    (reducedComplex W I coefficient (n + 1)).obj P ⟶ (reducedComplex W I coefficient n).obj P
  alpha : ∀ (n : ℕ) (P : ScalarComplex R) (_hP : IsBoundedFiniteProjective P),
    (completedComplex W I coefficient).obj P ⟶ (finiteOverCompleted W I n).obj P

/-- The generator formulas and coherence equations for this comparison data.
Source: Stacks 03EK, 03EL and 08TC
(blueprint: def-a1-constant-complex-quotient-model). -/
def ReductionData.IsNormalized (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) : Prop :=
  (∀ n : ℕ,
    e.coefficient ≫ limit.π (coefficientTower W I) (op n) = quotientMap W I n) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P)
    (r : ℤ) (V : W.ProEtᵒᵖ) (b : (completed W I).obj.obj V)
    (p : ((constantModules W R).obj (P.X r)).val.obj V)
    (a : (proEtaleConstantRing W (Quotient R I n)).obj.obj V)
    (m : (((completedComplex W I e.coefficient).obj P).X r).val.obj V)
    (x : ((((extension.{u + 1, u, u + 1}
      (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex (.up ℤ)).obj
        ((completedComplex W I e.coefficient).obj P)).X r).val.obj V),
    HEq m (tensorSection.{u + 1, u, u + 1} e.coefficient
      ((constantModules W R).obj (P.X r)) V b p) →
    HEq x (tensorSection.{u + 1, u, u + 1} (limit.π (coefficientTower W I) (op n))
      (((completedComplex W I e.coefficient).obj P).X r) V a m) →
    HEq ((((e.reduction n P hP).hom.f r).val.app V) x)
      (tensorSection.{u + 1, u, u + 1} (quotientMap W I n)
        ((constantModules W R).obj (P.X r)) V
          (a * (show (proEtaleConstantRing W (Quotient R I n)).obj.obj V from
            (limit.π (coefficientTower W I) (op n)).hom.app V b)) p)) ∧
  (∀ (n : ℕ) (P Q : ScalarComplex R)
    (hP : IsBoundedFiniteProjective P) (hQ : IsBoundedFiniteProjective Q) (f : P ⟶ Q),
    ((extension.{u + 1, u, u + 1} (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex
      (.up ℤ)).map ((completedComplex W I e.coefficient).map f) ≫ (e.reduction n Q hQ).hom =
      (e.reduction n P hP).hom ≫ (finiteComplex W I n).map f) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P)
    (r : ℤ) (V : W.ProEtᵒᵖ)
    (m : (((completedComplex W I e.coefficient).obj P).X r).val.obj V),
    HEq ((((e.unit n P hP).f r).val.app V) m)
      (tensorSection.{u + 1, u, u + 1} (limit.π (coefficientTower W I) (op n))
        (((completedComplex W I e.coefficient).obj P).X r) V 1 m)) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (r : ℤ) (V : W.ProEtᵒᵖ)
    (m : (((finiteOverCompleted W I (n + 1)).obj P).X r).val.obj V)
    (x : (((finiteComplex W I (n + 1)).obj P).X r).val.obj V),
    HEq m x → HEq ((((e.step n).app P).f r).val.app V m)
      ((((d.step n).app P).f r).val.app V x)) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P)
    (r : ℤ) (V : W.ProEtᵒᵖ)
    (a : (proEtaleConstantRing W (Quotient R I (n + 1))).obj.obj V)
    (m : (((completedComplex W I e.coefficient).obj P).X r).val.obj V)
    (x : (((reducedComplex W I e.coefficient (n + 1)).obj P).X r).val.obj V),
    HEq x (tensorSection.{u + 1, u, u + 1}
      (limit.π (coefficientTower W I) (op (n + 1)))
        (((completedComplex W I e.coefficient).obj P).X r) V a m) →
    HEq ((((e.reducedStep n P hP).f r).val.app V) x)
      (tensorSection.{u + 1, u, u + 1} (limit.π (coefficientTower W I) (op n))
        (((completedComplex W I e.coefficient).obj P).X r) V
          ((constantMap W (quotientStep I n)).hom.app V a) m)) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    e.unit (n + 1) P hP ≫ e.reducedStep n P hP = e.unit n P hP) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    e.reducedStep n P hP ≫
      ((restriction W (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex
        (.up ℤ)).map (e.reduction n P hP).hom =
      ((restriction W (limit.π (coefficientTower W I) (op (n + 1)))).mapHomologicalComplex
        (.up ℤ)).map (e.reduction (n + 1) P hP).hom ≫ (e.step n).app P) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    e.alpha n P hP = e.unit n P hP ≫
      ((restriction W (limit.π (coefficientTower W I) (op n))).mapHomologicalComplex
        (.up ℤ)).map (e.reduction n P hP).hom) ∧
  (∀ (n : ℕ) (P Q : ScalarComplex R)
    (hP : IsBoundedFiniteProjective P) (hQ : IsBoundedFiniteProjective Q) (f : P ⟶ Q),
    (completedComplex W I e.coefficient).map f ≫ e.alpha n Q hQ =
      e.alpha n P hP ≫ (finiteOverCompleted W I n).map f) ∧
  (∀ (n : ℕ) (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P),
    e.alpha (n + 1) P hP ≫ (e.step n).app P = e.alpha n P hP)

/-- The reduction tower as an actual functor to complexes over the completed ring.
Source: Stacks 08TC (blueprint: def-a1-constant-complex-quotient-model). -/
abbrev ReductionData.tower (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) :=
  let F : ℕᵒᵖ ⥤ (ScalarComplex R ⥤
      CochainComplex (proEtaleRingModules W (completed W I)) ℤ) :=
    { obj := fun n ↦ finiteOverCompleted W I n.unop
      map := (Functor.ofOpSequence e.step).map
      map_id := (Functor.ofOpSequence e.step).map_id
      map_comp := (Functor.ofOpSequence e.step).map_comp }
  F.flip

/-- The product map induced by the normalized quotient units and balanced reductions.
Source: Stacks 08TC (blueprint: def-a1-constant-complex-quotient-model). -/
def ReductionData.productMap (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d)
    (P : ScalarComplex R) (hP : IsBoundedFiniteProjective P) :
    (completedComplex W I e.coefficient).obj P ⟶
      ∏ᶜ (fun n ↦ ((e.tower W I).obj P).obj (op n)) :=
  Pi.lift (fun n ↦ e.alpha n P hP)


end AlgebraicGeometry.ConstantComplexBaseChange
