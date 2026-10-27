/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import all Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import all Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation

/-! # Adjunction and resolution normalization of ambient compositors

Source: Stacks Project, Tags 0D6E, 09T5, 03D3, 08BJ, 070I and 0DV0
(blueprint: lem-sf-ambient-adjunction-compositor-normalization).

The records package the published ordinary operations and their equations. Neither
realization constructs a new module category or chooses a new adjunction. The system
realization uses the whole ringed diagram category, before evaluation or total limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.AmbientCompositor

/-- A package of existing ordinary operations, with their actual specified adjunctions.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
structure Operations where
  M : Scheme.{u} → Type (u + 2)
  [category : ∀ X, Category.{u + 1} (M X)]
  [abelian : ∀ X, Abelian (M X)]
  [derived : ∀ X, HasDerivedCategory.{u + 2} (M X)]
  [kinjective : ∀ X, Abelian.HasKInjectiveResolutions (M X)]
  pull : ∀ {X Y}, (X ⟶ Y) → M Y ⥤ M X
  push : ∀ {X Y}, (X ⟶ Y) → M X ⥤ M Y
  extension : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion j], M X ⥤ M Y
  [pullAdditive : ∀ {X Y} (f : X ⟶ Y), (pull f).Additive]
  [pullLimits : ∀ {X Y} (f : X ⟶ Y), PreservesFiniteLimits (pull f)]
  [pullColimits : ∀ {X Y} (f : X ⟶ Y), PreservesFiniteColimits (pull f)]
  [pushAdditive : ∀ {X Y} (f : X ⟶ Y), (push f).Additive]
  [extensionAdditive : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion j], (extension j).Additive]
  [extensionLimits : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion j],
    PreservesFiniteLimits (extension j)]
  [extensionColimits : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion j],
    PreservesFiniteColimits (extension j)]
  adj : ∀ {X Y} (f : X ⟶ Y), pull f ⊣ push f
  openAdj : ∀ {X Y} (j : X ⟶ Y) [IsOpenImmersion j], extension j ⊣ pull j
  pullComp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), pull (f ≫ g) ≅ pull g ⋙ pull f
  pullId : ∀ X, pull (𝟙 X) ≅ 𝟭 (M X)

attribute [instance] Operations.category Operations.abelian Operations.derived
  Operations.kinjective Operations.pullAdditive Operations.pullLimits Operations.pullColimits
  Operations.pushAdditive Operations.extensionAdditive Operations.extensionLimits
  Operations.extensionColimits

namespace Operations
variable (o : Operations.{u})

/-- The published D operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
abbrev D (X : Scheme.{u}) := DerivedCategory (o.M X)

/-- The published P operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) := (o.pull f).mapDerivedCategory

/-- The published S operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
abbrev S {X Y : Scheme.{u}} (f : X ⟶ Y) := (o.push f).rightDerivedFunctor

/-- The published J operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
abbrev J {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (o.extension j).mapDerivedCategory

/-- The published adjunction operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) : o.P f ⊣ o.S f :=
  (o.adj f).mapDerivedCategoryRightDerivedAdjunction

/-- The published openAdjunction operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def openAdjunction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    o.J j ⊣ o.P j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (o.openAdj j)

/-- The ordinary direct-image comparison fixed by the specified adjunctions.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def ordinaryC {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.push f ⋙ o.push g ≅ o.push (f ≫ g) :=
  conjugateIsoEquiv ((o.adj g).comp (o.adj f)) (o.adj (f ≫ g)) (o.pullComp f g)

/-- The ordinary open-extension comparison fixed by successive open adjuncts.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def ordinaryE {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    o.extension j ⋙ o.extension b ≅ o.extension (j ≫ b) :=
  Adjunction.leftAdjointCompIso (o.openAdj j) (o.openAdj b) (o.openAdj (j ≫ b))
    (o.pullComp j b).symm

/-- Localization of the tensor/unit-normalized ordinary inverse-image comparison.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def d {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.P g ⋙ o.P f ≅ o.P (f ≫ g) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (o.pullComp f g).symm

/-- Inverse adjunction conjugate of d, with no new choice of direct image.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def c {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.S f ⋙ o.S g ≅ o.S (f ≫ g) :=
  (conjugateIsoEquiv (o.adjunction (f ≫ g))
    ((o.adjunction g).comp (o.adjunction f)) (o.d f g)).symm

/-- Inverse open-adjunction conjugate of d.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def e {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] : o.J j ⋙ o.J b ≅ o.J (j ≫ b) :=
  Adjunction.leftAdjointCompIso (o.openAdjunction j) (o.openAdjunction b)
    (o.openAdjunction (j ≫ b)) (o.d j b)

/-- The published pId operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def pId (X : Scheme.{u}) : o.P (𝟙 X) ≅ 𝟭 (o.D X) :=
  Functor.mapDerivedCategoryNatIso (o.pullId X) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The published sId operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def sId (X : Scheme.{u}) : o.S (𝟙 X) ≅ 𝟭 (o.D X) :=
  (conjugateIsoEquiv Adjunction.id (o.adjunction (𝟙 X)) (o.pId X)).symm

/-- The published jId operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def jId (X : Scheme.{u}) : o.J (𝟙 X) ≅ 𝟭 (o.D X) :=
  Adjunction.leftAdjointIdIso (o.openAdjunction (𝟙 X)) (o.pId X)

/-- The published jCongr operation or its canonical adjunction normalization.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def jCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : o.J f ≅ o.J g :=
  eqToIso (by cases h; rfl)

end Operations

/-- Finite-level realization using the published intrinsic constant-ring operations.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def finite (A : Type u) [CommRing A] [Finite A] : Operations.{u} where
  M X := proEtaleRingModules X (proEtaleConstantRing X A)
  pull f := sfIntrinsicPullback A f
  push f := proEtaleConstantModuleDirectImage f A
  extension j _ := sfIntrinsicExtensionByZero j A
  adj f := sfIntrinsicConstantModuleAdjunction f A
  openAdj j _ := sfIntrinsicOpenAdjunction A j
  pullComp f g := sfIntrinsicPullbackComp A f g
  pullId X := sfIntrinsicPullbackId A X

/-- The simultaneous ringed-sequence realization, reusing the published system operations.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def systems (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) : Operations.{u} where
  M X := ProEtale.SemilinearProperOpen.Modules C τ X
  pull f := ProEtale.SemilinearProperOpen.pull C τ f
  push f := ProEtale.SemilinearProperOpen.push C τ f
  extension j _ := ProEtale.SemilinearProperOpen.extension C τ j
  adj f := ProEtale.SemilinearProperOpen.ordinaryAdj C τ f
  openAdj j _ := ProEtale.SemilinearProperOpen.ordinaryOpenAdj C τ j
  pullComp f g := ProEtale.SemilinearProperOpen.pullComp C τ f g
  pullId X := Adjunction.leftAdjointIdIso (ProEtale.SemilinearProperOpen.ordinaryAdj C τ (𝟙 X))
    (ProEtale.SemilinearProperOpen.pushId_existsUnique C τ X).choose

/-- The positive quotient tower, starting at A₁ and retaining the actual quotient maps.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
abbrev coefficientTower (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) : CommRingCat.{u + 1} :=
  .of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The quotient transitions of the coefficient tower.
Source: Stacks 0D6E, 09T5, 03D3; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def coefficientTransition (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    coefficientTower l E (n + 1) ⟶ coefficientTower l E n :=
  CommRingCat.ofHom (RingHom.ulift (Padic.coefficientExtensionTransition l E (n + 1)))

/-- Both units, counits and Hom bijections are identified by inverse-conjugate comparisons.
Source: Stacks 0D6E, 09T5, 03D3, 0DV0
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
structure Normalized
    {A B : Type (u + 2)} [Category.{u + 2} A] [Category.{u + 2} B]
    {Lc Ls : A ⥤ B} {Rc Rs : B ⥤ A} (ac : Lc ⊣ Rc) (as_ : Ls ⊣ Rs)
    (a : Lc ≅ Ls) (b : Rc ≅ Rs) : Prop where
  unit : ∀ M : A,
    ac.unit.app M ≫ Rc.map (a.hom.app M) ≫ b.hom.app (Ls.obj M) = as_.unit.app M
  counit : ∀ N : B,
    Lc.map (b.hom.app N) ≫ a.hom.app (Rs.obj N) ≫ as_.counit.app N = ac.counit.app N
  hom : ∀ (M : A) (N : B) (h : Ls.obj M ⟶ N),
    as_.homEquiv M N h = ac.homEquiv M N (a.hom.app M ≫ h) ≫ b.hom.app N

/-- A scheme over the specified algebraic closure whose structure map is of finite type.
No separatedness is imposed. Source: the ambient convention of Stacks 0D6E
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
abbrev FiniteTypeOver (F : FiniteFieldDatum.{u}) (X : Scheme.{u}) : Prop :=
  ∃ a : X ⟶ Spec (.of F.k), LocallyOfFiniteType a ∧ QuasiCompact a

/-- Every asserted normalization and coherence equation, on the actual derived categories.
Source: Stacks 0D6E, 09T5, 03D3, 0DV0
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
structure Laws (F : FiniteFieldDatum.{u}) (o : Operations.{u}) : Prop where
  direct : ∀ {X Y Z : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    Normalized ((o.adjunction g).comp (o.adjunction f)) (o.adjunction (f ≫ g))
      (o.d f g) (o.c f g)
  openExtension : ∀ {X Y Z : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b],
    Normalized ((o.openAdjunction j).comp (o.openAdjunction b))
      (o.openAdjunction (j ≫ b)) (o.e j b) (o.d j b)
  kinjective : ∀ {X Y Z : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (o.M X) ℤ) [I.IsKInjective],
    CochainComplex.IsKInjective (((o.push f).mapHomologicalComplex (.up ℤ)).obj I) ∧
    CochainComplex.IsKInjective
      (((o.push g).mapHomologicalComplex (.up ℤ)).obj
        (((o.push f).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (let K := (HomotopyCategory.quotient (o.M X) (.up ℤ)).obj I
     DerivedCategory.Qh.map
         ((NatTrans.mapHomotopyCategory (o.ordinaryC f g).hom (.up ℤ)).app K) ≫
       (o.push (f ≫ g)).rightDerivedFunctorUnit.app K =
     DerivedCategory.Qh.map
         ((Functor.mapHomotopyCategoryCompIso (Iso.refl (o.push f ⋙ o.push g))
           (.up ℤ)).inv.app K) ≫
       (o.push g).rightDerivedFunctorUnit.app (((o.push f).mapHomotopyCategory (.up ℤ)).obj K) ≫
       (o.S g).map ((o.push f).rightDerivedFunctorUnit.app K) ≫
       (o.c f g).hom.app (DerivedCategory.Qh.obj K))
  localizedOpen : ∀ {X Y Z : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b],
    o.e j b = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (o.ordinaryE j b)
  s_assoc : ∀ {X Y Z T : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (_hT : FiniteTypeOver F T)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D X),
    (o.S h).map ((o.c f g).hom.app M) ≫ (o.c (f ≫ g) h).hom.app M =
      (o.c g h).hom.app ((o.S f).obj M) ≫ (o.c f (g ≫ h)).hom.app M ≫
        (eqToIso (congrArg o.S (Category.assoc f g h))).inv.app M
  s_unit : ∀ {X Y : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y)
    (f : X ⟶ Y) (M : o.D X),
    ((o.c (𝟙 X) f).hom.app M ≫
        (eqToIso (congrArg o.S (Category.id_comp f))).hom.app M =
      (o.S f).map ((o.sId X).hom.app M)) ∧
    ((o.c f (𝟙 Y)).hom.app M ≫
        (eqToIso (congrArg o.S (Category.comp_id f))).hom.app M =
      (o.sId Y).hom.app ((o.S f).obj M))
  j_assoc : ∀ {X Y Z T : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (_hT : FiniteTypeOver F T)
    (j : X ⟶ Y) (b : Y ⟶ Z) (a : Z ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a] (M : o.D X),
    (o.J a).map ((o.e j b).hom.app M) ≫ (o.e (j ≫ b) a).hom.app M =
      (o.e b a).hom.app ((o.J j).obj M) ≫ (o.e j (b ≫ a)).hom.app M ≫
        (o.jCongr (Category.assoc j b a)).inv.app M
  j_unit : ∀ {X Y : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y)
    (j : X ⟶ Y) [IsOpenImmersion j] (M : o.D X),
    ((o.e (𝟙 X) j).hom.app M ≫ (o.jCongr (Category.id_comp j)).hom.app M =
      (o.J j).map ((o.jId X).hom.app M)) ∧
    ((o.e j (𝟙 Y)).hom.app M ≫ (o.jCongr (Category.comp_id j)).hom.app M =
      (o.jId Y).hom.app ((o.J j).obj M))
  threefold : ∀ {X Y Z T : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (_hT : FiniteTypeOver F T)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D T) (N : o.D X) (k : (o.P ((f ≫ g) ≫ h)).obj M ⟶ N),
    (o.adjunction ((f ≫ g) ≫ h)).homEquiv M N k =
      (o.adjunction h).homEquiv M ((o.S g).obj ((o.S f).obj N))
        ((o.adjunction g).homEquiv ((o.P h).obj M) ((o.S f).obj N)
          ((o.adjunction f).homEquiv ((o.P g).obj ((o.P h).obj M)) N
            ((o.d f g).hom.app ((o.P h).obj M) ≫ (o.d (f ≫ g) h).hom.app M ≫ k))) ≫
        (o.S h).map ((o.c f g).hom.app N) ≫ (o.c (f ≫ g) h).hom.app N
  threefoldOpen : ∀ {X Y Z T : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (_hT : FiniteTypeOver F T)
    (j : X ⟶ Y) (b : Y ⟶ Z) (a : Z ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a]
    (M : o.D X) (N : o.D T) (k : (o.J ((j ≫ b) ≫ a)).obj M ⟶ N),
    (o.openAdjunction ((j ≫ b) ≫ a)).homEquiv M N k =
      (o.openAdjunction j).homEquiv M ((o.P b).obj ((o.P a).obj N))
        ((o.openAdjunction b).homEquiv ((o.J j).obj M) ((o.P a).obj N)
          ((o.openAdjunction a).homEquiv ((o.J b).obj ((o.J j).obj M)) N
            ((o.J a).map ((o.e j b).hom.app M) ≫ (o.e (j ≫ b) a).hom.app M ≫ k))) ≫
        (o.d j b).hom.app ((o.P a).obj N) ≫ (o.d (j ≫ b) a).hom.app N
  threefoldRight : ∀ {X Y Z T : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y)
    (_hZ : FiniteTypeOver F Z) (_hT : FiniteTypeOver F T)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D T) (N : o.D X) (k : (o.P (f ≫ (g ≫ h))).obj M ⟶ N),
    (o.adjunction (f ≫ (g ≫ h))).homEquiv M N k =
      (o.adjunction h).homEquiv M ((o.S g).obj ((o.S f).obj N))
        ((o.adjunction g).homEquiv ((o.P h).obj M) ((o.S f).obj N)
          ((o.adjunction f).homEquiv ((o.P g).obj ((o.P h).obj M)) N
            ((o.P f).map ((o.d g h).hom.app M) ≫ (o.d f (g ≫ h)).hom.app M ≫ k))) ≫
        (o.c g h).hom.app ((o.S f).obj N) ≫ (o.c f (g ≫ h)).hom.app N
  threefoldOpenRight : ∀ {X Y Z T : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y)
    (_hZ : FiniteTypeOver F Z) (_hT : FiniteTypeOver F T)
    (j : X ⟶ Y) (b : Y ⟶ Z) (a : Z ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a]
    (M : o.D X) (N : o.D T) (k : (o.J (j ≫ (b ≫ a))).obj M ⟶ N),
    (o.openAdjunction (j ≫ (b ≫ a))).homEquiv M N k =
      (o.openAdjunction j).homEquiv M ((o.P b).obj ((o.P a).obj N))
        ((o.openAdjunction b).homEquiv ((o.J j).obj M) ((o.P a).obj N)
          ((o.openAdjunction a).homEquiv ((o.J b).obj ((o.J j).obj M)) N
            ((o.e b a).hom.app ((o.J j).obj M) ≫ (o.e j (b ≫ a)).hom.app M ≫ k))) ≫
        (o.P j).map ((o.d b a).hom.app N) ≫ (o.d j (b ≫ a)).hom.app N

/-- Ordinary direct-image normalization on every pro-etale test object.
Source: Stacks 0D6E, 09T5, 03D3, 0DV0
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def FiniteSections (F : FiniteFieldDatum.{u}) (A : Type u) [CommRing A] [Finite A] : Prop :=
  ∀ {X Y Z : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : (finite A).M X) (V : Z.ProEt)
    (x : M.val.obj (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj V)))),
    (((finite A).ordinaryC f g).hom.app M).val.app (op V) x =
      M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op x

/-- Ordinary composition is normalized before finite evaluation on the whole diagram site.
Source: Stacks 0D6E, 09T5, 03D3, 0DV0
(blueprint: lem-sf-ambient-adjunction-compositor-normalization). -/
def SystemSections (F : FiniteFieldDatum.{u}) (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) : Prop :=
  ∀ {X Y Z : Scheme.{u}}
    (_hX : FiniteTypeOver F X) (_hY : FiniteTypeOver F Y) (_hZ : FiniteTypeOver F Z)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    (systems C τ).ordinaryC f g = ProEtale.SemilinearProperOpen.pushComp C τ f g

private abbrev pComp (o : Operations.{u}) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) := (o.d f g).symm

private theorem mapDerived_symm_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ≅ G) :
    (Functor.mapDerivedCategoryNatIso a.symm).inv =
      (Functor.mapDerivedCategoryNatIso a).hom := by
  simpa only [Iso.symm_symm_eq] using
    (Functor.mapDerivedCategoryNatIso_symm a.symm).symm

private theorem pComp_eq (o : Operations.{u}) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pComp o f g = Functor.mapDerivedCategoryNatIso (o.pullComp f g) ≪≫
      Functor.mapDerivedCategoryCompIso (o.pull g) (o.pull f) := by
  apply Iso.ext
  simp only [pComp, Operations.d, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, Iso.trans_hom, mapDerived_symm_inv]

private structure PullCoherence (o : Operations.{u}) : Prop where
  assoc : ∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    pComp o f (g ≫ h) ≪≫ Functor.isoWhiskerRight (pComp o g h) (o.P f) =
      eqToIso (congrArg o.P (Category.assoc f g h).symm) ≪≫
        pComp o (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (o.P h) (pComp o f g)
  left_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    eqToIso (congrArg o.P (Category.id_comp f).symm) ≪≫ pComp o (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (o.P f) (o.pId X) ≪≫ Functor.rightUnitor (o.P f) = Iso.refl _
  right_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    eqToIso (congrArg o.P (Category.comp_id f).symm) ≪≫ pComp o f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (o.pId Y) (o.P f) ≪≫ Functor.leftUnitor (o.P f) = Iso.refl _

private structure OrdinaryPullCoherence (o : Operations.{u}) : Prop where
  assoc : ∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    o.pullComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (o.pullComp g h) (o.pull f) =
      eqToIso (congrArg o.pull (Category.assoc f g h).symm) ≪≫
        o.pullComp (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (o.pull h) (o.pullComp f g)
  left_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    eqToIso (congrArg o.pull (Category.id_comp f).symm) ≪≫ o.pullComp (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (o.pull f) (o.pullId X) ≪≫ Functor.rightUnitor (o.pull f) = Iso.refl _
  right_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    eqToIso (congrArg o.pull (Category.comp_id f).symm) ≪≫ o.pullComp f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (o.pullId Y) (o.pull f) ≪≫ Functor.leftUnitor (o.pull f) = Iso.refl _

private theorem derived_pull_transport (o : Operations.{u})
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg o.pull h))).hom =
      (eqToIso (congrArg o.P h)).hom := by
  cases h
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem descend_pull_coherence (o : Operations.{u})
    (hp : OrdinaryPullCoherence o) : PullCoherence o := by
  constructor
  · intro X Y Z T f g h
    have hh := ProEtale.StrictTower.descend_coherence (o.pull h) (o.pull g) (o.pull f)
      (o.pull (g ≫ h)) (o.pull (f ≫ g))
      (o.pull (f ≫ g ≫ h)) (o.pull ((f ≫ g) ≫ h))
      (o.pullComp g h) (o.pullComp f g)
      (o.pullComp f (g ≫ h)) (o.pullComp (f ≫ g) h)
      (eqToIso (congrArg o.pull (Category.assoc f g h).symm)) (hp.assoc f g h)
    rw [derived_pull_transport o (Category.assoc f g h).symm] at hh
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [pComp_eq, Operations.P, Iso.trans_hom,
      Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      Functor.map_comp] using congr_app hh M
  · intro X Y f
    have hh := ProEtale.StrictTower.descend_left_unit (o.pull f)
      (o.pull (𝟙 X ≫ f)) (o.pull (𝟙 X))
      (eqToIso (congrArg o.pull (Category.id_comp f).symm))
      (o.pullComp (𝟙 X) f) (o.pullId X) (hp.left_unit f)
    rw [derived_pull_transport o (Category.id_comp f).symm] at hh
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hm := congr_app hh M
    simp only [pComp_eq, Operations.pId, Operations.P,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Iso.refl_hom, NatTrans.id_app, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj, NatTrans.id_app] at hm ⊢
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc, Category.comp_id, Functor.map_comp] using hm
  · intro X Y f
    have hh := ProEtale.StrictTower.descend_right_unit (o.pull f)
      (o.pull (f ≫ 𝟙 Y)) (o.pull (𝟙 Y))
      (eqToIso (congrArg o.pull (Category.comp_id f).symm))
      (o.pullComp f (𝟙 Y)) (o.pullId Y) (hp.right_unit f)
    rw [derived_pull_transport o (Category.comp_id f).symm] at hh
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hm := congr_app hh M
    simp only [pComp_eq, Operations.pId, Operations.P,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Iso.refl_hom, NatTrans.id_app, Functor.map_comp, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj, NatTrans.id_app] at hm ⊢
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Category.assoc, Category.comp_id, Functor.map_comp] using hm

private theorem left_comp_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') (M : A) :
    (a.comp b).homEquiv M _ ((Adjunction.leftAdjointCompIso a b c η).hom.app M) ≫
      η.hom.app (L''.obj M) = c.unit.app M := by
  rw [Adjunction.homEquiv_unit, Category.assoc, η.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c η).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← R''.map_comp, Iso.inv_hom_id_app, R''.map_id]
  exact Category.comp_id _

private theorem left_comp_unique
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') :
    ((a.comp b).ofNatIsoRight η).leftAdjointUniq c =
      Adjunction.leftAdjointCompIso a b c η := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (((a.comp b).ofNatIsoRight η).homEquiv M _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  exact (left_comp_unit a b c η M).symm

private theorem normalized_conjugate
    {A B : Type (u + 2)} [Category.{u + 2} A] [Category.{u + 2} B]
    {Lc Ls : A ⥤ B} {Rc Rs : B ⥤ A} (ac : Lc ⊣ Rc) (as_ : Ls ⊣ Rs)
    (a : Lc ≅ Ls) :
    Normalized ac as_ a (conjugateIsoEquiv ac as_ a.symm) := by
  have hh (M : A) (N : B) (h : Ls.obj M ⟶ N) :
      as_.homEquiv M N h = ac.homEquiv M N (a.hom.app M ≫ h) ≫
        (conjugateIsoEquiv ac as_ a.symm).hom.app N := by
    have ht : ac.homEquiv M N (a.hom.app M ≫ h) ≫
        (conjugateIsoEquiv ac as_ a.symm).hom.app N =
        as_.homEquiv M N (a.inv.app M ≫ (a.hom.app M ≫ h)) := by
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      rw [Category.assoc, (conjugateIsoEquiv ac as_ a.symm).hom.naturality,
        ← Category.assoc]
      change (ac.unit.app M ≫ (conjugateEquiv ac as_ a.inv).app _) ≫ _ = _
      rw [unit_conjugateEquiv, Category.assoc, ← Rs.map_comp]
    simpa only [Iso.inv_hom_id_app_assoc] using ht.symm
  refine ⟨?_, ?_, hh⟩
  · intro M
    have hu := hh M (Ls.obj M) (𝟙 _)
    rw [as_.homEquiv_id] at hu
    simpa [Adjunction.homEquiv_unit, Category.assoc] using hu.symm
  · intro N
    rw [a.hom.naturality_assoc]
    change a.hom.app (Rc.obj N) ≫ Ls.map
      ((conjugateEquiv ac as_ a.inv).app N) ≫ as_.counit.app N = _
    rw [conjugateEquiv_counit, Iso.hom_inv_id_app_assoc]

private theorem direct_normalized (o : Operations.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Normalized ((o.adjunction g).comp (o.adjunction f)) (o.adjunction (f ≫ g))
      (o.d f g) (o.c f g) := by
  have h := normalized_conjugate ((o.adjunction g).comp (o.adjunction f))
    (o.adjunction (f ≫ g)) (o.d f g)
  simpa only [Operations.c, conjugateIsoEquiv_iso_symm] using h

private theorem open_normalized (o : Operations.{u})
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    Normalized ((o.openAdjunction j).comp (o.openAdjunction b))
      (o.openAdjunction (j ≫ b)) (o.e j b) (o.d j b) := by
  have h := normalized_conjugate ((o.openAdjunction j).comp (o.openAdjunction b))
    (o.openAdjunction (j ≫ b)) (o.e j b)
  have he : conjugateIsoEquiv ((o.openAdjunction j).comp (o.openAdjunction b))
      (o.openAdjunction (j ≫ b)) (o.e j b).symm = o.d j b := by
    simp [Operations.e, Adjunction.leftAdjointCompIso, conjugateIsoEquiv_iso_symm]
  rwa [he] at h

private theorem c_hom_eq (o : Operations.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (o.c f g).hom =
      (let _ := (o.adj f).preservesKInjectiveComplexes
       (Functor.rightDerivedFunctorCompIso' (o.push f) (o.push g) (o.ordinaryC f g)).hom) := by
  let := (o.adj f).preservesKInjectiveComplexes
  have hh := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (o.adj f) (o.adj g) (o.adj (f ≫ g)) (o.ordinaryC f g) (o.pullComp f g) rfl
  rw [hh]
  change (conjugateIsoEquiv ((o.adjunction g).comp (o.adjunction f))
      (o.adjunction (f ≫ g)) (o.d f g).symm).hom = _
  rfl

private theorem c_fac (o : Operations.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (o.M X) (.up ℤ)) :
    DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (o.ordinaryC f g).hom (.up ℤ)).app K) ≫
      (o.push (f ≫ g)).rightDerivedFunctorUnit.app K =
    DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (o.push f ⋙ o.push g))
          (.up ℤ)).inv.app K) ≫
      (o.push g).rightDerivedFunctorUnit.app (((o.push f).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (o.S g).map ((o.push f).rightDerivedFunctorUnit.app K) ≫
      (o.c f g).hom.app (DerivedCategory.Qh.obj K) := by
  let := (o.adj f).preservesKInjectiveComplexes
  rw [c_hom_eq]
  have hh : (Functor.rightDerivedFunctorCompUnit (o.push f) (o.push g)).app K ≫
      (Functor.rightDerivedFunctorCompIso' (o.push f) (o.push g)
        (o.ordinaryC f g)).hom.app (DerivedCategory.Qh.obj K) =
      (o.push f ⋙ o.push g).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatTrans (o.ordinaryC f g).hom).app
          (DerivedCategory.Qh.obj K) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  simpa only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedNatTrans_app,
    Category.assoc, Operations.S] using hh.symm

private theorem open_localized (o : Operations.{u})
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    o.e j b = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (o.ordinaryE j b) := by
  let ac := (o.openAdj j).mapHomologicalComplex (.up ℤ)
  let bc := (o.openAdj b).mapHomologicalComplex (.up ℤ)
  let dc := (o.openAdj (j ≫ b)).mapHomologicalComplex (.up ℤ)
  let η := (o.pullComp j b).symm
  let ηc := Functor.mapHomologicalComplexCompIso η (.up ℤ)
  let ν := o.ordinaryE j b
  let νc := Functor.mapHomologicalComplexCompIso ν (.up ℤ)
  have hn : ∀ K, (ac.comp bc).homEquiv _ _ (νc.hom.app K) ≫
      ηc.hom.app (((o.extension (j ≫ b)).mapHomologicalComplex (.up ℤ)).obj K) =
        dc.unit.app K := by
    intro K
    apply HomologicalComplex.hom_ext
    intro i
    have h := left_comp_unit (o.openAdj j) (o.openAdj b) (o.openAdj (j ≫ b)) η
      (K.X i)
    rw [Adjunction.homEquiv_unit] at h ⊢
    exact h
  have hcomp := normalizedAdjunction_composition ac bc
    (o.openAdjunction j) (o.openAdjunction b)
    (o.extension j).mapDerivedCategoryFactors.hom
    (o.extension b).mapDerivedCategoryFactors.hom
    (o.pull j).mapDerivedCategoryFactors.inv (o.pull b).mapDerivedCategoryFactors.inv
    (ProEtale.SemilinearProperOpen.exact_hom_fac (o.openAdj j))
    (ProEtale.SemilinearProperOpen.exact_hom_fac (o.openAdj b))
  have he (K : CochainComplex (o.M X) ℤ) := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q) (ac.comp bc) dc
    ((o.openAdjunction j).comp (o.openAdjunction b)) (o.openAdjunction (j ≫ b))
    (fun K ↦ (o.J b).map ((o.extension j).mapDerivedCategoryFactors.hom.app K) ≫
      (o.extension b).mapDerivedCategoryFactors.hom.app
        (((o.extension j).mapHomologicalComplex (.up ℤ)).obj K))
    (o.extension (j ≫ b)).mapDerivedCategoryFactors.hom.app
    (fun L ↦ (o.pull j).mapDerivedCategoryFactors.inv.app
      (((o.pull b).mapHomologicalComplex (.up ℤ)).obj L) ≫
      (o.P j).map ((o.pull b).mapDerivedCategoryFactors.inv.app L))
    (o.pull (j ≫ b)).mapDerivedCategoryFactors.inv.app
    (by intros P L f; simpa only [Category.assoc] using hcomp P L f)
    (ProEtale.SemilinearProperOpen.exact_hom_fac (o.openAdj (j ≫ b)))
    ηc (o.d j b) νc.hom.app hn
    (by
      intro L
      have hv : ηc.hom.app L = (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app L := by
        ext i
        rfl
      rw [hv]
      simpa only [Category.assoc, Operations.P, Operations.d, η,
        Functor.exactDerivedRestrictionComposition] using
        Functor.exactDerivedRestrictionComposition_inv_factors
          (o.pull b) (o.pull j) (o.pull (j ≫ b)) η L) K
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (o.M X) (.up ℤ))
  intro K
  rw [← cancel_mono ((o.extension (j ≫ b)).mapDerivedCategoryFactors.hom.app K)]
  have hk := he K
  rw [left_comp_unique] at hk
  change (o.e j b).hom.app (DerivedCategory.Q.obj K) ≫ _ = _ at hk
  rw [hk]
  have hv : νc.hom.app K = (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app K := by
    ext i
    rfl
  rw [hv]
  simpa only [Category.assoc, Operations.J, ν,
    Functor.exactDerivedRestrictionComposition] using
    (Functor.exactDerivedRestrictionComposition_hom_factors
      (o.extension j) (o.extension b) (o.extension (j ≫ b)) ν K).symm

private theorem threefold_direct (o : Operations.{u})
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D T) (N : o.D X) (k : (o.P ((f ≫ g) ≫ h)).obj M ⟶ N) :
    (o.adjunction ((f ≫ g) ≫ h)).homEquiv M N k =
      (o.adjunction h).homEquiv M ((o.S g).obj ((o.S f).obj N))
        ((o.adjunction g).homEquiv ((o.P h).obj M) ((o.S f).obj N)
          ((o.adjunction f).homEquiv ((o.P g).obj ((o.P h).obj M)) N
            ((o.d f g).hom.app ((o.P h).obj M) ≫ (o.d (f ≫ g) h).hom.app M ≫ k))) ≫
        (o.S h).map ((o.c f g).hom.app N) ≫ (o.c (f ≫ g) h).hom.app N := by
  rw [(direct_normalized o (f ≫ g) h).hom]
  simp only [Adjunction.comp_homEquiv]
  change (o.adjunction h).homEquiv M ((o.S (f ≫ g)).obj N)
      ((o.adjunction (f ≫ g)).homEquiv ((o.P h).obj M) N
        ((o.d (f ≫ g) h).hom.app M ≫ k)) ≫
      (o.c (f ≫ g) h).hom.app N = _
  rw [(direct_normalized o f g).hom]
  rw [(o.adjunction h).homEquiv_naturality_right]
  simp only [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans, Equiv.coe_fn_mk, Function.comp_apply]
  simp only [Category.assoc]
  rfl

private theorem threefold_direct_right (o : Operations.{u})
    {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D T) (N : o.D X) (k : (o.P (f ≫ (g ≫ h))).obj M ⟶ N) :
    (o.adjunction (f ≫ (g ≫ h))).homEquiv M N k =
      (o.adjunction h).homEquiv M ((o.S g).obj ((o.S f).obj N))
        ((o.adjunction g).homEquiv ((o.P h).obj M) ((o.S f).obj N)
          ((o.adjunction f).homEquiv ((o.P g).obj ((o.P h).obj M)) N
            ((o.P f).map ((o.d g h).hom.app M) ≫ (o.d f (g ≫ h)).hom.app M ≫ k))) ≫
        (o.c g h).hom.app ((o.S f).obj N) ≫ (o.c f (g ≫ h)).hom.app N := by
  rw [(direct_normalized o f (g ≫ h)).hom]
  simp only [Adjunction.comp_homEquiv]
  change (o.adjunction (g ≫ h)).homEquiv M ((o.S f).obj N)
      ((o.adjunction f).homEquiv ((o.P (g ≫ h)).obj M) N
        ((o.d f (g ≫ h)).hom.app M ≫ k)) ≫
      (o.c f (g ≫ h)).hom.app N = _
  rw [(direct_normalized o g h).hom]
  rw [(o.adjunction f).homEquiv_naturality_left]
  simp only [Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans, Equiv.coe_fn_mk, Function.comp_apply]
  simp only [Category.assoc]
  rfl

private theorem threefold_open (o : Operations.{u})
    {X Y Z T : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z) (a : Z ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a]
    (M : o.D X) (N : o.D T) (k : (o.J ((j ≫ b) ≫ a)).obj M ⟶ N) :
    (o.openAdjunction ((j ≫ b) ≫ a)).homEquiv M N k =
      (o.openAdjunction j).homEquiv M ((o.P b).obj ((o.P a).obj N))
        ((o.openAdjunction b).homEquiv ((o.J j).obj M) ((o.P a).obj N)
          ((o.openAdjunction a).homEquiv ((o.J b).obj ((o.J j).obj M)) N
            ((o.J a).map ((o.e j b).hom.app M) ≫ (o.e (j ≫ b) a).hom.app M ≫ k))) ≫
        (o.d j b).hom.app ((o.P a).obj N) ≫ (o.d (j ≫ b) a).hom.app N := by
  rw [(open_normalized o (j ≫ b) a).hom]
  rw [Adjunction.comp_homEquiv]
  change (o.openAdjunction (j ≫ b)).homEquiv M ((o.P a).obj N)
      ((o.openAdjunction a).homEquiv ((o.J (j ≫ b)).obj M) N
        ((o.e (j ≫ b) a).hom.app M ≫ k)) ≫
      (o.d (j ≫ b) a).hom.app N = _
  rw [(open_normalized o j b).hom]
  rw [← (o.openAdjunction a).homEquiv_naturality_left]
  simp only [Adjunction.comp_homEquiv, Category.assoc]
  rfl

private theorem threefold_open_right (o : Operations.{u})
    {X Y Z T : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z) (a : Z ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a]
    (M : o.D X) (N : o.D T) (k : (o.J (j ≫ (b ≫ a))).obj M ⟶ N) :
    (o.openAdjunction (j ≫ (b ≫ a))).homEquiv M N k =
      (o.openAdjunction j).homEquiv M ((o.P b).obj ((o.P a).obj N))
        ((o.openAdjunction b).homEquiv ((o.J j).obj M) ((o.P a).obj N)
          ((o.openAdjunction a).homEquiv ((o.J b).obj ((o.J j).obj M)) N
            ((o.e b a).hom.app ((o.J j).obj M) ≫ (o.e j (b ≫ a)).hom.app M ≫ k))) ≫
        (o.P j).map ((o.d b a).hom.app N) ≫ (o.d j (b ≫ a)).hom.app N := by
  rw [(open_normalized o j (b ≫ a)).hom]
  rw [Adjunction.comp_homEquiv]
  change (o.openAdjunction j).homEquiv M ((o.P (b ≫ a)).obj N)
      ((o.openAdjunction (b ≫ a)).homEquiv ((o.J j).obj M) N
        ((o.e j (b ≫ a)).hom.app M ≫ k)) ≫
      (o.d j (b ≫ a)).hom.app N = _
  rw [(open_normalized o b a).hom]
  rw [(o.openAdjunction j).homEquiv_naturality_right]
  simp only [Adjunction.comp_homEquiv, Category.assoc]
  rfl

private theorem j_comp_transport (o : Operations.{u}) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k] (e : f ≫ g = k) :
    Adjunction.leftAdjointCompIso (o.openAdjunction f) (o.openAdjunction g)
      (o.openAdjunction k) (o.d f g ≪≫ eqToIso (congrArg o.P e)) =
        o.e f g ≪≫ o.jCongr e := by
  subst k
  simp only [Operations.jCongr, eqToIso_refl, Iso.trans_refl, Operations.e]

private theorem conjugate_right_unit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} {I RI : C ⥤ C}
    (a : F ⊣ R) (b : I ⊣ RI) (e : I ≅ 𝟭 C) (k : F ≅ I ⋙ F)
    (h : k ≪≫ Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F = Iso.refl F) :
    conjugateIsoEquiv (b.comp a) a k =
      Functor.isoWhiskerLeft R (conjugateIsoEquiv b Adjunction.id e.symm) ≪≫
        Functor.rightUnitor R := by
  have hk : k = (Functor.leftUnitor F).symm ≪≫
      Functor.isoWhiskerRight e.symm F := by
    apply Iso.ext
    have hh := congrArg Iso.hom h
    change k.hom ≫ (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F).hom = 𝟙 _ at hh
    have hi := (Iso.comp_hom_eq_id
      (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F)).1 hh
    simpa only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerRight_symm,
      Iso.symm_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom] using hi
  rw [hk, conjugateIsoEquiv_trans (b.comp a) (Adjunction.id.comp a) a,
    conjugateIsoEquiv_isoWhiskerRight b Adjunction.id a,
    conjugateIsoEquiv_iso_symm a (Adjunction.id.comp a),
    conjugateIsoEquiv_leftUnitor, Iso.symm_symm_eq]

private theorem c_eq (o : Operations.{u}) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.c f g = conjugateIsoEquiv ((o.adjunction g).comp (o.adjunction f))
      (o.adjunction (f ≫ g)) (pComp o f g) := rfl

private theorem sId_eq (o : Operations.{u}) (X : Scheme.{u}) :
    o.sId X = conjugateIsoEquiv (o.adjunction (𝟙 X)) Adjunction.id (o.pId X).symm := rfl

private theorem s_unital (o : Operations.{u}) (hp : PullCoherence o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : o.D X) :
    ((o.c (𝟙 X) f).hom.app M ≫
        (eqToIso (congrArg o.S (Category.id_comp f))).hom.app M =
      (o.S f).map ((o.sId X).hom.app M)) ∧
    ((o.c f (𝟙 Y)).hom.app M ≫
        (eqToIso (congrArg o.S (Category.comp_id f))).hom.app M =
      (o.sId Y).hom.app ((o.S f).obj M)) := by
  constructor
  · have hh := ProEtale.StrictTower.conjugate_unit (o.adjunction f)
      (o.adjunction (𝟙 X)) (o.pId X)
      (eqToIso (congrArg o.P (Category.id_comp f).symm) ≪≫ pComp o (𝟙 X) f)
      (by simpa only [Iso.trans_assoc] using hp.left_unit f)
    rw [ProEtale.SemilinearProperOpen.conjugate_transport o.P o.S
      (fun t ↦ o.adjunction t) ((o.adjunction f).comp (o.adjunction (𝟙 X)))
      (Category.id_comp f) (pComp o (𝟙 X) f)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, Operations.jId] using hm
  · have hh := conjugate_right_unit (o.adjunction f) (o.adjunction (𝟙 Y)) (o.pId Y)
      (eqToIso (congrArg o.P (Category.comp_id f).symm) ≪≫ pComp o f (𝟙 Y))
      (by simpa only [Iso.trans_assoc] using hp.right_unit f)
    rw [ProEtale.SemilinearProperOpen.conjugate_transport o.P o.S
      (fun t ↦ o.adjunction t) ((o.adjunction (𝟙 Y)).comp (o.adjunction f))
      (Category.comp_id f) (pComp o f (𝟙 Y))] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, Operations.jId] using hm

private theorem s_associative (o : Operations.{u}) (hp : PullCoherence o)
    {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D X) :
    (o.S h).map ((o.c f g).hom.app M) ≫ (o.c (f ≫ g) h).hom.app M =
      (o.c g h).hom.app ((o.S f).obj M) ≫ (o.c f (g ≫ h)).hom.app M ≫
        (eqToIso (congrArg o.S (Category.assoc f g h))).inv.app M := by
  have hp := congrArg Iso.hom (hp.assoc f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at hp
  have hh := ProEtale.StrictTower.conjugate_triangle_assoc
    (o.adjunction h) (o.adjunction g) (o.adjunction f)
    (o.adjunction (g ≫ h)) (o.adjunction (f ≫ g)) (o.adjunction (f ≫ g ≫ h))
    (pComp o g h) (pComp o f g)
    (eqToIso (congrArg (o.P) (Category.assoc f g h).symm) ≪≫
      pComp o (f ≫ g) h) (pComp o f (g ≫ h))
    (by simpa only [Iso.trans_hom, Category.assoc] using hp.symm)
  have ht := congrArg Iso.hom (ProEtale.SemilinearProperOpen.conjugate_transport (o.P) (o.S)
    (fun f ↦ o.adjunction f) ((o.adjunction h).comp (o.adjunction (f ≫ g)))
    (Category.assoc f g h) (pComp o (f ≫ g) h))
  simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom] at ht
  simp only [Iso.trans_hom] at hh
  rw [ht] at hh
  have hm := congr_app hh M
  apply (cancel_mono
    ((eqToIso (congrArg (o.S) (Category.assoc f g h))).hom.app M)).1
  simpa only [c_eq, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using hm.symm

private theorem j_associative (o : Operations.{u}) (hp : PullCoherence o)
    {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h] (M : o.D X) :
    (o.J h).map ((o.e f g).hom.app M) ≫ (o.e (f ≫ g) h).hom.app M =
      (o.e g h).hom.app ((o.J f).obj M) ≫ (o.e f (g ≫ h)).hom.app M ≫
        (o.jCongr (Category.assoc f g h)).inv.app M := by
  have hi : Functor.isoWhiskerLeft (o.P h) (pComp o f g).symm ≪≫
      ((pComp o (f ≫ g) h).symm ≪≫
        eqToIso (congrArg (o.P) (Category.assoc f g h))) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pComp o g h).symm (o.P f) ≪≫
        (pComp o f (g ≫ h)).symm := by
    have hp := congrArg Iso.symm (hp.assoc f g h)
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Iso.symm_hom, eqToIso.inv, eqToIso.hom] using
        (congr_app (congrArg Iso.hom hp) N).symm
  have hh := Adjunction.leftAdjointCompIso_assoc
    (o.openAdjunction f) (o.openAdjunction g) (o.openAdjunction h)
    (o.openAdjunction (f ≫ g)) (o.openAdjunction (g ≫ h)) (o.openAdjunction (f ≫ g ≫ h))
    (pComp o f g).symm (pComp o g h).symm
    (pComp o f (g ≫ h)).symm
    ((pComp o (f ≫ g) h).symm ≪≫
      eqToIso (congrArg (o.P) (Category.assoc f g h))) hi
  simp only [pComp, Iso.symm_symm_eq] at hh
  rw [j_comp_transport o (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)] at hh
  have hm := congr_app (congrArg Iso.hom hh) M
  apply (cancel_mono ((o.jCongr (Category.assoc f g h)).hom.app M)).1
  simpa only [Operations.e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hm.symm

private theorem j_unital (o : Operations.{u}) (hp : PullCoherence o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : o.D X) :
    ((o.e (𝟙 X) j).hom.app M ≫ (o.jCongr (Category.id_comp j)).hom.app M =
      (o.J j).map ((o.jId X).hom.app M)) ∧
    ((o.e j (𝟙 Y)).hom.app M ≫ (o.jCongr (Category.comp_id j)).hom.app M =
      (o.jId Y).hom.app ((o.J j).obj M)) := by
  constructor
  · have he : o.d (𝟙 X) j ≪≫ eqToIso (congrArg o.P (Category.id_comp j)) =
        Functor.isoWhiskerLeft (o.P j) (o.pId X) ≪≫ Functor.rightUnitor (o.P j) := by
      apply Iso.ext
      have hh := congrArg Iso.hom (hp.left_unit j)
      simp only [Iso.trans_hom, Iso.refl_hom] at hh
      have hh' : (eqToIso (congrArg o.P (Category.id_comp j).symm) ≪≫
          pComp o (𝟙 X) j).hom ≫
          (Functor.isoWhiskerLeft (o.P j) (o.pId X) ≪≫
            Functor.rightUnitor (o.P j)).hom = 𝟙 _ := by
        simpa only [Iso.trans_hom, Category.assoc] using hh
      simpa only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        eqToIso.inv, eqToIso.hom] using
        ((Iso.hom_comp_eq_id _).1 hh').symm
    have hh := Adjunction.leftAdjointCompIso_id_comp
      (o.openAdjunction (𝟙 X)) (o.openAdjunction j)
      (o.d (𝟙 X) j ≪≫ eqToIso (congrArg o.P (Category.id_comp j))) (o.pId X) he
    rw [j_comp_transport o (𝟙 X) j j (Category.id_comp j)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, Operations.jId] using hm
  · have he : o.d j (𝟙 Y) ≪≫ eqToIso (congrArg o.P (Category.comp_id j)) =
        Functor.isoWhiskerRight (o.pId Y) (o.P j) ≪≫ Functor.leftUnitor (o.P j) := by
      apply Iso.ext
      have hh := congrArg Iso.hom (hp.right_unit j)
      simp only [Iso.trans_hom, Iso.refl_hom] at hh
      have hh' : (eqToIso (congrArg o.P (Category.comp_id j).symm) ≪≫
          pComp o j (𝟙 Y)).hom ≫
          (Functor.isoWhiskerRight (o.pId Y) (o.P j) ≪≫
            Functor.leftUnitor (o.P j)).hom = 𝟙 _ := by
        simpa only [Iso.trans_hom, Category.assoc] using hh
      simpa only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        eqToIso.inv, eqToIso.hom] using
        ((Iso.hom_comp_eq_id _).1 hh').symm
    have hh := Adjunction.leftAdjointCompIso_comp_id
      (o.openAdjunction j) (o.openAdjunction (𝟙 Y))
      (o.d j (𝟙 Y) ≪≫ eqToIso (congrArg o.P (Category.comp_id j))) (o.pId Y) he
    rw [j_comp_transport o j (𝟙 Y) j (Category.comp_id j)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, Operations.jId] using hm

private theorem laws_of_pull_coherence (F : FiniteFieldDatum.{u})
    (o : Operations.{u}) (hp : PullCoherence o) : Laws F o where
  direct _ _ _ f g := direct_normalized o f g
  openExtension _ _ _ j b := open_normalized o j b
  kinjective _ _ _ f g I := by
    intro hI
    let := (o.adj f).preservesKInjectiveComplexes
    let := (o.adj g).preservesKInjectiveComplexes
    exact ⟨inferInstance, inferInstance, c_fac o f g _⟩
  localizedOpen _ _ _ j b := open_localized o j b
  s_assoc _ _ _ _ f g h M := s_associative o hp f g h M
  s_unit _ _ f M := s_unital o hp f M
  j_assoc _ _ _ _ j b a _ _ _ M := j_associative o hp j b a M
  j_unit _ _ j _ M := j_unital o hp j M
  threefold _ _ _ _ f g h M N k := threefold_direct o f g h M N k
  threefoldRight _ _ _ _ f g h M N k := threefold_direct_right o f g h M N k
  threefoldOpen _ _ _ _ j b a _ _ _ M N k := threefold_open o j b a M N k
  threefoldOpenRight _ _ _ _ j b a _ _ _ M N k := threefold_open_right o j b a M N k

private theorem system_sections (F : FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    SystemSections F C τ := by
  intro X Y Z _ _ _ f g
  unfold Operations.ordinaryC systems ProEtale.SemilinearProperOpen.pullComp
  exact Equiv.apply_symm_apply _ _

section SystemUnits
open ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)

private abbrev systemPushId (X : Scheme.{u}) := (pushId_existsUnique C τ X).choose

private theorem system_push_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushComp C τ (𝟙 X) f ≪≫ eqToIso (congrArg (push C τ) (Category.id_comp f)) =
      Functor.isoWhiskerRight (systemPushId C τ X) (push C τ f) ≪≫
        Functor.leftUnitor (push C τ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [push_map_apply C τ f ((systemPushId C τ X).hom.app M) n U]
  erw [(pushId_existsUnique C τ X).choose_spec.1 M n ((proEtaleBaseChange f).obj U)]
  erw [push_transport C τ (Category.id_comp f) M n U]
  erw [pushComp_apply C τ (𝟙 X) f M n U]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  apply ProEtale.StrictTower.restriction_eq M.val
  apply Prod.hom_ext
  · simp
  · exact ProEtale.StrictTower.site_left_unit (P := @WeaklyEtale) (Q := ⊤) f U

private theorem system_push_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushComp C τ f (𝟙 Y) ≪≫ eqToIso (congrArg (push C τ) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (push C τ f) (systemPushId C τ Y) ≪≫
        Functor.rightUnitor (push C τ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [(pushId_existsUnique C τ Y).choose_spec.1 ((push C τ f).obj M) n U]
  erw [push_transport C τ (Category.comp_id f) M n U]
  erw [pushComp_apply C τ f (𝟙 Y) M n U]
  erw [push_obj_map_apply C τ f M n
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).inv.app U)]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  apply ProEtale.StrictTower.restriction_eq M.val
  apply Prod.hom_ext
  · simp
  · exact ProEtale.StrictTower.site_right_unit (P := @WeaklyEtale) (Q := ⊤) f U

private theorem system_ordinary_pull_coherence : OrdinaryPullCoherence (systems C τ) where
  assoc f g h := pull_coherence C τ f g h
  left_unit {X Y} f := by
    change eqToIso (congrArg (pull C τ) (Category.id_comp f).symm) ≪≫
      pullComp C τ (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (pull C τ f)
        (Adjunction.leftAdjointIdIso (ordinaryAdj C τ (𝟙 X)) (systemPushId C τ X)) ≪≫
      Functor.rightUnitor _ = Iso.refl _
    have h := Adjunction.leftAdjointCompIso_comp_id (ordinaryAdj C τ f)
      (ordinaryAdj C τ (𝟙 X))
      (pushComp C τ (𝟙 X) f ≪≫ eqToIso (congrArg (push C τ) (Category.id_comp f)))
      (systemPushId C τ X) (system_push_left_unit C τ f)
    rw [ProEtale.StrictTower.mate_transport (pull C τ) (push C τ)
      (fun t ↦ ordinaryAdj C τ t) (ordinaryAdj C τ f) (ordinaryAdj C τ (𝟙 X))
      (Category.id_comp f) (pushComp C τ (𝟙 X) f)] at h
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hi := congr_app (congrArg Iso.inv h) M
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Functor.rightUnitor_inv_app] at hi
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Iso.refl_hom, NatTrans.id_app]
    rw [← Category.assoc]
    change (_ ≫ (pullComp C τ (𝟙 X) f).hom.app M) ≫ _ = _
    change _ ≫ (pullComp C τ (𝟙 X) f).hom.app M = _ at hi
    simp only [eqToIso.inv, eqToIso.hom] at hi ⊢
    rw [hi]
    erw [Category.comp_id, Category.id_comp, Iso.inv_hom_id_app]
    rfl
  right_unit {X Y} f := by
    change eqToIso (congrArg (pull C τ) (Category.comp_id f).symm) ≪≫
      pullComp C τ f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight
        (Adjunction.leftAdjointIdIso (ordinaryAdj C τ (𝟙 Y)) (systemPushId C τ Y))
        (pull C τ f) ≪≫ Functor.leftUnitor _ = Iso.refl _
    have h := Adjunction.leftAdjointCompIso_id_comp (ordinaryAdj C τ (𝟙 Y))
      (ordinaryAdj C τ f)
      (pushComp C τ f (𝟙 Y) ≪≫ eqToIso (congrArg (push C τ) (Category.comp_id f)))
      (systemPushId C τ Y) (system_push_right_unit C τ f)
    rw [ProEtale.StrictTower.mate_transport (pull C τ) (push C τ)
      (fun t ↦ ordinaryAdj C τ t) (ordinaryAdj C τ (𝟙 Y)) (ordinaryAdj C τ f)
      (Category.comp_id f) (pushComp C τ f (𝟙 Y))] at h
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hi := congr_app (congrArg Iso.inv h) M
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, Functor.leftUnitor_inv_app] at hi
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Iso.refl_hom, NatTrans.id_app]
    rw [← Category.assoc]
    change (_ ≫ (pullComp C τ f (𝟙 Y)).hom.app M) ≫ _ = _
    change _ ≫ (pullComp C τ f (𝟙 Y)).hom.app M = _ at hi
    simp only [eqToIso.inv, eqToIso.hom] at hi ⊢
    rw [hi]
    erw [Category.comp_id, Category.id_comp, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    exact (pull C τ f).map_id M

end SystemUnits

section TransportCoherence
attribute [-instance] CategoryTheory.catToReflQuiver
variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]

private abbrev trComparison (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {FG : C₀ ⥤ C₂} (a : FG ≅ F ⋙ G) :=
  trIso e₀ e₂ a ≪≫ trComp e₀ e₁ e₂ F G

private theorem transport_assoc (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁)
    (e₂ : C₂ ≌ D₂) (e₃ : C₃ ≌ D₃)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (FG : C₀ ⥤ C₂) (GH : C₁ ⥤ C₃) (FGH FGH' : C₀ ⥤ C₃)
    (a02 : FG ≅ F ⋙ G) (a13 : GH ≅ G ⋙ H)
    (a0 : FGH ≅ FG ⋙ H) (a1 : FGH' ≅ F ⋙ GH) (e : FGH ≅ FGH')
    (ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13) :
    trComparison e₀ e₂ e₃ a0 ≪≫
      Functor.isoWhiskerRight (trComparison e₀ e₁ e₂ a02) (trFunctor e₂ e₃ H) =
    trIso e₀ e₃ e ≪≫ trComparison e₀ e₁ e₃ a1 ≪≫
      Functor.isoWhiskerLeft (trFunctor e₀ e₁ F) (trComparison e₁ e₂ e₃ a13) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let x := e₀.inverse.obj M
  let t := a02.hom.app x ≫ G.map (e₁.unitIso.hom.app (F.obj x))
  have ho' := congr_app (congrArg Iso.hom ho) x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ho'
  have hn := e₂.unitIso.hom.naturality t
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  have ha := a13.hom.naturality (e₁.unitIso.hom.app (F.obj x))
  dsimp only [Functor.comp_map] at ha
  have hx : a0.hom.app x ≫ H.map (e₂.unitIso.hom.app (FG.obj x)) ≫
        H.map (e₂.inverse.map (e₂.functor.map t)) =
      e.hom.app x ≫ a1.hom.app x ≫ GH.map (e₁.unitIso.hom.app (F.obj x)) ≫
        a13.hom.app (e₁.inverse.obj (e₁.functor.obj (F.obj x))) ≫
          H.map (e₂.unitIso.hom.app
            (G.obj (e₁.inverse.obj (e₁.functor.obj (F.obj x))))) := by
    rw [← H.map_comp, ← hn, H.map_comp]
    dsimp only [t]
    rw [H.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (a0.hom.app x), ho']
    simp only [Category.assoc]
    rw [← reassoc_of% ha]
    rfl
  simpa only [trComparison, trIso, trComp, trFunctor,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Equivalence.funInvIdAssoc_inv_app, NatTrans.comp_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc, x, t] using
    congrArg e₃.functor.map hx

private theorem transport_left_unit (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁)
    (F H : C₀ ⥤ C₁) (I : C₁ ⥤ C₁)
    (q : F ≅ H) (k : H ≅ F ⋙ I) (e : I ≅ 𝟭 C₁)
    (ho : q ≪≫ k ≪≫ Functor.isoWhiskerLeft F e ≪≫
      Functor.rightUnitor F = Iso.refl F) :
    trIso e₀ e₁ q ≪≫ trComparison e₀ e₁ e₁ k ≪≫
      Functor.isoWhiskerLeft (trFunctor e₀ e₁ F) (trId e₁ e) ≪≫
        Functor.rightUnitor _ = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hh := congr_app (congrArg Iso.hom ho) (e₀.inverse.obj M)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app] at hh
  have hn := e.hom.naturality (e₁.unitIso.hom.app (F.obj (e₀.inverse.obj M)))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [trComparison, trIso, trComp, trFunctor, trId, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Equivalence.funInvIdAssoc_inv_app, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Iso.refl_hom, NatTrans.id_app, Category.assoc]
  have hm := congrArg e₁.functor.map hn
  simp only [Functor.map_comp] at hm
  erw [reassoc_of% hm]
  have hh' : q.hom.app (e₀.inverse.obj M) ≫ k.hom.app (e₀.inverse.obj M) ≫
      e.hom.app (F.obj (e₀.inverse.obj M)) = 𝟙 _ := by
    dsimp only [Functor.comp_obj, Functor.id_obj] at hh
    simpa only [Category.assoc, Category.comp_id] using hh
  have hv := congrArg e₁.functor.map hh'
  simp only [Functor.map_comp] at hv
  erw [e₁.functor.map_id] at hv
  rw [reassoc_of% hv]
  erw [Category.comp_id]
  exact e₁.functor_unit_comp (F.obj (e₀.inverse.obj M))

private theorem transport_right_unit (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁)
    (F H : C₀ ⥤ C₁) (I : C₀ ⥤ C₀)
    (q : F ≅ H) (k : H ≅ I ⋙ F) (e : I ≅ 𝟭 C₀)
    (ho : q ≪≫ k ≪≫ Functor.isoWhiskerRight e F ≪≫
      Functor.leftUnitor F = Iso.refl F) :
    trIso e₀ e₁ q ≪≫ trComparison e₀ e₀ e₁ k ≪≫
      Functor.isoWhiskerRight (trId e₀ e) (trFunctor e₀ e₁ F) ≪≫
        Functor.leftUnitor _ = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hh := congr_app (congrArg Iso.hom ho) (e₀.inverse.obj M)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app] at hh
  have hn := e₀.unitIso.hom.naturality (e.hom.app (e₀.inverse.obj M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [trComparison, trIso, trComp, trFunctor, trId, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Equivalence.funInvIdAssoc_inv_app, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Iso.refl_hom, NatTrans.id_app,
    Functor.map_comp, Category.assoc]
  have hu : e₀.unitIso.hom.app (I.obj (e₀.inverse.obj M)) ≫
      e₀.inverse.map (e₀.functor.map (e.hom.app (e₀.inverse.obj M))) ≫
      e₀.inverse.map (e₀.counitIso.hom.app M) = e.hom.app (e₀.inverse.obj M) := by
    rw [← Category.assoc, ← hn]
    simp only [Functor.id_obj, Category.assoc, e₀.unit_inverse_comp, Category.comp_id]
  have hf := congrArg (fun t ↦ q.hom.app (e₀.inverse.obj M) ≫
    k.hom.app (e₀.inverse.obj M) ≫ F.map t) hu
  have hh' : q.hom.app (e₀.inverse.obj M) ≫ k.hom.app (e₀.inverse.obj M) ≫
      F.map (e.hom.app (e₀.inverse.obj M)) = 𝟙 _ := by
    dsimp only [Functor.comp_obj, Functor.id_obj] at hh
    simpa only [Category.assoc, Category.comp_id] using hh
  have hr := (congrArg e₁.functor.map (hf.trans hh'))
  erw [e₁.functor.map_id] at hr
  dsimp only [Functor.comp_obj, Functor.id_obj] at hr ⊢
  simpa only [Functor.map_comp, Functor.map_id, Category.assoc,
    Category.comp_id, Equivalence.unit] using hr



private def untransportRight (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀} (b : trFunctor f e R ≅ R') :
    R' ⋙ e.inverse ≅ f.inverse ⋙ R :=
  Functor.isoWhiskerRight b.symm e.inverse ≪≫
    Functor.isoWhiskerLeft (f.inverse ⋙ R) e.unitIso.symm

private theorem tr_hom_formula (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R)
    {M : D₀} {N : D₁} (h : (trFunctor e f L).obj M ⟶ N) :
    (trAdj e f a).homEquiv M N h =
      e.counitIso.inv.app M ≫ e.functor.map
        (a.homEquiv _ _ (f.unitIso.hom.app _ ≫ f.inverse.map h)) := by
  rw [trAdj, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

private theorem tr_hom_normalization (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R)
    {R' : D₁ ⥤ D₀} (b : trFunctor f e R ≅ R')
    {M : D₀} {N : D₁} (h : (trFunctor e f L).obj M ⟶ N) :
    e.inverse.map (((trAdj e f a).ofNatIsoRight b).homEquiv M N h) ≫
        (untransportRight e f b).hom.app N =
      a.homEquiv _ _ (f.unitIso.hom.app _ ≫ f.inverse.map h) := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, tr_hom_formula]
  simp only [untransportRight, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← e.inverse.map_comp_assoc (b.hom.app N), b.hom_inv_id_app,
    e.inverse.map_id, Category.id_comp]
  rw [e.inv_fun_map]
  simp only [Category.assoc]
  rw [← e.unit_app_inverse]
  dsimp only [Functor.comp_obj, Equivalence.unit, Equivalence.unitInv]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem tr_comp_hom (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {Lg : C₀ ⥤ C₁} {Rg : C₁ ⥤ C₀} {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁}
    (ag : Lg ⊣ Rg) (af : Lf ⊣ Rf)
    {Rg' : D₁ ⥤ D₀} {Rf' : D₂ ⥤ D₁}
    (bg : trFunctor e₁ e₀ Rg ≅ Rg') (bf : trFunctor e₂ e₁ Rf ≅ Rf')
    {M : D₀} {N : D₂}
    (h : ((trFunctor e₀ e₁ Lg) ⋙ trFunctor e₁ e₂ Lf).obj M ⟶ N) :
    e₀.inverse.map ((((trAdj e₀ e₁ ag).ofNatIsoRight bg).comp
        ((trAdj e₁ e₂ af).ofNatIsoRight bf)).homEquiv M N h) ≫
        (untransportRight e₀ e₁ bg).hom.app (Rf'.obj N) ≫
        Rg.map ((untransportRight e₁ e₂ bf).hom.app N) =
      (ag.comp af).homEquiv _ _
        (Lf.map (e₁.unitIso.hom.app (Lg.obj (e₀.inverse.obj M))) ≫
          e₂.unitIso.hom.app _ ≫ e₂.inverse.map h) := by
  rw [Adjunction.comp_homEquiv]
  change e₀.inverse.map (((trAdj e₀ e₁ ag).ofNatIsoRight bg).homEquiv _ _
      (((trAdj e₁ e₂ af).ofNatIsoRight bf).homEquiv _ _ h)) ≫ _ ≫ _ = _
  rw [← Category.assoc, tr_hom_normalization]
  rw [← ag.homEquiv_naturality_right]
  rw [Category.assoc, tr_hom_normalization e₁ e₂ af bf h]
  dsimp only [trFunctor, Functor.comp_obj] at h ⊢
  rw [← af.homEquiv_naturality_left]
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem conjugate_hom
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (k : L' ⟶ L) {M : C} {N : D} (h : L.obj M ⟶ N) :
    a'.homEquiv M N (k.app M ≫ h) =
      a.homEquiv M N h ≫ (conjugateEquiv a a' k).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [(conjugateEquiv a a' k).naturality]
  simp only [← Category.assoc]
  rw [unit_conjugateEquiv]

private theorem tr_comp_mate (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {Lg : C₀ ⥤ C₁} {Rg : C₁ ⥤ C₀} {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁}
    {Lc : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀}
    (ag : Lg ⊣ Rg) (af : Lf ⊣ Rf) (ac : Lc ⊣ Rc)
    {Rg' : D₁ ⥤ D₀} {Rf' : D₂ ⥤ D₁} {Rc' : D₂ ⥤ D₀}
    (bg : trFunctor e₁ e₀ Rg ≅ Rg') (bf : trFunctor e₂ e₁ Rf ≅ Rf')
    (bc : trFunctor e₂ e₀ Rc ≅ Rc') (k : Lc ≅ Lg ⋙ Lf) (N : D₂) :
    e₀.inverse.map ((conjugateEquiv
      (((trAdj e₀ e₁ ag).ofNatIsoRight bg).comp
        ((trAdj e₁ e₂ af).ofNatIsoRight bf))
      ((trAdj e₀ e₂ ac).ofNatIsoRight bc)
      (trComparison e₀ e₁ e₂ k).hom).app N) ≫
        (untransportRight e₀ e₂ bc).hom.app N =
      (untransportRight e₀ e₁ bg).hom.app (Rf'.obj N) ≫
        Rg.map ((untransportRight e₁ e₂ bf).hom.app N) ≫
        (conjugateEquiv (ag.comp af) ac k.hom).app (e₂.inverse.obj N) := by
  let as_ := ((trAdj e₀ e₁ ag).ofNatIsoRight bg).comp
    ((trAdj e₁ e₂ af).ofNatIsoRight bf)
  let M := (Rf' ⋙ Rg').obj N
  let h : e₂.functor.obj (Lf.obj (e₁.inverse.obj
      (e₁.functor.obj (Lg.obj (e₀.inverse.obj M))))) ⟶ N := as_.counit.app N
  let t := Lf.map (e₁.unitIso.hom.app (Lg.obj (e₀.inverse.obj M))) ≫
    e₂.unitIso.hom.app _ ≫ e₂.inverse.map h
  have ht := tr_comp_hom e₀ e₁ e₂ ag af bg bf h
  have hh : as_.homEquiv M N h = 𝟙 _ := by
    dsimp only [h]
    rw [← as_.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  change e₀.inverse.map (as_.homEquiv M N h) ≫ _ ≫ _ =
    (ag.comp af).homEquiv _ _ t at ht
  rw [hh, e₀.inverse.map_id, Category.id_comp] at ht
  have hs := tr_hom_normalization e₀ e₂ ac bc
    ((trComparison e₀ e₁ e₂ k).hom.app M ≫ h)
  rw [conjugate_hom as_ ((trAdj e₀ e₂ ac).ofNatIsoRight bc)
    (trComparison e₀ e₁ e₂ k).hom] at hs
  rw [hh, Category.id_comp] at hs
  have hk : e₂.unitIso.hom.app _ ≫
      e₂.inverse.map ((trComparison e₀ e₁ e₂ k).hom.app M ≫ h) =
        k.hom.app (e₀.inverse.obj M) ≫ t := by
    simp only [trComparison, trIso, trComp, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Equivalence.funInvIdAssoc_inv_app, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    dsimp only [Functor.comp_obj, trFunctor, t]
    simp only [Equivalence.unit]
    erw [e₂.unit_naturality_assoc, e₂.unit_naturality_assoc]
  change _ = (ag.comp af).homEquiv _ (e₂.inverse.obj N) t at ht
  rw [hk, conjugate_hom (ag.comp af) ac k.hom, ← ht] at hs
  simpa only [Category.assoc] using hs

end TransportCoherence

private theorem finite_pull_transport (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    trIso (sfIntrinsicModuleEquivalence Y A) (sfIntrinsicModuleEquivalence X A)
      (eqToIso (congrArg (ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) h)) =
      eqToIso (congrArg (sfIntrinsicPullback A) h) := by
  cases h
  exact trIso_refl _ _ _

private theorem finite_ordinary_pull_coherence (A : Type u) [CommRing A] [Finite A] :
    OrdinaryPullCoherence (finite A) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  constructor
  · intro X Y Z T f g h
    have ho := ProEtale.upperStarComp_assoc B f g h
    have hh := transport_assoc (sfIntrinsicModuleEquivalence T A)
      (sfIntrinsicModuleEquivalence Z A) (sfIntrinsicModuleEquivalence Y A)
      (sfIntrinsicModuleEquivalence X A)
      (ProEtale.upperStar B h) (ProEtale.upperStar B g) (ProEtale.upperStar B f)
      (ProEtale.upperStar B (g ≫ h)) (ProEtale.upperStar B (f ≫ g))
      (ProEtale.upperStar B (f ≫ g ≫ h)) (ProEtale.upperStar B ((f ≫ g) ≫ h))
      (ProEtale.upperStarComp B g h) (ProEtale.upperStarComp B f g)
      (ProEtale.upperStarComp B f (g ≫ h)) (ProEtale.upperStarComp B (f ≫ g) h)
      (eqToIso (congrArg (ProEtale.upperStar B) (Category.assoc f g h).symm))
      (by
        apply Iso.ext
        apply NatTrans.ext
        funext M
        simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
          Category.comp_id, ProEtale.upperStarCongr] using
          congr_app (congrArg Iso.hom ho) M)
    rw [finite_pull_transport A (Category.assoc f g h).symm] at hh
    exact hh
  · intro X Y f
    have hh := transport_left_unit (sfIntrinsicModuleEquivalence Y A)
      (sfIntrinsicModuleEquivalence X A) (ProEtale.upperStar B f)
      (ProEtale.upperStar B (𝟙 X ≫ f)) (ProEtale.upperStar B (𝟙 X))
      (eqToIso (congrArg (ProEtale.upperStar B) (Category.id_comp f).symm))
      (ProEtale.upperStarComp B (𝟙 X) f) (ProEtale.upperStarId B X)
      (by
        rw [ProEtale.upperStarComp_id_left]
        simp only [ProEtale.upperStarCongr, Iso.trans_assoc,
          ← Functor.isoWhiskerLeft_symm]
        simp)
    rw [finite_pull_transport A (Category.id_comp f).symm] at hh
    exact hh
  · intro X Y f
    have hh := transport_right_unit (sfIntrinsicModuleEquivalence Y A)
      (sfIntrinsicModuleEquivalence X A) (ProEtale.upperStar B f)
      (ProEtale.upperStar B (f ≫ 𝟙 Y)) (ProEtale.upperStar B (𝟙 Y))
      (eqToIso (congrArg (ProEtale.upperStar B) (Category.comp_id f).symm))
      (ProEtale.upperStarComp B f (𝟙 Y)) (ProEtale.upperStarId B Y)
      (by
        rw [ProEtale.upperStarComp_id_right]
        simp only [ProEtale.upperStarCongr, Iso.trans_assoc,
          ← Functor.isoWhiskerRight_symm]
        simp)
    rw [finite_pull_transport A (Category.comp_id f).symm] at hh
    exact hh

private abbrev finiteRightComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (sfIntrinsicDirectImageComparison f A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso _ ≪≫
    Functor.leftUnitor _

private theorem finite_untransport (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    untransportRight (sfIntrinsicModuleEquivalence Y A)
      (sfIntrinsicModuleEquivalence X A) (finiteRightComparison A f) =
        sectionDirectImageIso A f := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [untransportRight, finiteRightComparison, sectionDirectImageIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.map_comp, NatTrans.comp_app,
    Category.id_comp, Category.assoc]
  rfl

private theorem finite_comp_mate (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : (finite A).M X) :
    (sfIntrinsicModuleEquivalence Z A).inverse.map
        (((finite A).ordinaryC f g).hom.app M) ≫
      (sectionDirectImageIso A (f ≫ g)).hom.app M =
    (sectionDirectImageIso A g).hom.app
        ((proEtaleConstantModuleDirectImage f A).obj M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).map
        ((sectionDirectImageIso A f).hom.app M) ≫
      (ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app
        ((sfIntrinsicModuleEquivalence X A).inverse.obj M) := by
  have h := tr_comp_mate (sfIntrinsicModuleEquivalence Z A)
    (sfIntrinsicModuleEquivalence Y A) (sfIntrinsicModuleEquivalence X A)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
    (finiteRightComparison A g) (finiteRightComparison A f)
    (finiteRightComparison A (f ≫ g))
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) M
  rw [ProEtale.conjugateEquiv_upperStarComp_hom] at h
  simp only [finite_untransport] at h
  convert h using 1
  congr 2

private theorem finite_sections (F : FiniteFieldDatum.{u})
    (A : Type u) [CommRing A] [Finite A] : FiniteSections F A := by
  intro X Y Z _ _ _ f g M V x
  change proEtaleRingModules X (proEtaleConstantRing X A) at M
  obtain ⟨y, hy⟩ := (sectionRealization_bijective A Z
    ((proEtaleConstantModuleDirectImage g A).obj
      ((proEtaleConstantModuleDirectImage f A).obj M)) (op V)).surjective x
  have hm := finite_comp_mate A f g M
  have hv := congrArg (fun t ↦ sectionRealization A X M
    (op ((proEtaleBaseChange (f ≫ g)).obj V)) ((t.hom.app (op V)) y)) hm
  change sectionRealization A X M (op ((proEtaleBaseChange (f ≫ g)).obj V))
      (((sectionDirectImageIso A (f ≫ g)).hom.app M).hom.app (op V)
        (((sfIntrinsicModuleEquivalence Z A).inverse.map
          (((finite A).ordinaryC f g).hom.app M)).hom.app (op V) y)) =
    sectionRealization A X M (op ((proEtaleBaseChange (f ≫ g)).obj V))
      (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map
        ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
        (((sectionDirectImageIso A f).hom.app M).hom.app
          (op ((proEtaleBaseChange g).obj V))
          (((sectionDirectImageIso A g).hom.app
            ((proEtaleConstantModuleDirectImage f A).obj M)).hom.app (op V) y))) at hv
  erw [sectionDirectImageIso_normalization, sectionRealization_naturality,
    sectionRealization_restrict, sectionDirectImageIso_normalization,
    sectionDirectImageIso_normalization, hy] at hv
  exact hv

/-- The specified ambient compositors are canonical, resolution normalized, natural,
associative and unital, on each positive level and on the ringed diagram category itself.
Source: Stacks 0D6E, 09T5, 08BJ, 070I, 015F, 03D3 and 0DV0
(blueprint: lem-sf-ambient-adjunction-compositor-normalization).

Proof:
1. For arbitrary Operations, the conjugate adjunction formula gives the unit, counit
   and Hom equations. Composite Hom equivalences give the four threefold formulas.
2. The source-library right-derived composition/conjugation theorem identifies c with
   the universal right-derived compositor. Its unit equation gives the stated
   K-injective normalization, since right adjoints to exact pullbacks preserve K-injectives.
3. Exact localization carries the ordinary open-extension unit equation to the derived
   one. Normalized-adjunction uniqueness and the exact composition factor equations
   identify e with localization of ordinaryE.
4. Descend ordinary pullback coherence through exact localization. Mate associativity
   and identity formulas transfer it to c and e, with all equality transports retained.
5. System pullback associativity is already proved. Its identity laws are the mates of
   the sectionwise push identity laws on the full diagram site. The definition of its
   pullback compositor also gives ordinaryC = pushComp by conjugation's inverse law.
6. Transport the proved fixed-scalar pullback coherence across the intrinsic realization
   equivalences, using naturality and their unit and counit triangle equations.
7. Normalize each transported adjunction Hom equivalence, then its composite. Applying
   this identity to the composite counit identifies ordinaryC with fixed-scalar
   lowerStarComp. Bijectivity and naturality of section realization and the normalized
   direct-image comparison give its asserted native section formula. -/
theorem ambientAdjunctionCompositorNormalization
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∀ n : ℕ, letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
      Laws F (finite (Padic.coefficientExtensionRing l E (n + 1))) ∧
      FiniteSections F (Padic.coefficientExtensionRing l E (n + 1))) ∧
    (Laws F (systems (coefficientTower l E) (coefficientTransition l E)) ∧
      SystemSections F (coefficientTower l E) (coefficientTransition l E)) := by
  constructor
  · intro n
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    refine ⟨laws_of_pull_coherence F _
      (descend_pull_coherence _ (finite_ordinary_pull_coherence _)), ?_⟩
    exact finite_sections F _
  · exact ⟨laws_of_pull_coherence F _ (descend_pull_coherence _
      (system_ordinary_pull_coherence _ _)), system_sections F _ _⟩

end WeilConjectures.AmbientCompositor
