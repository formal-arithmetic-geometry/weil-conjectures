/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.GeometricModuleTransport
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-! # Normalized derived monoidal comparisons on ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D, 07A6, 0D6E, 0FPI;
Modules on Sites, Tags 03D7, 03D8, 03EL
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).

The structures below only package the simultaneous witnesses of the statement. In
particular an ordinary pullback is tied to the geometric morphism by scalar extension
and its underlying Hom bijection. Derived adjunctions are fixed on K-flat/K-injective
representatives. The comparisons are fixed on representatives, including for a specified
geometric 2-isomorphism; none is an unconstrained isomorphism of functors.
-/

public noncomputable section

set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules

namespace CategoryTheory.RingedDerivedComparisons

set_option linter.checkUnivs false in
/-- A presentation of the ordinary derived category with its recorded signed tensor model.
Source: Stacks 0FPT, 06YN (blueprint: lem-sfb-ringed-derived-monoidal-comparisons).
These are the witnesses of `ringedDerived_closed_symmetric_monoidal`, not new tensor data. -/
structure Site where
  C : Type u
  [category : SmallCategory C]
  J : GrothendieckTopology C
  A : Sheaf J CommRingCat.{u}
  [derived : HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A))]
  closed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, w} J A)
  model : CoefficientTensorModels.{u, u, u, w} J A closed
  symmetry : @SymmetricCategory _ _ closed.monoidal
  coherence : RingedDerivedTensorCoherence.{u, u, u, w} J A closed model symmetry


attribute [instance] Site.category Site.derived

/-- The recorded ring sheaf, with commutativity forgotten.
Source: Stacks 03D7 (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Site.ring (X : Site.{u, w}) :=
  (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.A

/-- The existing module category of a corner.
Source: Stacks 03D7 (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Site.modules (X : Site.{u, w}) := ringedSiteModules.{u, u, u, u} X.ring

/-- The ordinary unbounded derived category of that module category.
Source: Stacks 05RR (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Site.D (X : Site.{u, w}) := DerivedCategory.{w} X.modules

/-- The underlying sheaf functor used to specify ordinary scalar-extension insertion.
Source: Stacks 03D7 (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Site.sets (X : Site.{u, w}) :=
  toSheaf X.ring ⋙ sheafCompose X.J (CategoryTheory.forget AddCommGrpCat.{u})

/-- The tensor corner of the existing projection-mate interface, with this very tensor.
Source: Stacks 07A4 (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
@[expose]
def Site.corner (X : Site.{u, w}) : RingedTensorCorner.{u, w} where
  site := X.C
  topology := X.J
  ring := X.A
  tensor := X.closed.tensor

/-- Morphisms are exactly the DAG's geometric ringed-topos morphisms.
Source: Stacks 03D7 (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Morphism (X Y : Site.{u, w}) := RingedToposMorphism X.ring Y.ring

/-- All normalization data for one of the statement's pullback/direct-image pairs.
Source: Stacks 07A4, 07A6, 0FPI, 03D7
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).
The `CoreMonoidal` maps are inverse to the displayed tensor/unit comparisons. -/
structure Lift {X Y : Site.{u, w}} (f : Morphism X Y) where
  edge : RingedTensorEdge Y.corner X.corner
  inverse_eq : edge.inverse = f.inverse
  direct_eq : edge.direct = f.direct
  geometric_adjunction : HEq edge.adjunction f.adj
  pushforward_eq : edge.pushforward = f.modules
  structural_map :
    edge.algebraic.ringUnderlying.hom ≫
        (sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).map edge.ringMap =
      eqToHom (congrArg (fun F ↦ F.obj
        ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A)) inverse_eq) ≫
          f.ringMap
  ordinary_adjunction : ∀ (M : Y.modules) (N : X.modules) (v : edge.pullback.obj M ⟶ N),
    Y.sets.map (edge.moduleAdjunction.homEquiv M N v) ≫
      (Functor.whiskerRight (eqToHom pushforward_eq) Y.sets).app N ≫
        f.underlying.hom.app N =
      f.adj.homEquiv (Y.sets.obj M) (X.sets.obj N)
        (eqToHom (congrArg (fun F ↦ F.obj (Y.sets.obj M)) inverse_eq.symm) ≫
          edge.insertion M ≫ X.sets.map v)
  [right_additive : edge.pushforward.Additive]
  eta : edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} (C := Y.modules) ⟶
    DerivedCategory.Q.{w} (C := X.modules) ⋙ edge.right
  isRightDerived : edge.right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso X.modules (ComplexShape.up ℤ))
  eta_injective : ∀ I : CochainComplex X.modules ℤ, I.IsKInjective → IsIso (eta.app I)
  epsilon_flat : ∀ P : CochainComplex Y.modules ℤ,
    Y.corner.mateFlat P → IsIso (derivedPullbackComplexComparison
      edge.pullback edge.left edge.epsilon P)
  canonical_adjunction : ∀ (P : CochainComplex Y.modules ℤ)
    (I : CochainComplex X.modules ℤ), Y.corner.mateFlat P → I.IsKInjective →
    ∀ b : P ⟶ (edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I,
      (edge.derivedAdjunction.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj I)).symm (DerivedCategory.Q.map b ≫ eta.app I) =
      derivedPullbackComplexComparison edge.pullback edge.left edge.epsilon P ≫
        DerivedCategory.Q.map
          (((edge.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P I).symm b)
  tensorModelY : RingedTensorModel Y.corner
  tensorModelX : RingedTensorModel X.corner
  tensorModelY_eq : ∀ P Q hP hQ,
    tensorModelY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom
  tensorModelX_eq : ∀ P Q hP hQ,
    tensorModelX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom
  monoidal : @Functor.CoreMonoidal Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal edge.left
  tensor_canonical : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      edge.left monoidal U V).inv =
      (edge.tensorComparison tensorModelY tensorModelX).hom.app (U, V)
  unit_canonical : ∃ j : edge.pullback.obj (SheafOfModules.unit Y.ring) ≅
      SheafOfModules.unit X.ring,
    (∀ M : Y.modules,
      (edge.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (edge.pullback.obj M)).hom =
        edge.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) ∧
    edge.left.map Y.coherence.unitIso.hom ≫
        derivedPullbackComplexComparison edge.pullback edge.left edge.epsilon
          (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            edge.pullback (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit Y.ring) ≫
            (CochainComplex.singleFunctor X.modules 0).map j.hom) ≫
        X.coherence.unitIso.inv =
        (@Functor.CoreMonoidal.εIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          edge.left monoidal).inv
  symmetric : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      edge.left monoidal U V).inv ≫
        (X.symmetry.toBraidedCategory.braiding (edge.left.obj U) (edge.left.obj V)).hom =
      edge.left.map (Y.symmetry.toBraidedCategory.braiding U V).hom ≫
        (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          edge.left monoidal V U).inv


attribute [instance] Lift.right_additive

/-- Scalar-extension insertion referred to the given geometric inverse image.
Source: Stacks 03D7, 03EL (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
@[expose]
def Lift.insertion {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) (M : Y.modules) :
    f.inverse.obj (Y.sets.obj M) ⟶ X.sets.obj (l.edge.pullback.obj M) :=
  eqToHom (congrArg (fun F ↦ F.obj (Y.sets.obj M)) l.inverse_eq.symm) ≫ l.edge.insertion M

/-- The canonical K-flat representative map, without a new choice of isomorphism.
Source: Stacks 06YY, 0FPI (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Lift.alpha {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f)
    (P : CochainComplex Y.modules ℤ) :=
  derivedPullbackComplexComparison l.edge.pullback l.edge.left l.edge.epsilon P

/-- The inverse tensorator, equal to the uniquely characterized canonical tensor comparison.
Source: Stacks 07A4 (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Lift.tensor {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) (U V : Y.D) :=
  (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
    l.edge.left l.monoidal U V).symm

/-- The inverse unit comparison; its degree-zero normalization is `unit_canonical`.
Source: Stacks 07A4, 03EL (blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
abbrev Lift.unit {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) :=
  (@Functor.CoreMonoidal.εIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
    l.edge.left l.monoidal).symm

/-- Normalization for a composite represented by the specified geometric path isomorphism.
The ordinary comparison is fixed by insertion, and kappa by its right-derived units.
Source: Stacks 0D6D, 0D6E, 07A6, 03D8
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
structure Composition {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) where
  ordinary : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback
  ordinary_insertion : ∀ M : Z.modules,
    lk.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)
  ordinary_right : lk.edge.pushforward ≅ lf.edge.pushforward ⋙ lg.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction
      (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) ordinary.symm
  pullback : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left
  pullback_model : ∀ (P : CochainComplex Z.modules ℤ), Z.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫
      lf.edge.left.map (lg.alpha P) ≫
      lf.alpha ((lg.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    lk.alpha P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  kappa : lk.edge.right ≅ lf.edge.right ⋙ lg.edge.right
  kappa_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫ kappa.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          lg.edge.right.map (lf.eta.app I)
  tensor : ∀ U V : Z.D,
    pullback.hom.app (Z.closed.tensor.obj (U, V)) ≫
      lf.edge.left.map (lg.tensor U V).hom ≫
      (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
    (lk.tensor U V).hom ≫
      X.closed.tensor.map
        (X := (lk.edge.left.obj U, lk.edge.left.obj V))
        (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Z.closed.monoidal.tensorUnit ≫
      lf.edge.left.map lg.unit.hom ≫ lf.unit.hom = lk.unit.hom
  homEquiv : ∀ (U : Z.D) (E : X.D) (b : lk.edge.left.obj U ⟶ E),
    lk.edge.derivedAdjunction.homEquiv U E b ≫ kappa.hom.app E =
      (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction).homEquiv U E
        (pullback.inv.app U ≫ b)
  counit : ∀ E : X.D,
    lk.edge.left.map (kappa.hom.app E) ≫
      pullback.hom.app ((lf.edge.right ⋙ lg.edge.right).obj E) ≫
      lf.edge.left.map (lg.edge.derivedAdjunction.counit.app (lf.edge.right.obj E)) ≫
      lf.edge.derivedAdjunction.counit.app E = lk.edge.derivedAdjunction.counit.app E


/-- Identity normalization, including the specified tensor and the entire adjunction.
Source: Stacks 07A4, 07A6, 03D7
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
structure Identity {X : Site.{u, w}} {f : Morphism X X} (l : Lift f)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))) where
  ordinary : l.edge.pullback ≅ 𝟭 X.modules
  ordinary_insertion : ∀ M : X.modules,
    l.insertion M ≫ X.sets.map (ordinary.hom.app M) = θ.hom.app (X.sets.obj M)
  ordinary_right : l.edge.pushforward ≅ 𝟭 X.modules
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv l.edge.moduleAdjunction (Adjunction.id (C := X.modules)) ordinary.symm
  pullback : l.edge.left ≅ 𝟭 X.D
  pullback_model : ∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
    ∃ a : (l.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ P,
      (∀ n : ℤ, a.f n = ordinary.hom.app (P.X n)) ∧
      pullback.hom.app (DerivedCategory.Q.obj P) = l.alpha P ≫ DerivedCategory.Q.map a
  pushforward : l.edge.right ≅ 𝟭 X.D
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    ∃ a : (l.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ I,
      (∀ n : ℤ, a.f n = ordinary_right.hom.app (I.X n)) ∧
      l.eta.app I ≫ pushforward.hom.app (DerivedCategory.Q.obj I) = DerivedCategory.Q.map a
  tensor : ∀ U V : X.D,
    (l.tensor U V).hom ≫ X.closed.tensor.map
        (X := (l.edge.left.obj U, l.edge.left.obj V)) (Y := (U, V))
        (pullback.hom.app U, pullback.hom.app V) =
      pullback.hom.app (X.closed.tensor.obj (U, V))
  unit : l.unit.hom = pullback.hom.app X.closed.monoidal.tensorUnit
  homEquiv : ∀ (U E : X.D) (b : l.edge.left.obj U ⟶ E),
    l.edge.derivedAdjunction.homEquiv U E b ≫ pushforward.hom.app E =
      (Adjunction.id (C := X.D)).homEquiv U E (pullback.inv.app U ≫ b)


/-- Transport along the given, ring-compatible geometric 2-isomorphism.
The insertion equation fixes its value on every generalized scalar-extension generator.
Source: Stacks 03D7, 03EL, 07A4, 07A6
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons). -/
structure TwoIso {X Y : Site.{u, w}} {h k : Morphism X Y}
    (lh : Lift h) (lk : Lift k) (θ : h.inverse ≅ k.inverse) where
  ordinary : lh.edge.pullback ≅ lk.edge.pullback
  ordinary_insertion : ∀ M : Y.modules,
    lh.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Y.sets.obj M) ≫ lk.insertion M
  ordinary_right : lk.edge.pushforward ≅ lh.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction lh.edge.moduleAdjunction ordinary
  pullback : lh.edge.left ≅ lk.edge.left
  pullback_model : ∀ P : CochainComplex Y.modules ℤ, Y.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫ lk.alpha P =
      lh.alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  pushforward : lk.edge.right ≅ lh.edge.right
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫ pushforward.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lh.eta.app I
  tensor : ∀ U V : Y.D,
    pullback.hom.app (Y.closed.tensor.obj (U, V)) ≫ (lk.tensor U V).hom =
      (lh.tensor U V).hom ≫ X.closed.tensor.map
        (X := (lh.edge.left.obj U, lh.edge.left.obj V))
        (Y := (lk.edge.left.obj U, lk.edge.left.obj V))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Y.closed.monoidal.tensorUnit ≫ lk.unit.hom = lh.unit.hom
  homEquiv : ∀ (U : Y.D) (E : X.D) (b : lk.edge.left.obj U ⟶ E),
    lh.edge.derivedAdjunction.homEquiv U E (pullback.hom.app U ≫ b) =
      lk.edge.derivedAdjunction.homEquiv U E b ≫ pushforward.hom.app E


set_option linter.checkUnivs false in
/-- All clauses of the normalization statement, universally over the presented sites.
Source: Stacks 07A4, 0D6D, 07A6, 0D6E, 0FPI
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).
The auxiliary morphism k is the composite represented by theta; allowing any such
presentation also retains arbitrary ring-compatible path isomorphisms. -/
structure System where
  lift : ∀ {X Y : Site.{u, w}}, (f : Morphism X Y) → Lift f
  composites : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z),
    ∃ (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
      k.ringMap = θ.hom.app ((sheafCompose Z.J
        (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
          f.inverse.map g.ringMap ≫ f.ringMap
  identities : ∀ X : Site.{u, w},
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A)
  composition : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z)
    (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
    k.ringMap = θ.hom.app ((sheafCompose Z.J
      (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
        f.inverse.map g.ringMap ≫ f.ringMap →
    Nonempty (Composition (lift f) (lift g) (lift k) θ)
  identity : ∀ (X : Site.{u, w}) (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
    f.ringMap = θ.hom.app ((sheafCompose X.J
      (CategoryTheory.forget CommRingCat.{u})).obj X.A) → Nonempty (Identity (lift f) θ)
  twoIso : ∀ {X Y : Site.{u, w}} (h k : Morphism X Y) (θ : h.inverse ≅ k.inverse),
    h.ringMap = θ.hom.app ((sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫ k.ringMap →
    Nonempty (TwoIso (lift h) (lift k) θ)


/-- The canonical derived comparisons are symmetric strong monoidal, and composition,
identity and specified ring-compatible geometric 2-isomorphisms respect the actual
canonical adjunctions.
Source: Stacks 07A4, 0D6D, 07A6, 0D6E, 0FPI; 03D7, 03D8, 03EL
(blueprint: lem-sfb-ringed-derived-monoidal-comparisons).

Proof: use flat-term K-flat representatives simultaneously for tensor and successive
pullbacks. Descend the ordinary pure-tensor comparisons, their signed associator,
symmetry and both action-unit diagrams. Ordinary scalar association sends t tensor z
to t tensor (1 tensor z), so multiplication proves the unit composition equation.
The underlying geometric Hom bijections and scalar insertion identify the ordinary
composite adjunction with the one for the composite morphism. On a K-flat P and a
K-injective I the inverse derived Hom bijection is Q of the ordinary transpose, after
alpha. Represent any derived map by a right fraction and replace its source once by
a flat-term K-flat resolution. For a resolution j of f_*I, kappa is represented by
Q(g_*j); counit naturality moves j through the ordinary transpose. The two alpha maps
and the pullback comparison give Q of scalar association, so the ordinary calculation
proves equality of the derived Hom bijections. This proves both units and counits;
the counit of Adjunction.comp gives the displayed formula. Identity scalar insertion
and the identity K-injective resolution give the identity tensor and Hom bijection.
For a specified geometric theta commuting with ring maps, transport the algebraic
inverse image; scalar extension sends s tensor x to s tensor theta(x). This respects
balancing precisely by ring compatibility. Test tensor and unit diagrams on pure
tensors and localize. Underlying geometric transposition and scalar insertion show
that the ordinary right comparison is its mate. Applying the same representative Hom
formula with the right-derived unit proves the last adjunction-compatibility clause.
No step assumes flat structural maps, bounded complexes, or preservation of K-injectives
by an ordinary direct image.

Detailed DAG proof plan:
1. For a ring sheaf $A$, write $Q_A:K(A)\to D(A)$ and let $\mathcal P_A$ be the flat-term K-flat
complexes. The cited descent theorem identifies $D(A)$ with the localization of $\mathcal P_A$ at
quasi-isomorphisms. The cited total-tensor model says that $P\otimes Q$ lies in $\mathcal P_A$ for
$P,Q\in\mathcal P_A$ and represents their derived tensor. The cited derived-pullback comparison
identifies $P_hQ_AP$ with $Q(h^*P)$ naturally on this class, and the tensor-pullback theorem says
$h^*P$ again lies in the corresponding resolving class. Thus repeated tensor products and
successive pullbacks may all be computed on the same representatives; no intermediate replacement
is needed. Equalities between natural transformations of derived functors can be checked on these
representatives: every derived object is isomorphic to one of them, and naturality conjugates its
component equality by that isomorphism. For transformations defined on representatives, use the
cited localization universal property to descend them.
Dependencies: lem-weil-pbc-site-derived-tensor-descent, lem-pur-kflat-total-tensor-model,
lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-localization-universal-property.

2. Use the symmetric monoidal structure on $D(A)$ of the cited ringed-site theorem: its unit is
$A[0]$, its associator is ordinary reassociation of total tensors, and its symmetry on bidegree
$(p,q)$ has sign $(-1)^{pq}$. On $P,Q\in\mathcal P_A$, the canonical $t_h$ is the localization of
the cochain map $c_{h;P,Q}$ of the cited cochain-coherence node; $e_h$ is the localized action map
$h^*A[0]\cong A'[0]$. That node states the cochain associator, both unitor, and signed-symmetry
squares. Localizing those squares gives precisely the corresponding squares for $t_h,e_h$ on
representatives. Step 1 then gives them on arbitrary derived objects (for the associator take
three representatives). Their invertibility and naturality are supplied by the tensor-pullback
theorem. Hence these particular comparisons, with the inverse-structure-map convention in the
strong monoidal definition, make $P_h$ symmetric strong monoidal.
Dependencies: lem-sf-ringed-derived-closed-symmetric-monoidal,
lem-pur-cochain-pullback-tensor-coherence, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
def-sfb-strong-monoidal-functor.

3. For $P\in\mathcal P_{A_Z}$, both $P_{gf}QP$ and $P_fP_gQP$ are computed respectively by
$(gf)^*P$ and $f^*g^*P$: $g^*P$ is still flat-term K-flat. Localize the ordinary comparison
$a_P:(gf)^*P\cong f^*g^*P$ specified in the cochain-coherence node. It is natural on the homotopy
category and descends uniquely by the localization universal property to $c_{f,g}$, using the
resolving-class equivalence of step 1. For $P,Q\in\mathcal P_{A_Z}$, that cochain node gives
$$(a_P\otimes a_Q)c_{gf;P,Q}=c_{f;g^*P,g^*Q}\,f^*(c_{g;P,Q})\,a_{\operatorname{Tot}(P\otimes
Q)}.$$
All complexes in this equation are valid representatives by step 1. Localization gives the
asserted tensor equation for $c_{f,g}$ on $QP,QQ$; naturality and essential surjectivity give it
for every $U,V$.
Dependencies: lem-weil-pbc-ringed-topoi-derived-pullback,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pur-cochain-pullback-tensor-coherence,
lem-weil-pbc-localization-universal-property.

4. The comparison $a$ in step 3 is inverse to multiplication of the two scalar-extension factors.
On the unit it sends $t\otimes z$ to $t\otimes(1\otimes z)$, with inverse $t\otimes(s\otimes
z)\mapsto t f^\sharp(s)\otimes z$ (inverse-image identifications understood). Applying $f^*(e_g)$
and then $e_f$ therefore gives $t(gf)^\sharp(z)$, which is also $e_{gf}(t\otimes z)$. Pure tensors
determine sheaf-linear maps by the cited section calculus. This proves
$e_fP_f(e_g)c_{f,g,A_Z}=e_{gf}$ after localization. The unit complexes and their pullbacks are
valid flat-term K-flat representatives by the model and pullback facts in step 1.
Dependencies: lem-pur-cochain-pullback-tensor-coherence,
def-weil-pbc-ringed-tensor-section-calculus.

5. Let $\epsilon_h^0:h^*h_*\to1$ denote the ordinary module counit. Under $a_P:(gf)^*P\cong
f^*g^*P$ and $(gf)_*=g_*f_*$, the ordinary transpose of $b:P\to g_*f_*I$ is
$$\epsilon_{f,I}^0\,f^*(\epsilon_{g,f_*I}^0\,g^*b)\,a_P.$$
Indeed the module adjunction is inverse-image transposition followed by scalar extension. The
cited geometric-module transport fixes that inverse-image transposition on underlying sheaves, and
the section calculus fixes scalar-extension insertion as $x\mapsto1\otimes x$. The two successive
transpositions therefore insert $1\otimes(1\otimes x)$; $a$ identifies this with $1\otimes x$.
Multiplication of a general outer scalar gives the same result on every $t\otimes x$, which
determines the map. The geometric part is precisely composition of the given inverse-image Hom
bijections. Thus these Hom bijections agree, degree by degree. The termwise-adjunction theorem
passes this equality to homotopy classes. This verifies the ordinary adjunction normalization of
the specific scalar-association comparison, rather than choosing a different comparison from
abstract adjoint uniqueness.
Dependencies: lem-weil-pbc-ringed-topoi-module-adjunction,
lem-weil-pbc-geometric-module-transport, def-weil-pbc-ringed-tensor-section-calculus,
lem-pur-cochain-pullback-tensor-coherence, def-weil-pbc-composite-adjunction,
lem-weil-pbc-termwise-adjunction-homotopy.

6. Write $\alpha_{h,P}:P_hQP\cong Qh^*P$ for the flat-term K-flat comparison and
$\beta_{h,I}:Qh_*I\cong R_hQI$ for the K-injective right-derived unit. The inverse of the
canonical derived Hom bijection, denoted $\Theta_h$, satisfies
$$\Theta_h(\beta_{h,I}\,Qb)=Q(\epsilon_{h,I}^0\,h^*b)\,\alpha_{h,P}\quad(b:P\to h_*I).$$
This is the explicit formula of the cited pre-derived-adjunction theorem with target resolution
$I\xrightarrow{1}I$ and source resolution $P\xrightarrow{1}P$, not an extra compatibility
assumption. The derived pullback theorem makes $\alpha_{h,P}$ invertible and the
right-derived-functor definition makes $\beta_{h,I}$ invertible. The canonical derived adjunction
in the item is the everywhere-defined adjunction assembled from these same Hom bijections. For a
quasi-isomorphism $s:P'\to P$ with $P'$ flat-term K-flat, naturality gives
$$\Theta_h(\beta_{h,I}Qb\,(Qs)^{-1})=Q(\epsilon_{h,I}^0h^*b)\,\alpha_{h,P'}\,(P_hQs)^{-1}.$$
Thus the formula also treats fraction representatives.
Dependencies: lem-pc-pre-derived-adjoint-functors-general, lem-pc-derived-adjoint-functors,
lem-weil-pbc-ringed-topoi-derived-pullback, def-sfb-right-derived-functor,
lem-weil-pbc-termwise-adjunction-homotopy.

7. Fix a K-injective $I$ on $X$, and choose a K-injective resolution $j:f_*I\to J$ on $Y$. The
pushforward-composition node states that $g_*j$ is a quasi-isomorphism and that $\kappa_{g,f,QI}$
is its localized class under the resolution identifications. No assertion that $f_*I$ is
K-injective is needed. To compare the derived Hom bijections on every morphism into $R_{gf}QI\cong
Qg_*f_*I$, represent a morphism out of $QN$ by a right fraction
$N\xleftarrow{s}P\xrightarrow{b}g_*f_*I$. Resolve $P$ once more by a flat-term K-flat complex and
compose the denominator and numerator with that resolution. This is again the same fraction.
Existence follows from the cited calculus-of-fractions and K-flat-resolution nodes. It therefore
suffices, by the naturality in step 6, to do the calculation for an actual map $b:P\to g_*f_*I$
with $P$ flat-term K-flat.
Dependencies: prop-pur-kinjective-resolutions-exist,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-pc-quasi-isomorphisms-multiplicative-system, lem-pc-right-fraction-representation,
lem-pc-kflat-resolution.

8. Put $v=\epsilon_{g,f_*I}^0g^*b:g^*P\to f_*I$. After applying $\kappa$, the map represented by
$b$ is represented on $Y$'s chosen K-injective resolution by $(g_*j)b:P\to g_*J$. Step 6 for $g$
sends it to
$$Q(\epsilon_{g,J}^0\,g^*((g_*j)b))\,\alpha_{g,P}=Q(jv)\,\alpha_{g,P}.$$
The equality is exactly naturality of the ordinary counit at $j$:
$\epsilon_{g,J}^0g^*(g_*j)=j\epsilon_{g,f_*I}^0$. Under the isomorphism $QJ\cong R_fQI$, the map
$Q(jv)$ is $\beta_{f,I}Qv$. Apply step 6 for $f$ to it. This is permitted because $g^*P$ is
flat-term K-flat by the tensor-pullback node. The resulting composite transpose is
$$Q(\epsilon_{f,I}^0 f^*v)\,\alpha_{f,g^*P}\,P_f(\alpha_{g,P}).$$
Explicitly the identification is $\iota_J=\beta_{f,I}(Qj)^{-1}:QJ\cong R_fQI$, so
$\iota_JQ(jv)=\beta_{f,I}Qv$; only invertibility of the quasi-isomorphism $Qj$ is used.
Dependencies: lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-weil-pbc-termwise-adjunction-homotopy, def-sfb-right-derived-functor,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

9. Precompose the last map of step 8 with $c_{f,g,QP}$. By the construction in step 3, the
composite of $c_{f,g,QP}$ with the two $\alpha$-comparisons is $Q(a_P)\alpha_{gf,P}$. Hence the
result is
$$Q(\epsilon_{f,I}^0 f^*(\epsilon_{g,f_*I}^0g^*b)a_P)\,\alpha_{gf,P}.$$
By the ordinary calculation of step 5 this is $Q(\epsilon_{gf,I}^0(gf)^*b)\alpha_{gf,P}$, which
step 6 identifies with $\Theta_{gf}(\beta_{gf,I}Qb)$. Step 7 and naturality give the equality for
every derived morphism out of every object into $R_{gf}QI$. Every $E\in D(A_X)$ has a K-injective
representative, so the same equality holds for every $E$. This proves that under precisely $c$ and
the specified $\kappa$, the canonical Hom bijection for $gf$ equals the composite canonical Hom
bijection. Since units and counits are the transposes of identities, this is compatibility of the
actual adjunctions.
Dependencies: lem-weil-pbc-ringed-topoi-derived-pullback,
lem-pur-cochain-pullback-tensor-coherence,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-pc-pre-derived-adjoint-functors-general, prop-pur-kinjective-resolutions-exist,
lem-weil-pbc-adjunction-of-natural-bijection.

10. Apply the definition of composite adjunction to the equality of Hom bijections just proved. In
full, the counit formula is
$$\varepsilon_{gf,E}=\varepsilon_{f,E}\,P_f(\varepsilon_{g,R_fE})\,c_{f,g,R_gR_fE}
\,P_{gf}(\kappa_{g,f,E}).$$
Its domain is $P_{gf}R_{gf}E$ and codomain is $E$. With these comparisons suppressed, it is
exactly the counit formula stated in the item. The unit is likewise the composite unit because the
same bijection sends the identity of the left-adjoint value to its unit.
Dependencies: def-weil-pbc-composite-adjunction, lem-weil-pbc-adjunction-of-natural-bijection.

11. For the identity geometric morphism with identity structural ring map, ordinary module
pullback is $A\otimes_A-$ and its action isomorphism to the identity has inverse $x\mapsto1\otimes
x$. The sheaf tensor section calculus shows that under this isomorphism $c_{\mathrm{id};P,Q}$
sends $x\otimes y$ to itself and the unit map sends $1$ to $1$. These equalities localize on
flat-term K-flat representatives, so identify the derived tensor comparisons with those of the
identity. Ordinary direct image is the identity. Its right-derived comparison on $I$ is $QI\cong
QI$ using the identity K-injective resolution; step 6 reduces to the identity Hom bijection. Thus
the canonical identity comparisons identify both unit and counit with identity maps, as required
by the definition of identity adjunction.
Dependencies: def-weil-pbc-ringed-tensor-section-calculus,
lem-pur-cochain-pullback-tensor-coherence, def-sfb-right-derived-functor,
def-weil-pbc-composite-adjunction.

12. Let $h,k:X\to Y$ and let the specified geometric 2-isomorphism have inverse-image component
$\theta:h^{-1}\cong k^{-1}$. Naturality at addition, multiplication, zero, one, and scalar action,
together with the canonical finite-product comparisons, identifies the transported ring and module
structures in the geometric-module-transport node. Commutation with the structural ring maps makes
$$d_M:h^*M\longrightarrow k^*M,\qquad s\otimes x\longmapsto s\otimes\theta_M(x)$$
well-defined; the inverse uses $\theta^{-1}$. This is an equation on generalized sheaf elements
using the transported-ring identifications. The section calculus proves naturality and equality of
maps from their pure-tensor values. Tensor compatibility is the two-line equality sending
$s\otimes(x\otimes y)$ along either route to $(s\otimes\theta x)\otimes(1\otimes\theta y)$; unit
compatibility follows from $s\otimes a\mapsto s h^\sharp(a)=s k^\sharp(\theta a)$. The right
component is the geometric mate of $\theta$; the geometric-module Hom formula and the
scalar-extension insertion show that it induces the corresponding module direct-image isomorphism
and intertwines the ordinary Hom bijections. These computations work termwise, including the
signed tensor differential.
Dependencies: lem-weil-pbc-geometric-module-transport,
def-weil-pbc-ringed-tensor-section-calculus, lem-weil-pbc-ringed-topoi-module-adjunction,
lem-pur-cochain-pullback-tensor-coherence, def-weil-pbc-adjunction-conjugate.

13. Apply $d$ termwise to flat-term K-flat representatives. The derived-pullback identifications
and the localization universal property give a natural isomorphism $P_h\cong P_k$, with inverse
induced by $d^{-1}$. Localize the tensor and unit equalities in step 12 and use step 1 to get a
monoidal isomorphism on every derived object. On direct images use the same K-injective
representative $I$ of the source object for both functors, and apply the right component of the
given geometric 2-isomorphism to $I$; this gives a chain isomorphism $h_*I\cong k_*I$ and hence
the canonical derived direct-image isomorphism. In the formula of step 6 the ordinary transposes
agree by step 12, so their localized transposes agree. Fractions and K-injective representatives
as in step 7 cover all arguments, proving adjunction compatibility. The conjugate bijection
identifies this isomorphism with the corresponding adjunction mate, fixing its normalization. All
representatives here are unbounded ones; the only pullback preservation used is the flat-term
K-flat theorem, which imposes no flatness on structural ring maps.
Dependencies: lem-weil-pbc-ringed-topoi-derived-pullback,
lem-weil-pbc-localization-universal-property, def-sfb-right-derived-functor,
lem-pc-pre-derived-adjoint-functors-general, def-weil-pbc-adjunction-conjugate,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. -/
theorem ringedDerivedMonoidalComparisons : Nonempty (System.{u, w}) := by
  sorry

end CategoryTheory.RingedDerivedComparisons
