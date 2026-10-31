/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Compatible central scalars and derived ringed-topos pullback

Source: Stacks Project, Cohomology on Sites, Tag 06YY (lemma-derived-base-change),
Modules on Sites, Tag 03D6 (definition-pushforward), and Conventions, section-algebra.
The compatible-central-scalar refinement is the agent-supplied prerequisite implicit
in the K-flat computation (blueprint: lem-pur-ringed-derived-pullback-linear).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Restrict the existing global-section action on module-sheaf Hom groups along `s`.
On a morphism `f`, its value at `U,x` is `(s r).val U • f.val.app U x`.
This is the actual sectionwise action, with Mathlib's existing preadditive structure.

Source: Stacks Project, Modules on Sites, Tag 03D6; Conventions, section-algebra
(blueprint: lem-pur-ringed-derived-pullback-linear). -/
@[instance_reducible]
noncomputable def scalarSectionLinear
    (R : Type v) [CommRing R] {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (A : Sheaf J CommRingCat.{u})
    (s : R →+* RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat)) :
    Linear R (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)) := by
  letI : Linear (RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))
      (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A)) :=
    homLinear A.obj (RingedTensor.ringSheaf A).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) s
      smul_comp := fun M N P r f g ↦ Linear.smul_comp M N P (s r) f g
      comp_smul := fun M N P f r g ↦ Linear.comp_smul M N P f (s r) g }

/-- Canonical K-flat derived pullback is linear over compatible actual scalar sections.
The two module-category structures are the explicitly constructed sectionwise actions;
the derived structures are Mathlib's induced localization structures. The universal
property on `LF,epsilon` specifies the left derived functor, not an arbitrary functor
with objectwise comparison isomorphisms. It includes the canonical K-flat construction
of `ringedTopoiDerivedPullback` and every realization canonically isomorphic to it.
The generalized-element form of `hs` says exactly that the structural map sends the
inverse image of each global scalar section to the specified target scalar section.

Source: Stacks Project, Cohomology on Sites, Tag 06YY (lemma-derived-base-change),
Modules on Sites, Tag 03D6, and Conventions, section-algebra. The scalar refinement
is agent supplied (blueprint: lem-pur-ringed-derived-pullback-linear).

Proof:
1. For the test sheaf underlying a module M, transport the equation expressing scalar
multiplication by `sA r` through `I.moduleSMul`. Naturality of the underlying-sheaf
isomorphism identifies its image with the corresponding module endomorphism. The
compatibilities `hstruct` and `hs` identify the image of the scalar with `sB r`.
2. Tensor balancing gives `1 tensor (k • m) = c(k) • (1 tensor m)`. The module
sheafification adjunction and extension-of-scalars Hom extensionality reduce equality
of the sheaf maps to this calculation. Transport by `hobj` and `hmap`, and apply
`Functor.linear_iff`, to obtain ordinary pullback linearity.
3. The exact derived realization supplied by the existing K-flat derived-pullback
construction is additive. Uniqueness of the left derived functor transports this
additivity to the supplied realization `LF`.
4. For each scalar r compare the natural endomorphisms `LF.map (r • id)` and `r • id`
of LF. The left-derived universal property `Functor.leftDerived_ext` reduces equality
to naturality of epsilon at `r • id`. Ordinary pullback and localization are linear,
so this naturality equation is exactly the required equality. Finally use
`Functor.linear_iff` to obtain linearity on every Hom group. No additional K-flat
resolutions or flatness of the structural map are needed. -/
theorem ringedDerivedPullback_linear
    (R : Type v) [CommRing R]
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (A : Sheaf JC CommRingCat.{u}) (B : Sheaf JD CommRingCat.{u})
    (u : RingedToposMorphism
      (RingedTensor.ringSheaf B)
      (RingedTensor.ringSheaf A))
    (AI : Sheaf JD CommRingCat.{u}) (I : AlgebraicInverseImage u.inverse A AI)
    (c : AI ⟶ B)
    (hstruct : I.ringUnderlying.hom ≫
      (sheafCompose JD (CategoryTheory.forget CommRingCat)).map c = u.ringMap)
    (sA : R →+* RingCat.sectionsSubring (A.obj ⋙ forget₂ CommRingCat RingCat))
    (sB : R →+* RingCat.sectionsSubring (B.obj ⋙ forget₂ CommRingCat RingCat))
    (hs : ∀ (r : R) (T : Sheaf JC (Type u))
      (a : T ⟶ (sheafCompose JC (CategoryTheory.forget CommRingCat)).obj A),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U), a.hom.app U x = (sA r).val U) →
      ∀ (V : Dᵒᵖ) (x : (u.inverse.obj T).obj.obj V),
        ((u.inverse.map a) ≫ u.ringMap).hom.app V x = (sB r).val V)
    (uStar : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A) ⥤
      ringedSiteModules.{u, u, u, u} (RingedTensor.ringSheaf B))
    (hobj : ∀ M : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)} (f : M ⟶ N),
      uStar.map f = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf B))]
    (LF : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      (RingedTensor.ringSheaf A)) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf B)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A)) (ComplexShape.up ℤ))] :
    (fun [_lA : Linear R (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf A))]
      [_lB : Linear R (ringedSiteModules.{u, u, u, u}
        (RingedTensor.ringSheaf B))] ↦
      LF.Additive ∧ Functor.Linear R LF ∧
        ∀ (X : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
          (RingedTensor.ringSheaf A))) (r : R),
          LF.map (r • (𝟙 X : X ⟶ X)) =
            r • (𝟙 (LF.obj X) : LF.obj X ⟶ LF.obj X))
      (_lA := scalarSectionLinear R A sA) (_lB := scalarSectionLinear R B sB) := by
  sorry

end SheafOfModules
