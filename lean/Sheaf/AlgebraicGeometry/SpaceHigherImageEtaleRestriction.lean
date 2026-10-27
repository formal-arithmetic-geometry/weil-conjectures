module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Higher module direct images and étale restriction on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03LX, via Tag 03LR;
Modules on Sites, Tags 03DH and 03DJ
(blueprint: lem-sfb-space-higher-image-etale-restriction).

All operations use the existing small affine ringed model and its actual module
restriction equivalence, without changing the coefficient universe. The ordinary
comparison is fixed on chart sections. The derived comparison is fixed by that
ordinary comparison and the universal right-derived units. Its cohomology on modules
in degree zero gives the requested higher images, in every nonnegative degree.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/-- The existing ordinary comparison, expressed using the specified tensor pullbacks.
The choices below retain the chart-section and local-tensor normalizations of the
recorded comparison and of tensor restriction; they are not unnormalized isomorphisms.
Source: Stacks, Tag 03LX (blueprint: lem-sfb-space-higher-image-etale-restriction). -/
def tensorEtaleModuleBaseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom) :
    moduleDirectImage f ⋙ moduleTensorPullback g ≅
      moduleTensorPullback h ⋙ moduleDirectImage f' :=
  isoWhiskerLeft (moduleDirectImage f)
      (moduleTensorPullback_etale_restriction g hg).choose ≪≫
    (etale_module_pushforward_restriction f g h f' hg hp).choose_spec.choose ≪≫
    isoWhiskerRight
      (moduleTensorPullback_etale_restriction h
        (etale_module_pushforward_restriction f g h f' hg hp).choose).choose.symm
      (moduleDirectImage f')

/-- The same comparison on the already fixed small affine module models. Cancellation
uses only the units of the specified module equivalences, so the chart normalization
is retained, including when the base-change map is the identity or is not surjective.
Source: Stacks, Tag 03LX (blueprint: lem-sfb-space-higher-image-etale-restriction). -/
def smallTensorEtaleModuleBaseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom) :
    smallModuleDirectImage f ⋙ smallModuleTensorPullback g ≅
      smallModuleTensorPullback h ⋙ smallModuleDirectImage f' :=
  isoWhiskerLeft X.smallModuleEquivalence.inverse
      (isoWhiskerLeft (moduleDirectImage f)
        (Y.smallModuleEquivalence.funInvIdAssoc
          (moduleTensorPullback g ⋙ Y'.smallModuleRestriction))) ≪≫
    isoWhiskerLeft X.smallModuleEquivalence.inverse
      (isoWhiskerRight (tensorEtaleModuleBaseChange f g h f' hg hp)
        Y'.smallModuleRestriction) ≪≫
    (isoWhiskerLeft X.smallModuleEquivalence.inverse
      (isoWhiskerLeft (moduleTensorPullback h)
        (X'.smallModuleEquivalence.funInvIdAssoc
          (moduleDirectImage f' ⋙ Y'.smallModuleRestriction)))).symm

section Derived

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
  [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} Y'.SmallModules]

/-- Canonical derived étale restriction of module direct images, with its universal
unit normalization. The following theorem states its cohomology on all module sheaves.

Source: Stacks, Tag 03LX, via Tag 03LR; Tags 03DH and 03DJ
(blueprint: lem-sfb-space-higher-image-etale-restriction).

Proof:
1. Use the enlarged étale ringed-site model and chartwise étale permanence to identify
both horizontal tensor pullbacks with localized restriction. Base change proves h
étale without any surjectivity assumption on g. The exact localized adjunction
supplies exact extension by zero left adjoint to restriction.
2. By the right-adjoint-preserves-injectives theorem restriction preserves injectives.
The complex adjunction also preserves K-injectives: maps from an acyclic complex
into the restriction correspond to maps from its exact extension by zero.
3. Module categories on the existing small ringed models are Grothendieck abelian.
The ringed-site resolution theorem supplies K-injective resolutions (and ordinary
injective resolutions for modules). Exact restriction preserves the augmented exact
sequence and sends these resolutions to resolutions.
4. Apply the recorded ordinary chart-normalized comparison to every resolution term.
Its naturality for the differentials gives an isomorphism of complexes.
5. Exact restriction commutes with cohomology. The derived units compute direct image
on K-injective resolutions. Thus the termwise comparison induces the displayed
isomorphism, characterized by its compatibility with those units.
6. Lift a module map to resolutions. Naturality of the ordinary comparison gives a
commuting square of complexes. The map-via-lift and resolution-lifting statements
identify its cohomology maps with the derived maps. Different lifts are homotopic;
comparison of two resolutions gives independence of the resolution. Equivalently,
uniqueness of right derived functors proves the displayed unit-normalized uniqueness.
All arguments concern all module sheaves and impose no finiteness hypotheses. -/
theorem derived_moduleDirectImage_etale_restriction
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom) :
    ∃! beta : derivedDirectImage f ⋙ (smallModuleTensorPullback g).rightDerivedFunctor ≅
        (smallModuleTensorPullback h).rightDerivedFunctor ⋙ derivedDirectImage f',
      ∀ K : HomotopyCategory X.SmallModules (ComplexShape.up ℤ),
        (Functor.rightDerivedFunctorCompUnit
            (smallModuleDirectImage f) (smallModuleTensorPullback g)).app K ≫
          beta.hom.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory
              (smallTensorEtaleModuleBaseChange f g h f' hg hp).hom (.up ℤ)).app K) ≫
          (Functor.rightDerivedFunctorCompUnit
            (smallModuleTensorPullback h) (smallModuleDirectImage f')).app K := by
  sorry

/-- Higher direct images of all structure modules commute with étale restriction.
The value displayed is cohomology of the existing right derived functor on the
module in degree zero; by injective-resolution comparison it is exactly R^q f_* M.
Both pullbacks are the original tensor pullbacks, transported by the fixed small
model. A functor isomorphism records naturality for every module morphism at once.

Source: Stacks, Tag 03LX (blueprint: lem-sfb-space-higher-image-etale-restriction).
Proof: apply degree-q cohomology to derived_moduleDirectImage_etale_restriction
on modules embedded in degree zero. Exactness of the two restrictions commutes
with cohomology and with the degree-zero embedding. The injective-resolution
comparison isoRightDerivedObj identifies this with the classical right derived
functor in def-sp-left-exact-additive. Its degree-zero identification is the
ordinary chart comparison: the augmented comparison commutes with M to I^0 and
induces that map on the kernels. Resolution lifting gives the module naturality
and independence as in steps 5 and 6 of the preceding theorem. -/
theorem higher_moduleDirectImage_etale_restriction
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (f' : X' ⟶ Y')
    (hg : IsEtale g.hom.hom) (hp : IsPullback h.hom f'.hom f.hom g.hom) (q : ℕ) :
    Nonempty
      (DerivedCategory.singleFunctor X.SmallModules 0 ⋙ derivedDirectImage f ⋙
          DerivedCategory.homologyFunctor Y.SmallModules (q : ℤ) ⋙
          smallModuleTensorPullback g ≅
        smallModuleTensorPullback h ⋙ DerivedCategory.singleFunctor X'.SmallModules 0 ⋙
          derivedDirectImage f' ⋙ DerivedCategory.homologyFunctor Y'.SmallModules (q : ℤ)) := by
  sorry

end Derived

end AlgebraicGeometry.AlgebraicSpace
