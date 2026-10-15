/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-!
# Ordinary derived operations with identified pro-etale coefficients

Source: Weil conjectures blueprint, proper base change, definition of derived operations;
Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules, and Cohomology on Sites,
Sections 07A5 and 0735 (blueprint: def-weil-pbc-proetale-operations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Modules over an arbitrary commutative coefficient sheaf on the original small site.
Source: Stacks, Modules on Sites (blueprint: def-weil-pbc-proetale-operations). -/
abbrev proEtaleRingModules (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard localization at quasi-isomorphisms, with no completion or boundedness.
Source: Stacks, Tag 05RU (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance proEtaleRingModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (proEtaleRingModules X R) :=
  HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The ring map adjoint to the fixed identification of inverse-image coefficients.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingDirectImageMap :
    R ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S :=
  (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R ≫
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map c.hom

/-- Sectionwise direct image, with scalar action through the adjoint coefficient map.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingModuleDirectImage :
    proEtaleRingModules X S ⥤ proEtaleRingModules Y R :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R S c).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The displayed inverse image: inverse-image module action followed by sheafified tensor
extension along `c`. Source: Stacks, lemma-adjoint-push-pull-modules and Tag 03EK
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingModulePullbackObj (M : proEtaleRingModules Y R) :
    proEtaleRingModules X S :=
  SheafOfModules.changeOfRings.{u, u + 1, u + 1} c.hom ((proEtaleModuleInverseImage f R).obj M)

/-- The inverse-image map followed by the sheafified map on tensors.
Source: Stacks, Tag 03EK (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingModulePullbackMap {M N : proEtaleRingModules Y R} (a : M ⟶ N) :
    proEtaleRingModulePullbackObj f R S c M ⟶ proEtaleRingModulePullbackObj f R S c N :=
  SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom _ ((proEtaleModuleInverseImage f R).map a)

/-- The specified tensor maps respect identities and composition.
Source: Stacks, Tag 03EK (blueprint: def-weil-pbc-proetale-operations).
Proof: the inverse-image functor respects both operations. On each presheaf tensor,
`id ⊗ a` respects both operations on pure tensors, which generate the tensor product.
The sheafification functor preserves these equalities. -/
theorem proEtaleRingModulePullback_functorial :
    (∀ M : proEtaleRingModules Y R,
      proEtaleRingModulePullbackMap f R S c (𝟙 M) = 𝟙 _) ∧
    (∀ (M N P : proEtaleRingModules Y R) (a : M ⟶ N) (b : N ⟶ P),
      proEtaleRingModulePullbackMap f R S c (a ≫ b) =
        proEtaleRingModulePullbackMap f R S c a ≫ proEtaleRingModulePullbackMap f R S c b) := by
  sorry

/-- The module pullback functor, with the actual sheaf tensor construction as its objects.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingModulePullback :
    proEtaleRingModules Y R ⥤ proEtaleRingModules X S where
  obj := proEtaleRingModulePullbackObj f R S c
  map := proEtaleRingModulePullbackMap f R S c
  map_id := (proEtaleRingModulePullback_functorial f R S c).1
  map_comp := (proEtaleRingModulePullback_functorial f R S c).2 _ _ _

/-- Both module operations are additive, pullback is exact, and they are adjoint.
Source: Stacks, lemma-adjoint-push-pull-modules and Tag 04JC
(blueprint: def-weil-pbc-proetale-operations).
Proof: apply inverse image to the action map under its product comparison. Apply direct
image to the action and restrict along the ring unit. Naturality of the unit and its
product compatibility show that an abelian map is linear iff its adjunct is linear.
Restrict the sheaf adjunction to linear maps. Tensor extension along `c` identifies with
transport of action by `c.inv`: on pure tensors the map is `r ⊗ m ↦ c.inv(r)m`, with
inverse `m ↦ 1 ⊗ m`. Balancing proves both composite identities, and restrictions commute.
The underlying abelian inverse image is exact by sitePullback_abelian_exact; the module
kernels and cokernels have those underlying abelian sheaves. Scalar transport preserves
this exactness. Addition of maps is respected by these constructions. -/
theorem proEtaleRingModuleOperations_properties :
    (proEtaleRingModulePullback f R S c).Additive ∧
    (proEtaleRingModuleDirectImage f R S c).Additive ∧
    PreservesFiniteLimits (proEtaleRingModulePullback f R S c) ∧
    PreservesFiniteColimits (proEtaleRingModulePullback f R S c) ∧
    Nonempty (proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c) := by
  sorry

/-- Additivity of the specified pullback. Source: Stacks, Modules on Sites
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance proEtaleRingModulePullback_additive :
    (proEtaleRingModulePullback f R S c).Additive :=
  (proEtaleRingModuleOperations_properties f R S c).1

/-- Additivity of direct image. Source: Stacks, Modules on Sites
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance proEtaleRingModuleDirectImage_additive :
    (proEtaleRingModuleDirectImage f R S c).Additive :=
  (proEtaleRingModuleOperations_properties f R S c).2.1

/-- Left exactness of pullback. Source: Stacks, Tag 04JC
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance proEtaleRingModulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (proEtaleRingModulePullback f R S c) :=
  (proEtaleRingModuleOperations_properties f R S c).2.2.1

/-- Right exactness of pullback. Source: Stacks, Tag 04JC
(blueprint: def-weil-pbc-proetale-operations). -/
noncomputable instance proEtaleRingModulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (proEtaleRingModulePullback f R S c) :=
  (proEtaleRingModuleOperations_properties f R S c).2.2.2.1

/-- K-injective resolutions exist in all modules over these coefficients.
Source: Stacks, Section 07A5 and Theorem 079P
(blueprint: def-weil-pbc-proetale-operations).
Proof: transport the site to `proEtaleSiteModel X`, enlarging only the Hom universe.
Apply grothendieckAbelian_and_functorial_kInjective_resolutions there. Transport back
along the inverse equivalence, which preserves acyclicity, homotopies, and injectives.
The construction supplies monomorphic quasi-isomorphisms, so gives the stated instance.
No constructibility, torsion, completeness, or boundedness condition is imposed. -/
theorem proEtaleRingModules_hasKInjectiveResolutions (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian.HasKInjectiveResolutions (proEtaleRingModules X R) := by
  sorry

attribute [instance] proEtaleRingModules_hasKInjectiveResolutions

/-- Ordinary uncompleted derived inverse image, by exact termwise descent.
Source: Stacks, Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev proEtaleRingDerivedPullback :
    DerivedCategory (proEtaleRingModules Y R) ⥤ DerivedCategory (proEtaleRingModules X S) :=
  (proEtaleRingModulePullback f R S c).mapDerivedCategory

/-- Ordinary uncompleted unbounded derived direct image via K-injectives in all modules.
Source: Stacks, Section 07A5 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable abbrev proEtaleRingDerivedDirectImage :
    DerivedCategory (proEtaleRingModules X S) ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  (proEtaleRingModuleDirectImage f R S c).rightDerivedFunctor

/-- Termwise pullback computes the derived pullback on all complexes and chain maps.
Source: Stacks, Section 0735 (blueprint: def-weil-pbc-proetale-operations). -/
noncomputable def proEtaleRingDerivedPullbackFactors :
    DerivedCategory.Q ⋙ proEtaleRingDerivedPullback f R S c ≅
      (proEtaleRingModulePullback f R S c).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (proEtaleRingModulePullback f R S c).mapDerivedCategoryFactors

/-- The exact pullback takes any K-flat resolution to a quasi-isomorphism.
Source: Stacks, Tag 06YS and Section 0735 (blueprint: def-weil-pbc-proetale-operations).
Proof: a K-flat resolution is a quasi-isomorphism. Exactness preserves cohomology and hence
quasi-isomorphisms. The factorization isomorphism identifies the resulting representative
with derived pullback, so no functorial K-flat resolution needs to be chosen. -/
theorem proEtaleRingDerivedPullback_kFlat
    {P K : CochainComplex (proEtaleRingModules Y R) ℤ}
    (a : P ⟶ K) (ha : CochainComplex.IsKFlatResolution a) :
    QuasiIso ((proEtaleRingModulePullback f R S c).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.map a) := by
  sorry

/-- Direct image is computed on every K-injective representative, naturally in that
representative. Source: Stacks, Section 07A5
(blueprint: def-weil-pbc-proetale-operations).
Proof: the K-injective right derivability structure gives an invertible component of the
right-derived unit at each K-injective complex. Its naturality gives the formula for maps.
A quasi-isomorphism between K-injectives is a homotopy equivalence by
CochainComplex.IsKInjective.quasiIso_iff; additive termwise direct image preserves its
homotopy inverse. Thus the resolution calculation descends through localization. -/
theorem proEtaleRingDerivedDirectImage_kInjective
    (I : CochainComplex (proEtaleRingModules X S) ℤ) [I.IsKInjective] :
    IsIso ((proEtaleRingModuleDirectImage f R S c).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)) := by
  sorry

/-- The ordinary derived adjunction on the full unbounded derived categories.
Source: Stacks, Lemma 0DVC and Section 0735
(blueprint: def-weil-pbc-proetale-operations).
Proof: exact pullback has an everywhere defined total left derived functor by
exactFunctor_derivedFunctor. Direct image has an everywhere defined right derived functor
by K-injective resolutions. Apply preDerivedAdjunctionGeneral to the underived module
adjunction. Its fraction normalization gives the canonical Hom bijection and its
naturality in both variables, hence the displayed adjunction. The left functor is
triangulated by exact descent, and the right one by right-derived triangulatedness. -/
theorem proEtaleRingDerivedOperations_adjunction :
    Nonempty (proEtaleRingDerivedPullback f R S c ⊣ proEtaleRingDerivedDirectImage f R S c) := by
  sorry

end AlgebraicGeometry.Scheme
