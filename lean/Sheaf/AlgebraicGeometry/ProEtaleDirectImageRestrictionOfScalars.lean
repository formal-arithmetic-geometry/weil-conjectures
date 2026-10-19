/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
/-!
# Derived pro-etale direct image and restriction of scalars

Source: blueprint `def-weil-derived-direct-image`, order 1468, coefficient tower maps;
Stacks Project, Tags 0D6E, 0D6J and 015F
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction along the induced map of constant ring sheaves, using Mathlib's
unchanged-underlying-abelian-sheaf restriction functor. Its exactness is the instance
`proEtaleRingRestrictScalars_preservesFiniteLimits/Colimits`; its derived functor is
therefore the termwise `mapDerivedCategory`.
Source: Stacks Tags 03DA and 015F
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable abbrev proEtaleCoefficientRestrictScalars (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleRingModules X (proEtaleConstantRing X B) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) :=
  proEtaleRingRestrictScalars
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))

/-- Exact restriction preserves finite limits. Source: Stacks Tag 015F
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable instance proEtaleCoefficientRestrictScalars_preservesFiniteLimits
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (proEtaleCoefficientRestrictScalars X φ) :=
  (proEtaleRingRestrictScalars_properties
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))).1

/-- Exact restriction preserves finite colimits. Source: Stacks Tag 015F
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable instance proEtaleCoefficientRestrictScalars_preservesFiniteColimits
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteColimits (proEtaleCoefficientRestrictScalars X φ) :=
  (proEtaleRingRestrictScalars_properties
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))).2.1

/-- The underived coefficient square has the uniquely normalized identity-on-sections
comparison. Source: blueprint order 1468; Stacks Tag 0D6E
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
Proof: the two constant-ring structure maps send each a to the constant section φ(a).
Their equality follows by the universal property of sheafification. Both functors have
sections N(X ×_Y W), the same restrictions and the same restricted scalar action.
Identity on these sections is linear, natural, invertible and uniquely determines the
comparison because module sheaf morphisms are determined by their section maps. -/
theorem proEtaleCoefficientDirectImageComparison_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃! e : proEtaleConstantModuleDirectImage f B ⋙ proEtaleCoefficientRestrictScalars Y φ ≅
        proEtaleCoefficientRestrictScalars X φ ⋙ proEtaleConstantModuleDirectImage f A,
      ∀ (N : proEtaleRingModules X (proEtaleConstantRing X B)) (W : Y.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W n = n := by
  sorry

/-- The actual identity-on-sections comparison, selected by its unique characterization.
Source: blueprint order 1468; Stacks Tag 0D6E
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable def proEtaleCoefficientDirectImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    proEtaleConstantModuleDirectImage f B ⋙ proEtaleCoefficientRestrictScalars Y φ ≅
      proEtaleCoefficientRestrictScalars X φ ⋙ proEtaleConstantModuleDirectImage f A :=
  Classical.choose (proEtaleCoefficientDirectImageComparison_existsUnique f φ)

/-- Derived direct image commutes with restriction of finite commutative coefficients.
The displayed equality says that the comparison is the inverse of f_*(j), after the
canonical termwise-localization and K-injective resolution identifications. In particular
restriction of scalars is not assumed to preserve K-injectivity.
Source: blueprint `def-weil-derived-direct-image`, order 1468; Stacks Tags 0D6E, 0D6J,
015F (blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
Proof:
1. Restriction leaves underlying abelian sheaves, kernels and sheafified cokernels
unchanged, so is exact and additive. Exact descent gives its triangulated termwise
functor and identifies it with the derived identity-topos coefficient direct image
(lem-weil-pbc-exact-functor-derived-factorization and
lem-weil-pbc-exact-functor-derived-functor).
2. The two ringed-topos composites have the same constant-section structure map and
hence the identity-on-sections comparison defined above. Canonical direct images use
these structure maps directly; no extra chosen coefficient isomorphism is required.
3. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to both
factorizations. Identify derived restrictions with their exact termwise descent and
compose the two comparison isomorphisms in the displayed direction.
4. For K-injective J and a K-injective resolution j of its restriction, the normalized
composition theorem says f_*(j) is a quasi-isomorphism. Resolve f_*J over B_Y using
prop-pur-kinjective-resolutions-exist; exact restriction identifies that second
comparison with the identity. Thus the result is the inverse of f_*(j), as expressed
by the equation below, independently of resolutions and naturally in every derived
morphism. No flatness of B over A or boundedness or property of f is required. -/
theorem proEtaleDerivedDirectImage_restrictScalars
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃ d : (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory ⋙
        proEtaleConstantDerivedDirectImage f A ≅
      proEtaleConstantDerivedDirectImage f B ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory,
      ∀ (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X B)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
        [I.IsKInjective]
        (j : ((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso j],
        QuasiIso (((proEtaleConstantModuleDirectImage f A).mapHomologicalComplex (.up ℤ)).map j) ∧
        d.hom.app (DerivedCategory.Q.obj J) ≫
            (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
              ((proEtaleConstantModuleDirectImage f B).rightDerivedFunctorObjQIso J).hom ≫
            (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantModuleDirectImage f B).mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
                (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map
              (((proEtaleConstantModuleDirectImage f A).mapHomologicalComplex (.up ℤ)).map j) =
          (proEtaleConstantDerivedDirectImage f A).map
              ((proEtaleCoefficientRestrictScalars X φ).mapDerivedCategoryFactors.hom.app J) ≫
            (proEtaleConstantDerivedDirectImage f A).map (DerivedCategory.Q.map j) ≫
            ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso I).hom := by
  sorry

end AlgebraicGeometry.Scheme
