/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-! # Bounded-below descent from a weak Serre heart

Source: Stacks Project, Cohomology on Sites, Tag 0D7U, lemma-equivalence-bounded
(blueprint: lem-sfb-ringed-bounded-below-descent-criterion).

The ordinary pullback is specified by its adjunction to the induced module direct
image. The total derived direct image is specified by its universal comparison and
its K-injective computation. The displayed unit equation specifies the canonical
derived adjunction. Both localization morphism universes are independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wO wR

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Exact pullback and acyclic descent on a weak Serre heart give bounded-below descent.

Source: Stacks Project, Cohomology on Sites, Tag 0D7U, lemma-equivalence-bounded
(blueprint: lem-sfb-ringed-bounded-below-descent-criterion).

Proof plan:
1. Exact-functor cohomology comparison (lem-weil-pbc-exact-functor-complex-cohomology)
   shows that pullback preserves the lower bound and the cohomology condition.
   Apply lem-sfb-ringed-unit-from-cohomology to the assumed units on the cohomology
   sheaves; the canonical unit is invertible on every bounded-below B-object.
2. For F in A, the heart equivalence gives F isomorphic to pullback of G in B.
   The assumed unit gives Rf_*F isomorphic to G[0]. The adjunction triangle identity
   makes the counit on pullback of G invertible; naturality transports this to F.
3. Small ringed sites have Grothendieck module categories and K-injective resolutions
   (prop-pur-kinjective-resolutions-exist). The module adjunction
   (lem-weil-pbc-ringed-topoi-module-adjunction) and preservation of limits by right
   adjoints (lem-weil-pbc-right-adjoint-preserves-limits) make direct image left exact.
4. For K with cohomology zero below a, the standard t-structure
   (def-sbc-standard-tstructure-derived-category) gives a representative zero below a.
   The convergent truncation spectral sequence (thm-sp-truncation-e2) has
   E2(p,q) = H^p(Rf_*H^qK). Step 2 kills every column except p=0. Its finite,
   exhaustive, separated filtration gives H^n(Rf_*K) isomorphic to
   H^0(Rf_*H^nK), in B and zero for n<a. Thus Rf_* preserves the specified part.
5. Apply lem-sfb-ringed-counit-from-cohomology, using step 2 on every H^qK, to
   make the canonical counit invertible on every bounded-below A-object.
6. Restrict the two functors, their canonical unit and counit to the full
   subcategories. The same triangle identities give the asserted equivalence,
   whose functor and inverse are precisely those restrictions. No local
   cohomological bound is used. -/
theorem RingedToposMorphism.boundedBelowDescent
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (O : Sheaf J CommRingCat.{u}) (R : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wO}
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))]
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (F : ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ f.modules)
    (Rf : DerivedCategory.{wO}
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) ⥤
      DerivedCategory.{wR}
        (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (β : f.modules.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q.{wR} (C := ringedSiteModules.{u, u, u, u}
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
      DerivedCategory.Q.{wO} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso
        (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))
        (.up ℤ)))
    (hKI : ∀ I : CochainComplex
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) ℤ,
      I.IsKInjective → IsIso (β.app I))
    (d : F.mapDerivedCategory.{wR, wO} ⊣ Rf)
    (hd : ∀ P : CochainComplex
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      d.unit.app (DerivedCategory.Q.{wR}.obj P) ≫
          Rf.map (F.mapDerivedCategoryFactors.{wR, wO}.hom.app P) =
        DerivedCategory.Q.{wR}.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          β.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (A : ObjectProperty
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)))
    (B : ObjectProperty
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    [hAContainsZero : A.ContainsZero]
    [hAIsClosedUnderIsomorphisms : A.IsClosedUnderIsomorphisms]
    [hAIsClosedUnderKernels : A.IsClosedUnderKernels]
    [hAIsClosedUnderCokernels : A.IsClosedUnderCokernels]
    [hAIsClosedUnderExtensions : A.IsClosedUnderExtensions]
    [hBContainsZero : B.ContainsZero]
    [hBIsClosedUnderIsomorphisms : B.IsClosedUnderIsomorphisms]
    [hBIsClosedUnderKernels : B.IsClosedUnderKernels]
    [hBIsClosedUnderCokernels : B.IsClosedUnderCokernels]
    [hBIsClosedUnderExtensions : B.IsClosedUnderExtensions]
    (eHeart : B.FullSubcategory ≌ A.FullSubcategory)
    (hHeart : eHeart.functor ⋙ A.ι ≅ B.ι ⋙ F)
    (hunit : ∀ G :
      ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R), B G →
      IsIso (d.unit.app ((DerivedCategory.singleFunctor.{wR}
        (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) 0).obj G))) :
    (∃ e : (DerivedCategory.homologyProperty.{wR} B ⊓
          (DerivedCategory.TStructure.t.{wR} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).plus).FullSubcategory ≌
        (DerivedCategory.homologyProperty.{wO} A ⊓
          (DerivedCategory.TStructure.t.{wO} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))).plus).FullSubcategory,
      e.functor ⋙ (DerivedCategory.homologyProperty.{wO} A ⊓
          (DerivedCategory.TStructure.t.{wO} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))).plus).ι =
        (DerivedCategory.homologyProperty.{wR} B ⊓
          (DerivedCategory.TStructure.t.{wR} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).plus).ι ⋙
          F.mapDerivedCategory.{wR, wO} ∧
      e.inverse ⋙ (DerivedCategory.homologyProperty.{wR} B ⊓
          (DerivedCategory.TStructure.t.{wR} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).plus).ι =
        (DerivedCategory.homologyProperty.{wO} A ⊓
          (DerivedCategory.TStructure.t.{wO} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))).plus).ι ⋙ Rf) ∧
    (∀ L : DerivedCategory.{wR}
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
      (DerivedCategory.homologyProperty.{wR} B ⊓
          (DerivedCategory.TStructure.t.{wR} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).plus) L →
        IsIso (d.unit.app L)) ∧
    (∀ M : DerivedCategory.{wO}
      (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)),
      (DerivedCategory.homologyProperty.{wO} A ⊓
          (DerivedCategory.TStructure.t.{wO} (C := ringedSiteModules.{u, u, u, u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))).plus) M →
        IsIso (d.counit.app M)) := by
  sorry
end CategoryTheory
