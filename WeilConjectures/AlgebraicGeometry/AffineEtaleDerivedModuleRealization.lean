/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.KInjectiveTotalDerived

/-!
# Affine small étale realization of the unbounded module derived category

Source: Stacks Project, spaces-perfect.tex, Tags 071Q and 08H8; perfect.tex,
Tag 06Z0; schemes.tex, Tags 01HV and 01I9; sites-cohomology.tex, Section 07A5
(blueprint: lem-sfb-affine-etale-derived-module-realization).
-/

@[expose] public section

set_option autoImplicit false

universe u wA wE

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The associated étale module functor is Zariski tilde followed by the canonical
ringed-site extension. The context contains only continuity and adjoint-existence proofs.
On an affine étale Spec B over Spec A its sections are B tensor_A M, with the usual
base-change restriction maps.
Source: Stacks, Descent 03DU and 03FH; Schemes 01HV and 01I9
(blueprint: lem-sfb-affine-etale-derived-module-realization). -/
def affineEtaleAssociatedFunctor (A : Type u) [CommRing A]
    (c : ZariskiEtaleModuleContext (Spec (.of A))) :
    ModuleCat.{u} A ⥤ SmallEtaleModules (Spec (.of A)) :=
  tilde.functor (.of A) ⋙ c.extension

/-- Global sections on the affine small étale ringed site, regarded as A-modules.
Restriction to Zariski opens followed by ordinary global sections evaluates at the
terminal étale object. The scalar identification is the usual Gamma(Spec A) = A.
Source: Stacks, spaces-perfect.tex 071Q; perfect.tex 06Z0
(blueprint: lem-sfb-affine-etale-derived-module-realization). -/
def affineEtaleGlobalSections (A : Type u) [CommRing A]
    (c : ZariskiEtaleModuleContext (Spec (.of A))) :
    SmallEtaleModules (Spec (.of A)) ⥤ ModuleCat.{u} A :=
  c.restriction ⋙ moduleSpecΓFunctor (R := .of A)

/-- The full-subcategory predicate of having quasi-coherent cohomology in every degree
on the small étale ringed site. Quasi-coherence is Mathlib's local-presentation predicate.
Source: Stacks, spaces-perfect.tex, preceding Tag 071Q
(blueprint: lem-sfb-affine-etale-derived-module-realization). -/
def smallEtaleDerivedQCohProperty (X : Scheme.{u})
    [HasDerivedCategory.{wE} (SmallEtaleModules X)] :
    ObjectProperty (DerivedCategory (SmallEtaleModules X)) :=
  fun K ↦ ∀ i : ℤ,
    ((DerivedCategory.homologyFunctor (SmallEtaleModules X) i).obj K).IsQuasicoherent

/-- Affine associated étale modules are exact and faithful. Applied termwise they give
an equivalence from the unbounded module derived category to the full subcategory of
étale complexes with quasi-coherent cohomology. Its inverse is derived global sections,
characterized by its right-derived universal property and K-injective computation.
The last two natural isomorphisms state compatibility with every cohomology functor
and ordinary global sections.

Source: Stacks, spaces-perfect.tex 071Q and 08H8, perfect.tex 06Z0,
schemes.tex 01HV and 01I9, sites-cohomology.tex Section 07A5
(blueprint: lem-sfb-affine-etale-derived-module-realization).

Proof:
1. Identify tilde followed by epsilon pullback with the associated étale module sheaf,
   using lem-weil-pbc-spec-module-tilde-sections,
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence,
   lem-weil-pbc-module-pullback-affine-sections and
   lem-weil-pbc-affine-tilde-gamma-adjunction. On Spec B the identification is
   b tensor m mapped to b times the pullback of the canonical section of m.
   Restriction sends b tensor m to g-sharp(b) tensor m. At Spec A this is M,
   naturally in module maps, and evaluation therefore proves faithfulness.
2. Tilde preserves finite limits by lem-sc-tilde-preserves-finite-limits and colimits
   by its adjunction. Epsilon pullback is exact by
   lem-sfb-scheme-derived-etale-qcoh-comparison. Their composite is exact in the
   ambient module-sheaf category.
3. Kernel, image and quotient comparisons give the natural cohomology isomorphisms.
   lem-weil-pbc-exact-functor-derived-factorization descends the termwise functor
   through the quasi-isomorphism localization of def-weil-abstract-derived-category.
4. Compose lem-pc-affine-qcoh-derived-equivalence with
   lem-sfb-scheme-derived-etale-qcoh-comparison. Both are unbounded equivalences;
   the latter identifies derived étale and Zariski global sections. Their composite
   is termwise associated étale sheaf, and its inverse is derived étale sections.
5. prop-pur-kinjective-resolutions-exist provides K-injective replacements on this
   ringed site. Apply lem-weil-pbc-kinjective-total-derived to termwise sections on
   the homotopy category followed by localization. Sections is additive and preserves
   mapping cones and shifts. The resulting universal functor is computed on each
   K-injective complex by termwise sections. For K to I a K-injective resolution,
   invert Q(K to I) and the comparison on I to obtain R-Gamma(K) = Q(Gamma(I)).
   Uniqueness of right derived functors identifies it with the inverse in step 4. -/
theorem exists_affineEtaleDerivedModuleRealization (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wE} (SmallEtaleModules (Spec (.of A)))] :
    ∃ c : ZariskiEtaleModuleContext (Spec (.of A)),
    ∃ (_ha : (affineEtaleAssociatedFunctor A c).Additive)
      (_hg : (affineEtaleGlobalSections A c).Additive),
      PreservesFiniteLimits (affineEtaleAssociatedFunctor A c) ∧
      PreservesFiniteColimits (affineEtaleAssociatedFunctor A c) ∧
      (affineEtaleAssociatedFunctor A c).Faithful ∧
      ∃ e : DerivedCategory (ModuleCat.{u} A) ≌
        (smallEtaleDerivedQCohProperty (Spec (.of A))).FullSubcategory,
        Nonempty (DerivedCategory.Q ⋙ e.functor ⋙
          (smallEtaleDerivedQCohProperty (Spec (.of A))).ι ≅
          (affineEtaleAssociatedFunctor A c).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q) ∧
        (∃ (RG : DerivedCategory (SmallEtaleModules (Spec (.of A))) ⥤
              DerivedCategory (ModuleCat.{u} A))
          (η : (affineEtaleGlobalSections A c).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG),
          (∀ G : DerivedCategory (SmallEtaleModules (Spec (.of A))) ⥤
              DerivedCategory (ModuleCat.{u} A),
            Function.Bijective
              (fun β : RG ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Qh β)) ∧
          (∀ I : CochainComplex (SmallEtaleModules (Spec (.of A))) ℤ,
            I.IsKInjective →
              IsIso (η.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ∧
          (∀ K : CochainComplex (SmallEtaleModules (Spec (.of A))) ℤ,
            ∃ (I : CochainComplex (SmallEtaleModules (Spec (.of A))) ℤ) (f : K ⟶ I),
              I.IsKInjective ∧ QuasiIso f ∧
              Nonempty (RG.obj (DerivedCategory.Q.obj K) ≅
                DerivedCategory.Q.obj
                  (((affineEtaleGlobalSections A c).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I))) ∧
          Nonempty (e.inverse ≅ (smallEtaleDerivedQCohProperty (Spec (.of A))).ι ⋙ RG)) ∧
        (∀ i : ℤ, Nonempty (e.functor ⋙
          (smallEtaleDerivedQCohProperty (Spec (.of A))).ι ⋙
            DerivedCategory.homologyFunctor (SmallEtaleModules (Spec (.of A))) i ≅
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ⋙
            affineEtaleAssociatedFunctor A c)) ∧
        Nonempty (affineEtaleAssociatedFunctor A c ⋙ affineEtaleGlobalSections A c ≅
          𝟭 (ModuleCat.{u} A)) := by
  sorry

end

end AlgebraicGeometry.Scheme.Modules
