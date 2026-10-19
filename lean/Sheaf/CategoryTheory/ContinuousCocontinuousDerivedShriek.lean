/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Sheaf.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.CategoryTheory.LeftDerivedExactWhenDefined
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-!
# Unbounded derived lower shriek for continuous cocontinuous functors

Source: Stacks Project, Cohomology on Sites, Tag 07AC; Modules on Sites, Tag 0797;
Derived Categories, Tags 05S8, 05S9, 05SE, 09T5 and 0DVC
(blueprint: lem-trf-continuous-cocontinuous-derived-shriek).
-/

@[expose] public noncomputable section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- The ring `g⁻¹ O` is restriction along the continuous site functor.
Source: Stacks Project, Tag 0797
(blueprint: lem-trf-continuous-cocontinuous-derived-shriek). -/
abbrev lowerShriekSourceRing (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K CommRingCat.{u}) :=
  (f.sheafPushforwardContinuous RingCat.{u} J K).obj
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Module inverse image for the identity structural ring map is literal restriction.
Source: Stacks Project, Tag 0797
(blueprint: lem-trf-continuous-cocontinuous-derived-shriek). -/
abbrev lowerShriekInverseImage (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K CommRingCat.{u}) :=
  SheafOfModules.pushforward.{u} (𝟙 (lowerShriekSourceRing J K f R))

/-- The complete existence conclusion, retaining its canonical comparison and adjunction.
Source: Stacks Project, Tags 07AC, 0797, 05S9, 05SE, 09T5 and 0DVC
(blueprint: lem-trf-continuous-cocontinuous-derived-shriek).

The continuity witness is produced from the covering hypotheses, not assumed in addition
to them. The chosen derived-category hom universes are the larger universe of the size
convention. `definedAt` is precisely the pro-diagram criterion of Definition 05S9, at the
value supplied by the derived functor. `normalization` uses the standard factorization
isomorphism only to identify termwise restriction with its descended functor. -/
structure ContinuousCocontinuousDerivedShriekData
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) (R : Sheaf K CommRingCat.{u}) where
  /-- Continuity on the generated topologies. -/
  [continuous : f.IsContinuous J K]
  /-- Additivity of restriction. -/
  [inverseAdditive : (lowerShriekInverseImage J K f R).Additive]
  /-- Left exactness of restriction. -/
  [inverseLeftExact : PreservesFiniteLimits (lowerShriekInverseImage J K f R)]
  /-- Right exactness of restriction, using cocontinuity. -/
  [inverseRightExact : PreservesFiniteColimits (lowerShriekInverseImage J K f R)]
  /-- The ordinary module lower shriek. -/
  shriek : ringedSiteModules.{u} (lowerShriekSourceRing J K f R) ⥤
    ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
  /-- Additivity of lower shriek. -/
  [shriekAdditive : shriek.Additive]
  /-- Its defining ordinary adjunction. -/
  adjunction : shriek ⊣ lowerShriekInverseImage J K f R
  /-- Derived categories in the larger universe. -/
  [derivedSource : HasDerivedCategory.{u + 1}
    (ringedSiteModules.{u} (lowerShriekSourceRing J K f R))]
  /-- Derived categories in the larger universe. -/
  [derivedTarget : HasDerivedCategory.{u + 1}
    (ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))]
  /-- The total unbounded left derived functor. -/
  derivedShriek : DerivedCategory (ringedSiteModules.{u} (lowerShriekSourceRing J K f R)) ⥤
    DerivedCategory
      (ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
  /-- Canonical derived comparison on complexes. -/
  comparison : DerivedCategory.Q ⋙ derivedShriek ⟶
    shriek.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  /-- The total-left-derived universal property. -/
  universal : derivedShriek.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  /-- Defined at every homotopy-category object, with no boundedness restriction. -/
  definedAt : ∀ X : HomotopyCategory
      (ringedSiteModules.{u} (lowerShriekSourceRing J K f R)) (ComplexShape.up ℤ),
    IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ⊤ X ⋙
        Over.forget X ⋙ shriek.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (derivedShriek.obj (DerivedCategory.Qh.obj X))
  /-- Shift compatibility of the derived functor. -/
  [commShift : derivedShriek.CommShift ℤ]
  /-- Preservation of distinguished triangles. -/
  triangulated : derivedShriek.IsTriangulated
  /-- The derived adjunction with termwise inverse image. -/
  derivedAdjunction : derivedShriek ⊣ (lowerShriekInverseImage J K f R).mapDerivedCategory
  /-- The derived Hom bijection is the canonical one from the ordinary adjunction. -/
  normalization : ∀
    (M : CochainComplex (ringedSiteModules.{u} (lowerShriekSourceRing J K f R)) ℤ)
    (N : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a : (shriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N),
    derivedAdjunction.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N)
        (comparison.app M ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
          ((adjunction.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv M N a) ≫
        (lowerShriekInverseImage J K f R).mapDerivedCategoryFactors.inv.app N

/-- Source: Stacks Project, Tag 07AC, with Tag 0797 for the ordinary adjunction,
Tags 05S8--05S9 for definedness, Tag 05SE for triangulatedness, and Tags 09T5 and
0DVC for the normalized derived adjunction
(blueprint: lem-trf-continuous-cocontinuous-derived-shriek).

Proof:
1. Restriction preserves kernels sectionwise. Epimorphisms of module sheaves are locally
surjective by lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective. Refine local lifts
using cocontinuity to prove exactness. The identity ring map introduces no scalar extension.
2. Sheafify the free Yoneda modules (lem-weil-pbc-free-yoneda-presheaf-module and
def-weil-presheaf-modules-sheafification). Maps from E_U to M are M(U). Their coproduct
over all pairs (U,s) surjects onto M. Such sums include zero and are closed under finite sums.
3. The evaluation bijections identify Hom(E_U,g⁻¹N) with N(fU), represented by E_fU.
Extend from sums by lem-trf-partially-defined-module-adjoint to obtain g_! ⊣ g⁻¹.
The Hom bijections give additivity; left adjoints preserve all colimits, so g_! is right
exact and preserves sequential colimits (lem-weil-pbc-left-adjoint-preserves-colimits).
4. For an injective I, lem-trf-module-pullback-injective-section-acyclic gives
Ext^p(E_U,g⁻¹I)=0 for p>0, with these actual module coefficients.
5. By lem-trf-acyclic-coproduct-ext-orthogonal-hom, Hom(P,g⁻¹I) is acyclic for any
bounded-above acyclic complex of sums of E_U. Adjunction identifies this with Hom(g_!P,I).
Injectives detect acyclicity: a nonzero cohomology embeds in an injective, extends from
cycles modulo boundaries to the ambient term modulo boundaries, and gives a cocycle
which cannot be a boundary. Enough injectives follow from the Grothendieck property.
6. Both module categories are Grothendieck abelian (prop-pur-kinjective-resolutions-exist).
Sequential colimits are exact. Apply lem-trf-unbounded-left-derived-criterion with the
class of sums from step 2, using steps 3 and 5. Essential constancy holds everywhere;
new-everywhere-defined-derived-functors assembles the derived functor and its comparison.
7. Additivity preserves cone matrices and homotopies. Thus QK(g_!) is triangulated.
Use lem-pur-homotopy-category-triangulated and lem-pur-quasi-isos-saturated-triangulated
to obtain Situation 05S8, then lem-pur-left-derived-exact-when-defined gives triangulatedness.
8. Exact restriction descends termwise by lem-weil-pbc-exact-functor-derived-factorization.
Its right-derived denominator diagram is essentially constant with this value, since
each denominator is sent to an isomorphism. Apply lem-pc-pre-derived-adjoint-functors-general
with this cocone and the left-derived cone from step 6. Evaluating its canonical formula
at identity denominators gives precisely normalization, with the displayed factorization
isomorphism identifying termwise restriction with its descended functor. -/
theorem continuousCocontinuous_exists_derivedShriek
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (R : Sheaf K.toGrothendieck CommRingCat.{u}) :
    Nonempty (ContinuousCocontinuousDerivedShriekData J.toGrothendieck K.toGrothendieck f R) := by
  sorry

end CategoryTheory
