/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.PartiallyDefinedModuleAdjoint
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Exact module lower shriek and its underlying abelian sheaf

Source: Stacks Project, Modules on Sites, Tags 0797, 0798 and 04BH
(blueprint: lem-sfb-local-slice-module-shriek-exact).
-/

@[expose] public section

set_option autoImplicit false

universe c d vc vd r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Module precomposition has an additive exact left adjoint, and forgetting its ring
 action agrees naturally with abelian lower shriek.

Source: Stacks Project, Modules on Sites, Tags 0797, 0798 and 04BH
(blueprint: lem-sfb-local-slice-module-shriek-exact).

The covering presieves are `J` and `K`. The slice functor is literally `Over.post F`;
`hsliceCover` says that it identifies the actual localized covering families.
The source ring is the target ring precomposed with `F`, with identity structural map.
Consequently the restricted rings agree sectionwise on every slice. The continuity
instance is the sheaf-theoretic consequence of `hcover` and pullback preservation,
explicit only to type the canonical precomposition functors. No terminal object is assumed.
The common coefficient universe contains both sites and an arbitrary further level `r`.

Proof:
1. Apply lem-trf-ringed-site-restriction-generator-data: module precomposition is
   additive, and sums of the free module sheaves on objects epimorphically generate.
   Its natural evaluation bijections corepresent Hom from each such sum by the
   corresponding sum on the target. Isomorphic sums give the same corepresentation
   by precomposing Hom with the isomorphism. The module categories are abelian by
   def-weil-sheaf-of-modules-category. Apply lem-trf-partially-defined-module-adjoint
   to obtain the module left adjoint L (0797).
2. By lem-weil-pbc-left-adjoint-preserves-colimits, L preserves finite colimits;
   lem-sfb-preserving-colimits-additive then gives additivity. Fix its unit.
3. By lem-weil-pbc-site-continuous-pushforward-sheaf and
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction, abelian precomposition
   has a left adjoint A, globally and on each slice. Continuity and cocontinuity
   restrict to slices because their covers are underlying covers
   (def-pur-localized-ringed-site). The restricted source ring is precomposition
   of the restricted target ring, sectionwise.
4. The slice site equivalence gives fully faithful abelian precomposition on each
   slice, using precomposition with a cover-preserving quasi-inverse. Its counit
   at the restricted target ring is invertible: fullness lifts the unit to an
   inverse, and faithfulness and the two adjunction identities give both inverse
   equations. This uses no terminal object on either original site.
5. Apply lem-sfb-module-shriek-forgetful-counit-criterion (0798) with these counits.
   Its comparison from A after forgetting to forgetting after L is invertible.
   Inverting it gives the displayed natural isomorphism. Uniqueness of left
   adjoints transports it to any abelian left adjoint A in the conclusion.
6. By lem-sfb-abelian-lower-shriek-exact (04BH), A is exact under the stated
   pullback and equalizer hypotheses. By lem-weil-pbc-module-sheaves-colimits-forgetful,
   forgetting is faithful and preserves kernels and cokernels. The comparison
   therefore identifies the underlying image of every short exact module sequence
   with its exact image under A. Faithful forgetting reflects zero objects and
   exactness, so L is exact, equivalently it preserves finite limits and colimits.
-/
theorem exists_exact_moduleLeftAdjoint_forget_iso_of_localSliceEquivalences
    {C : Type c} [Category.{vc} C] {D : Type d} [Category.{vd} D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    [HasPullbacks C] [HasEqualizers C]
    (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape WalkingParallelPair F]
    (hcover : ∀ (X : C) (P : Presieve X), P ∈ J X → P.map F ∈ K (F.obj X))
    [F.IsContinuous J.toGrothendieck K.toGrothendieck]
    [F.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    (hslice : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (hsliceCover : ∀ (X : C) (Y : Over X) (P : Presieve Y),
      P.map (Over.forget X) ∈ J Y.left ↔
        (P.map (Over.post F)).map (Over.forget (F.obj X)) ∈ K (F.obj Y.left))
    (R : Sheaf K.toGrothendieck CommRingCat.{max c d vc vd r}) :
    ∃ L : ringedSiteModules.{max c d vc vd r}
        ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
          J.toGrothendieck K.toGrothendieck).obj
          ((sheafCompose K.toGrothendieck
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)) ⥤
        ringedSiteModules.{max c d vc vd r}
          ((sheafCompose K.toGrothendieck
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R),
      L.Additive ∧
      Nonempty (L ⊣ SheafOfModules.pushforward.{max c d vc vd r} (F := F)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
          J.toGrothendieck K.toGrothendieck).obj
          ((sheafCompose K.toGrothendieck
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)))) ∧
      PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧
      ∀ A : Sheaf J.toGrothendieck AddCommGrpCat.{max c d vc vd r} ⥤
          Sheaf K.toGrothendieck AddCommGrpCat.{max c d vc vd r},
        (A ⊣ F.sheafPushforwardContinuous AddCommGrpCat.{max c d vc vd r}
          J.toGrothendieck K.toGrothendieck) →
        Nonempty (L ⋙ SheafOfModules.toSheaf.{max c d vc vd r}
          ((sheafCompose K.toGrothendieck
            (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R) ≅
          SheafOfModules.toSheaf.{max c d vc vd r}
            ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
              J.toGrothendieck K.toGrothendieck).obj
              ((sheafCompose K.toGrothendieck
                (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)) ⋙
            A) := by
  sorry

end CategoryTheory
