/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Exact module lower shriek under equivalences on slices

Source: Stacks Project, Modules on Sites, Tags 0797, 0798 and 04BH
(blueprint: lem-sfb-ringed-site-slice-equivalence-exact-shriek).
-/

@[expose] public section

universe c d vc vd r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Precomposition of module sheaves has an additive exact left adjoint under equivalences
of the induced slice sites.

Source: Stacks Project, Modules on Sites, Tags 0797, 0798 and 04BH
(blueprint: lem-sfb-ringed-site-slice-equivalence-exact-shriek).

The actual covering presieves are `J` and `K`. On a slice a family covers precisely when its
image family `P.map (Over.forget _)` (not the sieve it generates) covers. The continuity
instance is the sheaf-theoretic consequence of `hcover` and preservation of pullbacks,
included to type Mathlib's canonical precomposition. It does not impose an additional
mathematical condition. The ring on the source is exactly precomposition of the target ring,
and the structural ring map is its identity. Thus its restrictions on every slice agree
sectionwise with the restricted ring on the target slice, including their restriction
homomorphisms.

Proof:
1. Use the sites, functor and ring in lem-sfb-local-slice-module-shriek-exact. The site
   sizes, continuity and cocontinuity, pullbacks and equalizers and their preservation
   are its hypotheses. By def-pur-localized-ringed-site (Stacks 04IX), the restricted
   rings evaluate at an arrow with domain d as R(d). Their pullbacks along `Over.post F`
   are therefore exactly the restrictions of R composed with F, with identity ring map.
   The slice equivalence and the covering iff below are precisely equivalence of the
   induced slice sites. No terminal object is required.
2. Apply lem-sfb-local-slice-module-shriek-exact. Its restriction is the displayed
   `SheafOfModules.pushforward` with identity structural map. Its additive exact left
   adjoint supplies L, its natural Hom bijections give the adjunction, and exactness
   gives preservation of every short exact short complex. The extra comparison with
   abelian lower shriek in that lemma is unused. Equivalently, 0797 supplies the module
   adjoint, 0798 identifies its underlying abelian functor under the slice hypotheses,
   and 04BH gives exactness.
-/
theorem exists_exact_moduleLeftAdjoint_of_sliceEquivalences
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
      ∃ hL : L.Additive,
        Nonempty (L ⊣ SheafOfModules.pushforward.{max c d vc vd r} (F := F)
          (𝟙 ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
            J.toGrothendieck K.toGrothendieck).obj
            ((sheafCompose K.toGrothendieck
              (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R)))) ∧
        ∀ S : ShortComplex (ringedSiteModules.{max c d vc vd r}
          ((F.sheafPushforwardContinuous RingCat.{max c d vc vd r}
            J.toGrothendieck K.toGrothendieck).obj
            ((sheafCompose K.toGrothendieck
              (forget₂ CommRingCat.{max c d vc vd r} RingCat.{max c d vc vd r})).obj R))),
          S.ShortExact →
            (@ShortComplex.map _ _ _ _ _ _ S L
              (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ L hL)).ShortExact := by
  sorry

end CategoryTheory
