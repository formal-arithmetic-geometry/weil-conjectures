/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteSubterminalModuleCounitMono
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteBinaryCoverModulePushout
import Mathlib.CategoryTheory.Abelian.CommSq

/-! # The extension-by-zero sequence for a binary cover on a ringed site

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; the Gluing paragraph of
literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md
(blueprint: lem-dla1-site-open-cover-extension-sequence).

The nested maps are the recorded adjunction transposes. By uniqueness of left adjoints,
these are exactly extension of the slice counits under the relocalization comparison.
- middle arrow: the difference of the two nested maps;
- last arrow: the sum of the two extension/restriction counits.
-/

@[expose] public noncomputable section

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

open SubterminalLocal

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

/-- The map from the overlap extension into the biproduct, with the negative second component.
Source: Stacks 03DI and the blueprint's open-cover triangle
(blueprint: lem-dla1-site-open-cover-extension-sequence).
The existing `nested` is the transpose of restriction of the extension unit, equivalently
extension of the slice counit through the canonical composite-left-adjoint isomorphism. -/
def siteOpenCoverExtensionFirst {U V W : C} (aU : W ⟶ U) (aV : W ⟶ V)
    (F : Modules.{c, v, r} R) :
    (jbang.{c, v, r} R W).obj ((jstar.{c, v, r} R W).obj F) ⟶
      (jbang.{c, v, r} R U).obj ((jstar.{c, v, r} R U).obj F) ⊞
        (jbang.{c, v, r} R V).obj ((jstar.{c, v, r} R V).obj F) :=
  biprod.lift (nested.{c, v, r} R aU F) (-nested.{c, v, r} R aV F)

/-- The map from the two extensions to the ambient module is the sum of their counits.
Source: Stacks 03DI and the blueprint's open-cover triangle
(blueprint: lem-dla1-site-open-cover-extension-sequence). -/
def siteOpenCoverExtensionLast (U V : C) (F : Modules.{c, v, r} R) :
    (jbang.{c, v, r} R U).obj ((jstar.{c, v, r} R U).obj F) ⊞
      (jbang.{c, v, r} R V).obj ((jstar.{c, v, r} R V).obj F) ⟶ F :=
  biprod.desc ((adj.{c, v, r} R U).counit.app F) ((adj.{c, v, r} R V).counit.app F)

private theorem siteNested_naturality {A B : C} (a : A ⟶ B)
    {F G : Modules.{c, v, r} R} (f : F ⟶ G) :
    (jbang.{c, v, r} R A).map ((jstar.{c, v, r} R A).map f) ≫
        nested.{c, v, r} R a G =
      nested.{c, v, r} R a F ≫
        (jbang.{c, v, r} R B).map ((jstar.{c, v, r} R B).map f) := by
  apply ((adj.{c, v, r} R A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [nested, Equiv.apply_symm_apply]
  let α := overFunctorMap.{max c v r} (coefficients.{c, v, r} R) a
  let k := overMap.{max c v r} (coefficients.{c, v, r} R) a
  change (jstar.{c, v, r} R A).map f ≫
      (α.inv.app G ≫ k.map ((adj.{c, v, r} R B).unit.app _) ≫ α.hom.app _) =
    (α.inv.app F ≫ k.map ((adj.{c, v, r} R B).unit.app _) ≫ α.hom.app _) ≫
      (jstar.{c, v, r} R A).map
        ((jbang.{c, v, r} R B).map ((jstar.{c, v, r} R B).map f))
  rw [← Category.assoc, ← Category.assoc, α.inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  have hη := (adj.{c, v, r} R B).unit.naturality ((jstar.{c, v, r} R B).map f)
  simp only [Functor.id_map, Functor.comp_map] at hη
  rw [← k.map_comp_assoc]
  erw [hη]
  rw [k.map_comp_assoc]
  have hα := α.hom.naturality
    ((jbang.{c, v, r} R B).map ((jstar.{c, v, r} R B).map f))
  simp only [Functor.comp_map] at hα
  erw [hα]
  rfl

/-- The canonical binary-cover extension sequence is naturally short exact.
Source: Stacks 03DI--03DJ and the Gluing paragraph of the current tower-geometric blueprint
(blueprint: lem-dla1-site-open-cover-extension-sequence).

Proof:
1. Use `def-weil-extension-by-zero-presheaf` and
   `def-weil-presheaf-modules-sheafification` to construct extension. The normalized
   adjunction of `lem-pur-site-restriction-module-adjunction-exact` has counit the
   sheafified sum of the summand components. Relocalization and uniqueness of left
   adjoints identify `nested` with extension of the slice counit; compatibility of
   composite counits gives both displayed identities and makes the composite zero.
2. The unsigned overlap/counit square is a pushout by binary-cover descent
   (`lem-dla1-site-binary-cover-module-pushout`). Transpose maps from both extension
   terms to maps on the two slices; agreement over the overlap is exactly the
   sheaf gluing compatibility, so these maps glue uniquely to a map from F.
   The generic abelian pushout complex is exact and its last arrow is epi.
   Independently, the extension counit at the subterminal object W is mono by
   `lem-dla1-site-subterminal-module-counit-mono`: objectwise its presheaf form
   sums at most one copy of F, hence is injective, and exact sheafification preserves
   monicity. The first counit identity makes the W-to-U nested map mono by
   cancellation. Its factorization through the first biproduct projection makes
   the signed first map mono. Together these give the stated short exactness.
3. Restriction, the direct-sum presheaf, sheafification, units and counits are functorial.
   Consequently both signed arrows commute with every F → G as displayed below.
-/
theorem site_open_cover_extension_sequence (K : Precoverage C)
    (hsite : K.IsSiteForCoverings) [HasPullbacks C]
    (R : Sheaf K.toGrothendieck CommRingCat.{max c v r})
    {X U V : C} (hX : IsTerminal X) (u : U ⟶ X) (v : V ⟶ X) [Mono u] [Mono v]
    (hcover : Presieve.singleton u ⊔ Presieve.singleton v ∈ K X) :
    (∀ F : Modules.{c, v, r} R,
      nested.{c, v, r} R (Limits.pullback.fst u v) F ≫ (adj.{c, v, r} R U).counit.app F =
        (adj.{c, v, r} R (Limits.pullback u v)).counit.app F ∧
      nested.{c, v, r} R (Limits.pullback.snd u v) F ≫ (adj.{c, v, r} R V).counit.app F =
        (adj.{c, v, r} R (Limits.pullback u v)).counit.app F ∧
      ∃ hz : siteOpenCoverExtensionFirst.{c, v, r} R (Limits.pullback.fst u v)
          (Limits.pullback.snd u v) F ≫ siteOpenCoverExtensionLast.{c, v, r} R U V F = 0,
        (ShortComplex.mk
          (siteOpenCoverExtensionFirst.{c, v, r} R
            (Limits.pullback.fst u v) (Limits.pullback.snd u v) F)
          (siteOpenCoverExtensionLast.{c, v, r} R U V F) hz).ShortExact) ∧
    (∀ (F G : Modules.{c, v, r} R) (f : F ⟶ G),
      (jbang.{c, v, r} R (Limits.pullback u v)).map
          ((jstar.{c, v, r} R (Limits.pullback u v)).map f) ≫
        siteOpenCoverExtensionFirst.{c, v, r} R
          (Limits.pullback.fst u v) (Limits.pullback.snd u v) G =
      siteOpenCoverExtensionFirst.{c, v, r} R
        (Limits.pullback.fst u v) (Limits.pullback.snd u v) F ≫
        biprod.map
          ((jbang.{c, v, r} R U).map ((jstar.{c, v, r} R U).map f))
          ((jbang.{c, v, r} R V).map ((jstar.{c, v, r} R V).map f)) ∧
      biprod.map
          ((jbang.{c, v, r} R U).map ((jstar.{c, v, r} R U).map f))
          ((jbang.{c, v, r} R V).map ((jstar.{c, v, r} R V).map f)) ≫
        siteOpenCoverExtensionLast.{c, v, r} R U V G =
      siteOpenCoverExtensionLast.{c, v, r} R U V F ≫ f) := by
  refine ⟨?_, ?_⟩
  · intro F
    have hU : nested.{c, v, r} R (Limits.pullback.fst u v) F ≫
        (adj.{c, v, r} R U).counit.app F =
        (adj.{c, v, r} R (Limits.pullback u v)).counit.app F := by
      apply ((adj.{c, v, r} R (Limits.pullback u v)).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right]
      rw [show ((adj.{c, v, r} R (Limits.pullback u v)).homEquiv _ _)
        (nested.{c, v, r} R (Limits.pullback.fst u v) F) = _ from
          Equiv.apply_symm_apply _ _]
      rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
      let α := overFunctorMap.{max c v r} (coefficients.{c, v, r} R)
        (Limits.pullback.fst u v)
      change (α.inv.app F ≫ _ ≫ α.hom.app _) ≫
        (jstar.{c, v, r} R (Limits.pullback u v)).map
          ((adj.{c, v, r} R U).counit.app F) = 𝟙 _
      rw [Category.assoc, Category.assoc, ← α.hom.naturality]
      simp only [CategoryTheory.Functor.comp_map]
      rw [← CategoryTheory.Functor.map_comp_assoc,
        Adjunction.right_triangle_components, CategoryTheory.Functor.map_id,
        Category.id_comp]
      exact α.inv_hom_id_app F
    have hV : nested.{c, v, r} R (Limits.pullback.snd u v) F ≫
        (adj.{c, v, r} R V).counit.app F =
        (adj.{c, v, r} R (Limits.pullback u v)).counit.app F := by
      apply ((adj.{c, v, r} R (Limits.pullback u v)).homEquiv _ _).injective
      rw [Adjunction.homEquiv_naturality_right]
      rw [show ((adj.{c, v, r} R (Limits.pullback u v)).homEquiv _ _)
        (nested.{c, v, r} R (Limits.pullback.snd u v) F) = _ from
          Equiv.apply_symm_apply _ _]
      rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components]
      let α := overFunctorMap.{max c v r} (coefficients.{c, v, r} R)
        (Limits.pullback.snd u v)
      change (α.inv.app F ≫ _ ≫ α.hom.app _) ≫
        (jstar.{c, v, r} R (Limits.pullback u v)).map
          ((adj.{c, v, r} R V).counit.app F) = 𝟙 _
      rw [Category.assoc, Category.assoc, ← α.hom.naturality]
      simp only [CategoryTheory.Functor.comp_map]
      rw [← CategoryTheory.Functor.map_comp_assoc,
        Adjunction.right_triangle_components, CategoryTheory.Functor.map_id,
        Category.id_comp]
      exact α.inv_hom_id_app F
    refine ⟨hU, hV, ?_⟩
    have hz : siteOpenCoverExtensionFirst.{c, v, r} R (Limits.pullback.fst u v)
        (Limits.pullback.snd u v) F ≫ siteOpenCoverExtensionLast.{c, v, r} R U V F = 0 := by
      simp [siteOpenCoverExtensionFirst, siteOpenCoverExtensionLast, hU, hV]
    refine ⟨hz, ?_⟩
    have hP := siteBinaryCoverModulePushout.{c, v, r} K hsite R hX u v hcover F
    have : Mono ((adj.{c, v, r} R (Limits.pullback u v)).counit.app F) :=
      siteSubterminalModuleCounitMono.{c, v, r} R hX (Limits.pullback.fst u v ≫ u) F
    have : Mono (nested.{c, v, r} R (Limits.pullback.fst u v) F) :=
      mono_of_mono_fac hU
    have : Mono (siteOpenCoverExtensionFirst.{c, v, r} R (Limits.pullback.fst u v)
        (Limits.pullback.snd u v) F) :=
      mono_of_mono_fac (biprod.lift_fst _ _)
    exact ShortComplex.ShortExact.mk' hP.exact_shortComplex
      inferInstance hP.epi_shortComplex_g
  · intro F G f
    constructor
    · apply biprod.hom_ext
      · simpa [siteOpenCoverExtensionFirst, Category.assoc] using
          siteNested_naturality.{c, v, r} R (Limits.pullback.fst u v) f
      · simpa [siteOpenCoverExtensionFirst, Category.assoc] using
          congrArg Neg.neg
            (siteNested_naturality.{c, v, r} R (Limits.pullback.snd u v) f)
    · apply biprod.hom_ext'
      · simpa [siteOpenCoverExtensionLast, Category.assoc] using
          (adj.{c, v, r} R U).counit.naturality f
      · simpa [siteOpenCoverExtensionLast, Category.assoc] using
          (adj.{c, v, r} R V).counit.naturality f

end SheafOfModules
