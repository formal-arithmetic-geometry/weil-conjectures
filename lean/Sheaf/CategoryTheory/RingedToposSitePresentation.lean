/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.SheafSubcategoryComparison
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Presenting a morphism of ringed topoi by a morphism of sites

Source: Stacks Project, Modules on Sites, Tag 03CR, using Sites Tags 03A1, 03CI and 03A2
(blueprint: lem-weil-pbc-ringed-topos-site-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Every morphism of ringed topoi admits a finite-limit site presentation.

Source: Stacks Project, Tag 03CR, clauses (1)-(6)
(blueprint: lem-weil-pbc-ringed-topos-site-presentation).

The commutative ring sheaves are forgotten to ring sheaves only to use the existing
`RingedToposMorphism` interface. Its module direct image is the induced one, not extra
geometric data. The identifications `a` and `b`, together with their counit equations,
express exactly `A' = g_* A` and `B' = e_* B` as transported ring sheaves. Indeed their
adjuncts are ring maps; the equivalence counits are isomorphisms, so this characterizes
the transported ring structures and their canonical structural isomorphisms. No arbitrary
identification of the structural maps is allowed. The last equation says that the inverse
image comparison `alpha` identifies the structural ring maps of the composite morphisms.
Its adjoint mate gives the corresponding direct image comparison.

Proof:
1. In the sheaves on `D`, start with the sheafified representables, the terminal sheaf
   and `B`. Close this set of objects under chosen pullbacks, iterating over the natural
   numbers. At each stage the arrows form a set. Every finite diagram occurs at some stage;
   the resulting full small category `D'` has terminal objects and pullbacks, hence finite
   limits (equalizers are pullbacks of diagonals).
2. Give `D'` the epimorphic covering families. The sheaf subcategory comparison theorem
   gives the equivalence `e`, with sections at `T` equal to `Hom(T,-)`. In the sheaves on
   `C`, repeat the construction including `A` and every `f.inverse.obj T` for `T` in `D'`.
   This gives `C'` and `g` with the same Hom formula.
3. Restrict `f.inverse` to obtain `v : D' ⥤ C'`. Ambient finite limits compute those of
   the full subcategories, so `v` preserves finite limits, including the terminal object.
4. A left adjoint preserves colimits. Coproducts of sheaves are sheafified presheaf
   coproducts; epimorphisms of sheaves are coequalizers of their kernel pairs. Therefore
   `f.inverse` sends epimorphic families to epimorphic families. Choose the covering
   precoverages to include their images; this changes neither topology nor sheaves.
   Pullback comparisons are isomorphisms by step 3. Thus `v` is Stacks-continuous.
5. The left-exact site inverse-image theorem supplies `h`, with direct image given by
   precomposition with `v` and finite-limit-preserving inverse image.
6. The Hom formulas and the original adjunction give, naturally in both arguments,
   `(h_* g_* F)(T) = Hom(f.inverse.obj T,F) ≃ Hom(T,f.direct.obj F)`.
   This is the direct image comparison. Uniqueness of adjoints, or the Yoneda Hom
   bijection, gives its inverse-image mate `alpha`, compatibly with both adjunctions.
7. Finite-product-preserving functors transport ring operations and their equations;
   natural transformations commute with them. Transport `A` and `B` by `g_*` and `e_*`.
   Their structural maps are the counits, giving `a` and `b` and the displayed equations.
   Define the direct-image ring map of `h` by `e_*` of the adjunct of `f.ringMap`, followed
   by the direct image comparison in step 6. Take its adjunct for `h.ringMap`. The final
   equation follows from this definition and the mate identities. All module direct
   images are the induced ones, so the three morphisms have the existing interface. -/
theorem ringedTopos_sitePresentation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (A : Sheaf J.toGrothendieck CommRingCat.{u})
    (B : Sheaf K.toGrothendieck CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K.toGrothendieck (forget₂ CommRingCat RingCat)).obj B)) :
    ∃ (C' D' : Type u) (_ : SmallCategory C') (_ : SmallCategory D')
      (J' : Precoverage C') (K' : Precoverage D')
      (_ : J'.HasIsos) (_ : J'.IsStableUnderComposition)
      (_ : J'.IsStableUnderBaseChange) (_ : J'.HasPullbacks)
      (_ : K'.HasIsos) (_ : K'.IsStableUnderComposition)
      (_ : K'.IsStableUnderBaseChange) (_ : K'.HasPullbacks)
      (_ : HasFiniteLimits C') (_ : HasFiniteLimits D')
      (A' : Sheaf J'.toGrothendieck CommRingCat.{u})
      (B' : Sheaf K'.toGrothendieck CommRingCat.{u})
      (g : RingedToposMorphism
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj A)
        ((sheafCompose J'.toGrothendieck (forget₂ CommRingCat RingCat)).obj A'))
      (e : RingedToposMorphism
        ((sheafCompose K.toGrothendieck (forget₂ CommRingCat RingCat)).obj B)
        ((sheafCompose K'.toGrothendieck (forget₂ CommRingCat RingCat)).obj B'))
      (h : RingedToposMorphism
        ((sheafCompose J'.toGrothendieck (forget₂ CommRingCat RingCat)).obj A')
        ((sheafCompose K'.toGrothendieck (forget₂ CommRingCat RingCat)).obj B'))
      (v : D' ⥤ C') (_ : PreservesFiniteLimits v)
      (_ : v.IsContinuous K'.toGrothendieck J'.toGrothendieck)
      (a : (sheafCompose J'.toGrothendieck (forget CommRingCat)).obj A' ≅
        g.direct.obj ((sheafCompose J.toGrothendieck (forget CommRingCat)).obj A))
      (b : (sheafCompose K'.toGrothendieck (forget CommRingCat)).obj B' ≅
        e.direct.obj ((sheafCompose K.toGrothendieck (forget CommRingCat)).obj B))
      (alpha : e.inverse ⋙ f.inverse ≅ h.inverse ⋙ g.inverse),
      g.direct.IsEquivalence ∧ e.direct.IsEquivalence ∧
      (∀ (T : D') (R : Presieve T), R ∈ K' T → R.map v ∈ J' (v.obj T)) ∧
      h.direct = v.sheafPushforwardContinuous (Type u)
        K'.toGrothendieck J'.toGrothendieck ∧
      g.ringMap = g.inverse.map a.hom ≫
        g.adj.counit.app ((sheafCompose J.toGrothendieck (forget CommRingCat)).obj A) ∧
      e.ringMap = e.inverse.map b.hom ≫
        e.adj.counit.app ((sheafCompose K.toGrothendieck (forget CommRingCat)).obj B) ∧
      f.inverse.map e.ringMap ≫ f.ringMap =
        alpha.hom.app ((sheafCompose K'.toGrothendieck (forget CommRingCat)).obj B') ≫
          g.inverse.map h.ringMap ≫ g.ringMap := by
  sorry

end CategoryTheory
