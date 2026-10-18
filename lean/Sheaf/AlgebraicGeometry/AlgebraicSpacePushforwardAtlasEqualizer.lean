/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-!
# The atlas equalizer for a module direct image on an algebraic space

Source: Stacks Project, Morphisms of Algebraic Spaces, Tag 03M8
(blueprint: lem-trf-space-pushforward-atlas-equalizer).

All three arrows are characterized on every compatible chart section. Étale tensor
pullbacks are represented by the existing restriction functor `pullback`. The module
on the overlap is restriction of the original module along the first composite;
the pullback square canonically identifies it with restriction along the second.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine surjective étale atlas computes module direct image by its Čech kernel.
Source: Stacks Project, Morphisms of Algebraic Spaces, Tag 03M8
(blueprint: lem-trf-space-pushforward-atlas-equalizer).

The three projection formulas specify the canonical arrows, rather than just the
existence of an abstract kernel diagram. In each formula the two chart conditions
say that the charts have the same underlying scheme, map to the source, and map to
`V`. Heterogeneous equality compares the same section in the two presentations of
its module of sections; it introduces no change of coefficient universe.

Proof:
1. Extend `F` to the enlarged étale ringed site by
   lem-trf-space-enlarged-etale-ringed-site-model. Its values on `X ×_Y V` give
   the chart-limit direct image of def-trf-space-etale-module-functors.
2. Represent the atlas overlap by a scheme, using
   lem-trf-space-fibre-products-etale-covers. Its two projections are étale.
   Base change the atlas by `V → Y`: the singleton `V ×_Y U → V ×_Y X` covers.
   Use lem-trf-space-chartwise-etale-permanence to regard these as enlarged objects.
3. The overlap of that cover, taken over `V ×_Y X`, is `V ×_Y R` by the
   fibre-product universal property: its sections are triples `(v,u₁,u₂)` with
   the same `v` and equal images of `u₁,u₂` in `X`.
4. The normalized comparison of lem-trf-space-etale-module-pushforward-restriction
   identifies the étale tensor pullbacks with restriction, preserving the original
   `F` section on every chart. The two pullbacks to `R` agree through the square.
   Restriction to `U` and to its two projections gives exactly the three displayed
   projection formulas. These characterize the arrows by the chart-limit property.
5. Apply the singleton-cover sheaf equalizer of def-weil-pbc-sites-and-cohomology
   to the underlying abelian sheaf. Restrictions are linear over `O_Y(V)` by
   def-weil-sheaf-of-modules-category, since the maps have the same composite to `V`.
   Thus restriction is injective and its image is the kernel of the difference.
6. The construction commutes with restrictions in `V` and with module morphisms.
   Kernels are sectionwise, so the section equalizers give the asserted kernel
   fork in `Y.Modules`. This gives exactness at the first two terms only. -/
theorem moduleDirectImage_atlas_equalizer
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : Over S) [IsAffine U.left] (p : schemeSpace U ⟶ X)
    (hp : IsEtale p.hom.hom) (hs : IsSurjective p.hom.hom) (F : X.Modules) :
    ∃ (R : Over S) (p₁ p₂ : schemeSpace R ⟶ schemeSpace U)
      (h₁ : IsEtale p₁.hom.hom) (h₂ : IsEtale p₂.hom.hom),
      IsPullback p₁.hom p₂.hom p.hom p.hom ∧
      ∃ (ι : (moduleDirectImage f).obj F ⟶
          (moduleDirectImage (p ≫ f)).obj ((pullback p hp).obj F))
        (r₁ r₂ : (moduleDirectImage (p ≫ f)).obj ((pullback p hp).obj F) ⟶
          (moduleDirectImage ((p₁ ≫ p) ≫ f)).obj
            ((pullback (p₁ ≫ p) (isEtale_comp p₁.hom.hom p.hom.hom h₁ hp)).obj F)),
        (∀ (V : Y.EtaleSite) (q : ModuleChart f V) (t : ModuleChart (p ≫ f) V),
          q.left.obj = (moduleChartTarget p).obj t.left →
          HEq q.hom.left t.hom.left →
          ∀ s : ((moduleDirectImage f).obj F).val.obj (op V),
            HEq
              (((moduleDirectImageModel (p ≫ f)).projection ((pullback p hp).obj F) V).app
                (op t) (ι.val.app (op V) s))
              (((moduleDirectImageModel f).projection F V).app (op q) s)) ∧
        (∀ (V : Y.EtaleSite) (q : ModuleChart (p ≫ f) V)
          (t : ModuleChart ((p₁ ≫ p) ≫ f) V),
          q.left.obj = (moduleChartTarget p₁).obj t.left →
          HEq q.hom.left t.hom.left →
          ∀ s : ((moduleDirectImage (p ≫ f)).obj ((pullback p hp).obj F)).val.obj (op V),
            HEq
              (((moduleDirectImageModel ((p₁ ≫ p) ≫ f)).projection
                ((pullback (p₁ ≫ p) (isEtale_comp p₁.hom.hom p.hom.hom h₁ hp)).obj F)
                V).app (op t) (r₁.val.app (op V) s))
              (((moduleDirectImageModel (p ≫ f)).projection ((pullback p hp).obj F) V).app
                (op q) s)) ∧
        (∀ (V : Y.EtaleSite) (q : ModuleChart (p ≫ f) V)
          (t : ModuleChart ((p₁ ≫ p) ≫ f) V),
          q.left.obj = (moduleChartTarget p₂).obj t.left →
          HEq q.hom.left t.hom.left →
          ∀ s : ((moduleDirectImage (p ≫ f)).obj ((pullback p hp).obj F)).val.obj (op V),
            HEq
              (((moduleDirectImageModel ((p₁ ≫ p) ≫ f)).projection
                ((pullback (p₁ ≫ p) (isEtale_comp p₁.hom.hom p.hom.hom h₁ hp)).obj F)
                V).app (op t) (r₂.val.app (op V) s))
              (((moduleDirectImageModel (p ≫ f)).projection ((pullback p hp).obj F) V).app
                (op q) s)) ∧
        ∃ hz : ι ≫ (r₁ - r₂) = 0, Nonempty (IsLimit (KernelFork.ofι ι hz)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
