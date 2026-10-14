/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded

/-! # Short exact rows for an unrestricted relative cover comparison

Source: Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY.
(blueprint: lem-pc-relative-mv-cover-rows).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Resolve the relative cover comparison as a map of short exact rows, before
passing from their quotients to mapping cones.
Source: Stacks Project, Cohomology, Tags 08BV and 08HZ (the restriction rows),
08FE (open direct-image comparison), and 08HY (the base-change mate).
(blueprint: lem-pc-relative-mv-cover-rows).

Proof: Choose injective-term K-injective resolutions of K and K'. Restrict to
U, V, their intersection and the inverse-image cover. Exact extension by zero
preserves K-injectivity under restriction. For each resolution take the pair
of restriction units and the difference of restrictions to the intersection.
Sheaf gluing proves the kernel assertion and injective flasqueness proves
surjectivity degreewise. Apply direct image; the same sequence on inverse
images of test opens stays exact and computes the relative direct images.
Transpose phi to K -> Rg'_*K', lift this map into the target K-injective
resolution, and restrict its components to the cover. For the source tensor
pullback, use a K-flat resolution of the entire finite diagram. A simultaneous
resolution is obtained in the category of diagrams; its underlying complexes
are K-flat and it preserves the short exact row in the derived category.
Lift the adjoint comparison there. Naturality of the restriction units and
the underived open counit square identify its three components and their
compatibilities, including the difference sign in the second horizontal map.
Rectify the resulting homotopy-commutative row diagram with mapping cylinders:
factor its first maps as degreewise split monomorphisms, extend the square
homotopies across the contractible cylinder summands, and take the quotient
maps. The cylinders are homotopy equivalent to the original middle vertices;
the resulting rows are degreewise split short exact and the quotient diagram
is the original overlap comparison, because it is formed from the resolved
restriction rows. Compare derived direct-image compositions by their adjoint
mates and use the additive biproduct comparison for the middle vertex. These
comparisons supply the six displayed isomorphisms. Expanding the base-change
mate and pasting the composite-adjunction counits identifies the global,
two local and quotient components with the displayed relative maps.
No identification of a mapping cone is asserted in this lemma: that is the
separate short-exact-to-cone quasi-isomorphism. Empty opens give zero local
terms, repeated opens give split restriction rows, and zero coefficients give
zero diagrams, so none of those cases requires extra hypotheses. -/
theorem relativeMV_cover_rows
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ a.left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (b U).left ⊞ (b V).left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom ≫ biprod.fst =
        e₂.hom ≫ biprod.fst ≫ (b U).hom ∧
      DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom ≫ biprod.snd =
        e₂.hom ≫ biprod.snd ≫ (b V).hom ∧
      DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ (b (U ⊓ V)).hom := by sorry

end AlgebraicGeometry
