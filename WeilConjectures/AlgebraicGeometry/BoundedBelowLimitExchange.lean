/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.AlgebraicGeometry.DerivedInverseImageComposition
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Bounded-below exchange under affine inverse limits

Source: Stacks Project, Tag 0GJL, `lemma-base-change-Rf-star-colim-complexes`,
with the inverse system of Tag 0EZT and the relative continuity of Tag 0GIU
(blueprint: lem-sf-bounded-below-limit-exchange).

The four cones specify arbitrary representatives of the four scheme limits. The
projection equations specify the induced edges. The chosen Cartesian identifications
record the stage squares and their limit square. The exchange is the recorded abelian
exchange, evaluated on bounded-below objects. Since `D⁺` is a full subcategory of `D`,
invertibility can equivalently be read in `D` as below.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The canonical exchange for a bounded-below abelian etale complex is invertible
at an affine-transition inverse limit if it is invertible at every stage above the
stage from which the complex is pulled back.

Source: Stacks Project, Tag 0GJL, `lemma-base-change-Rf-star-colim-complexes`
(blueprint: lem-sf-bounded-below-limit-exchange).

Proof in words:
1. Restrict to the nonempty directed tail above `i₀`. A cone extends to the original
   index by choosing a common upper bound, independently of the choice, so all four
   limits stay the same. The limit square is Cartesian by the universal properties
   of the four limits and the stage pullbacks. Base change preserves qcqs, hence
   each `h.app i` is qcqs (lem-weil-pbc-qcqs-morphism-permanence).
2. Set `Lᵢ = eᵢ⁻¹ Kᵢ` and `L = e⁻¹ K`. The canonical inverse-image composition
   comparisons identify these with pullbacks from `L₀` and respect transitions
   (lem-weil-pbc-derived-inverse-image-composition). Apply the two relative
   continuity isomorphisms of lem-sf-relative-derived-image-limit, first to `g`
   and then to `h`, in every integer degree `p`.
3. Inverse image commutes with the colimits
   (lem-weil-pbc-inverse-image-preserves-colimits). The projection equations and
   coherent composition identify the source colimit after pulling back by `f`.
   Exactness (prop-weil-pbc-inverse-image-exact) and the natural cohomology
   comparison (lem-weil-pbc-exact-functor-complex-cohomology) identify these
   sheaves with the cohomology of the two sides of exchange.
4. Identify the maps: the canonical legs of relative continuity are the mates of
   inverse-image squares. Apply lem-weil-pbc-mate-pasting to the two factorizations
   of each projection rectangle, using the coherent inverse-image comparisons.
   This gives `cᵢʰ ∘ rᵢ⁻¹ βᵢ = β ∘ f⁻¹ cᵢᵍ`, and the same equation for transition
   rectangles. Thus the stage exchanges form a natural transformation and its
   colimit is the cohomology of the limit exchange under the continuity isomorphisms.
5. Each stage exchange is invertible. The inverses also commute with transitions,
   so the colimit universal property (def-weil-pbc-category-colimit) constructs
   the inverse of their colimit map. Hence the limit exchange induces isomorphisms
   on cohomology in every integer degree, including negative degrees. Apply
   lem-weil-pbc-derived-plus-iso-on-cohomology to obtain the asserted isomorphism.
-/
theorem isIso_abelianDerivedBaseChangeArrow_of_affine_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (Y T X S : Iᵒᵖ ⥤ Scheme.{u})
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S)
    (sq : ∀ i : Iᵒᵖ,
      ChosenCartesianSquare (h.app i) (e.app i) (f.app i) (g.app i))
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (Y.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (T.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (X.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (S.map a)]
    [∀ i : Iᵒᵖ, QuasiCompact (g.app i)]
    [∀ i : Iᵒᵖ, QuasiSeparated (g.app i)]
    (cY : Cone Y) (cT : Cone T) (cX : Cone X) (cS : Cone S)
    (_hcY : IsLimit cY) (_hcT : IsLimit cT) (_hcX : IsLimit cX) (_hcS : IsLimit cS)
    (eLim : cY.pt ⟶ cT.pt) (hLim : cY.pt ⟶ cX.pt)
    (gLim : cT.pt ⟶ cS.pt) (fLim : cX.pt ⟶ cS.pt)
    (_he : ∀ i : Iᵒᵖ, eLim ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (_hh : ∀ i : Iᵒᵖ, hLim ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (_hg : ∀ i : Iᵒᵖ, gLim ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (_hf : ∀ i : Iᵒᵖ, fLim ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (sqLim : ChosenCartesianSquare hLim eLim fLim gLim)
    (i₀ : I)
    (K₀ : _root_.DerivedCategory.Plus
      (Sheaf (T.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (_hstage : ∀ (i : I) (hi : i₀ ≤ i),
      IsIso (abelianDerivedBaseChangeArrow (sq (op i))
        (((upperStar AddCommGrpCat.{u + 1} (T.map (homOfLE hi).op)).mapDerivedCategoryPlus.obj
          K₀).obj))) :
    IsIso (abelianDerivedBaseChangeArrow sqLim
      (((upperStar AddCommGrpCat.{u + 1} (cT.π.app (op i₀))).mapDerivedCategoryPlus.obj
        K₀).obj)) := by
  sorry

end AlgebraicGeometry.Etale
