/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.AlgebraicGeometry.ConstructibleEtaleFiniteAffineSyzygy
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.InverseImageFreeEtaleModule
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleFreeSheafDerivedSections
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import WeilConjectures.AlgebraicGeometry.LimitPullbackSectionsColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison

/-!
# Ext continuity for constructible etale modules in affine inverse limits

Source: Stacks Project, Etale Cohomology, Tags 09YU and 0GIT, with the finite-resolution
Ext argument recorded in the node (blueprint: lem-trf-constructible-etale-ext-continuity).

The canonical maps are constructed from exact inverse image on the ordinary module derived
category, its single-degree comparison, and `upperStarComp`. Continuity is expressed by
representatives: every limit class descends and equality is witnessed at a common later stage.

## Main definitions

- `AlgebraicGeometry.Etale.affineLimitExtHom`: derived Hom between shifted inverse images.
- `AlgebraicGeometry.Etale.affineLimitExtSingleIso`: the single-degree composition comparison.
- `AlgebraicGeometry.Etale.affineLimitExtPullback`: the canonical inverse-image map on Ext.
- `AlgebraicGeometry.Etale.affineLimitExtLeg`, `AlgebraicGeometry.Etale.affineLimitExtTransition`:
  the legs to the limit and the later-stage transition maps.

## Main statements

- `AlgebraicGeometry.Etale.affineLimitExtPullback_comp`,
  `AlgebraicGeometry.Etale.affineLimitExtPullback_trans`,
  `AlgebraicGeometry.Etale.affineLimitExtLeg_transition`: the compatibility clauses.
- `AlgebraicGeometry.Etale.constructible_etale_ext_continuity`: Ext continuity.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The derived Hom group between shifted inverse images of two module sheaves.
The single functors are at degrees `-p` and `-q`, hence represent `P[p]` and `Q[q]`.
For `p = 0`, `q = n`, this is the Ext group in the ordinary module derived category.
Source: the Ext convention in Tags 09YU and 0GIT and the node's statement
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
def affineLimitExtHom {S T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (f : T ⟶ S) (P Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q : ℤ) : Type (u + 1) :=
  ((DerivedCategory.singleFunctor _ (-p)).obj ((upperStar (ModuleCat.{u + 1} A) f).obj P) ⟶
    (DerivedCategory.singleFunctor _ (-q)).obj ((upperStar (ModuleCat.{u + 1} A) f).obj Q))

/-- Identify a single-degree pullback along `h = g ≫ f` with exact derived pullback along
`g` of the single-degree pullback along `f`. This uses the canonical inverse-image composition
isomorphism, followed by the inverse of `mapDerivedCategorySingleFunctor`.
Source: inverse-image functoriality in Tag 09YU and the node's last proof step
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
noncomputable def affineLimitExtSingleIso {S T Y : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S) (g : Y ⟶ T) (h : Y ⟶ S)
    (w : h = g ≫ f) (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℤ) :
    (DerivedCategory.singleFunctor _ (-p)).obj ((upperStar (ModuleCat.{u + 1} A) h).obj P) ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ (-p)).obj
          ((upperStar (ModuleCat.{u + 1} A) f).obj P)) :=
  (DerivedCategory.singleFunctor _ (-p)).mapIso
      ((upperStarComp (ModuleCat.{u + 1} A) g f h w).app P) ≪≫
    ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategorySingleFunctor (-p)).symm.app
      ((upperStar (ModuleCat.{u + 1} A) f).obj P)

/-- The canonical map on derived Hom induced by exact inverse image, transported by the
canonical single-degree and inverse-image composition comparisons. No map is chosen.
Source: inverse-image functoriality in Tag 09YU and the node's last proof step
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
noncomputable def affineLimitExtPullback {S T Y : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S) (g : Y ⟶ T) (h : Y ⟶ S)
    (w : h = g ≫ f) (P Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q : ℤ) (a : affineLimitExtHom f P Q p q) : affineLimitExtHom h P Q p q :=
  (affineLimitExtSingleIso f g h w P p).hom ≫
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map a ≫
    (affineLimitExtSingleIso f g h w Q q).inv

/-- Exact inverse image preserves composition of derived morphisms, including morphisms
between different single degrees. Source: the composition clause of the node, Tag 09YU.
Proof: expand the conjugations, cancel the middle single-degree comparison and its inverse,
and apply `Functor.map_comp` to the exact derived inverse-image functor.
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
theorem affineLimitExtPullback_comp {S T Y : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (f : T ⟶ S) (g : Y ⟶ T) (h : Y ⟶ S)
    (w : h = g ≫ f) (P Q R : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q r : ℤ) (a : affineLimitExtHom f P Q p q) (b : affineLimitExtHom f Q R q r) :
    affineLimitExtPullback f g h w P R p r (a ≫ b) =
      affineLimitExtPullback f g h w P Q p q a ≫
        affineLimitExtPullback f g h w Q R q r b := by
  sorry

/-- Pullback of derived Hom is compatible with a further inverse image over the same base.
Source: passage-to-later-stages clause of the node, Tag 09YU and its last proof step.
Proof: use the associativity of `upperStarComp`, apply its natural transformations termwise
to complexes and then localize; naturality of `mapDerivedCategorySingleFunctor` identifies
the two conjugations. The derived functor composition comparison identifies the two images
of the morphism, giving the displayed equality.
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
theorem affineLimitExtPullback_trans {S T Y Z : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A]
    (f : T ⟶ S) (g : Y ⟶ T) (h : Y ⟶ S) (w : h = g ≫ f)
    (k : Z ⟶ Y) (l : Z ⟶ S) (v : l = k ≫ h)
    (P Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q : ℤ) (a : affineLimitExtHom f P Q p q) :
    affineLimitExtPullback h k l v P Q p q (affineLimitExtPullback f g h w P Q p q a) =
      affineLimitExtPullback f (k ≫ g) l
        (v.trans ((congrArg (fun t ↦ k ≫ t) w).trans (Category.assoc k g f).symm))
        P Q p q a := by
  sorry

/-- The canonical Ext leg from stage `j` to the limit, with the cone equation supplying the
comparison to the fixed stage `i`. Source: Tag 09YU, canonical pullback to the limit
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
noncomputable def affineLimitExtLeg {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {i j : I} (hij : i ≤ j)
    {A : Type (u + 1)} [CommRing A]
    (P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q : ℤ) (a : affineLimitExtHom (D.map (homOfLE hij).op) P Q p q) :
    affineLimitExtHom (c.π.app (op i)) P Q p q :=
  affineLimitExtPullback (D.map (homOfLE hij).op) (c.π.app (op j)) (c.π.app (op i))
    (c.w (homOfLE hij).op).symm P Q p q a

/-- The covariant later-stage map: `i ≤ j ≤ k` gives Ext on `X_j` to Ext on `X_k`.
Source: Tag 09YU, the inverse-image transition maps of the node
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
noncomputable def affineLimitExtTransition {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {A : Type (u + 1)} [CommRing A]
    (P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q : ℤ) (a : affineLimitExtHom (D.map (homOfLE hij).op) P Q p q) :
    affineLimitExtHom (D.map (homOfLE (hij.trans hjk)).op) P Q p q :=
  affineLimitExtPullback (D.map (homOfLE hij).op) (D.map (homOfLE hjk).op)
    (D.map (homOfLE (hij.trans hjk)).op)
    (D.map_comp (homOfLE hjk).op (homOfLE hij).op) P Q p q a

/-- The canonical legs agree after passage to a later stage.
Source: the later-stage clause of the node, Tag 09YU.
Proof: apply `affineLimitExtPullback_trans` to the stage transition and the limit projection.
The cone equation identifies their composite with the earlier projection. Proof irrelevance
identifies the witnesses in `upperStarComp`, so the resulting pullbacks agree.
(blueprint: lem-trf-constructible-etale-ext-continuity). -/
theorem affineLimitExtLeg_transition {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {A : Type (u + 1)} [CommRing A]
    (P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (p q : ℤ) (a : affineLimitExtHom (D.map (homOfLE hij).op) P Q p q) :
    affineLimitExtLeg D c (hij.trans hjk) P Q p q
        (affineLimitExtTransition D hij hjk P Q p q a) =
      affineLimitExtLeg D c hij P Q p q a := by
  sorry

/-- Every Ext class at the limit descends, and two representatives with the same image
become equal at a common later stage. This is elementwise bijectivity of the filtered-colimit
comparison, with the canonical maps above; their composition and later-stage compatibility
are stated by `affineLimitExtPullback_comp` and `affineLimitExtLeg_transition`.
Source: Tags 09YU and 0GIT, with the finite-resolution Ext argument in the node
(blueprint: lem-trf-constructible-etale-ext-continuity).

Proof: resolve the constructible source through the required finite degree by finite sums
of extension-by-zero free sheaves on affine etale objects; all syzygies remain constructible.
For each free term, extension-by-zero adjunction computes Ext by cohomology on the affine
objects. Canonical free-sheaf pullback identifies the comparison maps with section/cohomology
pullback, so affine-limit cohomology continuity gives their bijectivity. In degree zero, the
finite presentation expresses Hom as the kernel of two finite sums of sections: sections
descend to a common stage and relations vanish at a common later stage. For degree `n`,
induct simultaneously on degree and syzygy index, first proving injectivity with the mono
four lemma on the shifted Ext sequence and then surjectivity with the epi four lemma on
the unshifted sequence. Filtered-colimit exactness supplies the exact rows. At syzygy zero
and degree `n`, this gives exactly the two representative clauses below. All maps are the
exact-inverse-image maps used in these calculations, with compatibility supplied above. -/
theorem constructible_etale_ext_continuity
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, IsNoetherian (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hP : (D.obj (op i)).IsConstructibleEtaleModuleSheaf P)
    (hQ : (D.obj (op i)).IsConstructibleEtaleModuleSheaf Q) :
    ∀ n : ℕ,
      (∀ a : affineLimitExtHom (c.π.app (op i)) P Q 0 (n : ℤ),
        ∃ (j : I) (hij : i ≤ j)
          (b : affineLimitExtHom (D.map (homOfLE hij).op) P Q 0 (n : ℤ)),
          affineLimitExtLeg D c hij P Q 0 (n : ℤ) b = a) ∧
      (∀ (j k : I) (hij : i ≤ j) (hik : i ≤ k)
        (a : affineLimitExtHom (D.map (homOfLE hij).op) P Q 0 (n : ℤ))
        (b : affineLimitExtHom (D.map (homOfLE hik).op) P Q 0 (n : ℤ)),
        affineLimitExtLeg D c hij P Q 0 (n : ℤ) a =
          affineLimitExtLeg D c hik P Q 0 (n : ℤ) b →
        ∃ (l : I) (hjl : j ≤ l) (hkl : k ≤ l),
          affineLimitExtTransition D hij hjl P Q 0 (n : ℤ) a =
            affineLimitExtTransition D hik hkl P Q 0 (n : ℤ) b) := by
  sorry

end AlgebraicGeometry.Etale
