/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.SitePointReconstructionSets
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Filtered.Final
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# Realizing a finitely presented stalk module on a localized site

Source: Stacks Project, Cohomology on Sites, Tag 0DEN, proof of (1), and Sites,
Tag 04H2 (blueprint: lem-sfb-site-fp-stalk-realization).

The stalk ring and module functors below are actual filtered colimits of sections.
The localized stalk uses the over category of the pointed neighborhood `(U,x)`.
Its ring cocone has the original stalk ring as vertex; initiality of the forgetful
functor makes it a colimit, giving the canonical identification of the two rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteFpStalkRealization

variable {C : Type u} [SmallCategory C]

/-- Restriction of a commutative ring sheaf to a neighborhood system, forgetting only
commutativity. Source: Stacks, 0DEN (blueprint: lem-sfb-site-fp-stalk-realization). -/
def ringDiagram {N : Type u} [SmallCategory N] (d : N ⥤ C)
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) : Nᵒᵖ ⥤ RingCat.{u} :=
  d.op ⋙ R.obj ⋙ forget₂ CommRingCat RingCat

/-- The module stalk over any specified colimit ring cocone. This is Mathlib's
varying-ring module colimit, not a chosen lift of a set functor.
Source: Stacks, 0DEN (blueprint: lem-sfb-site-fp-stalk-realization). -/
def modules {N : Type u} [SmallCategory N] [IsCofiltered N] (d : N ⥤ C)
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c) :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ModuleCat.{u} c.pt :=
  letI : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall N
  SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward₀ d _ ⋙
    PresheafOfModules.colimitFunctor hc

/-- The underlying set stalk over a neighborhood system, as an actual section colimit.
Source: Stacks, 04H2 (blueprint: lem-sfb-site-fp-stalk-realization). -/
def sets {N : Type u} [SmallCategory N] (d : N ⥤ C)
    (J : GrothendieckTopology C) : Sheaf J (Type u) ⥤ Type u :=
  sheafToPresheaf J (Type u) ⋙ (Functor.whiskeringLeft _ _ _).obj d.op ⋙ colim

variable (J : Precoverage C) [HasFiniteLimits C]
  (p : GeometricMorphism (Type u) (Sheaf J.toGrothendieck (Type u)))

/-- Forget the element of a pointed neighborhood. Source: Stacks, 00YA and 0DEN
(blueprint: lem-sfb-site-fp-stalk-realization). -/
abbrev neighborhoods : sitePointNeighbourhood J p ⥤ C :=
  CategoryOfElements.π (sitePointFunctor J p)

/-- The stalk ring is the colimit of the section rings over pointed neighborhoods.
Source: Stacks, 0DEN (blueprint: lem-sfb-site-fp-stalk-realization). -/
def stalkRing (R : Sheaf J.toGrothendieck CommRingCat.{u}) : RingCat.{u} :=
  colimit (ringDiagram (neighborhoods J p) R)

/-- Module inverse image at the point, constructed by the varying-ring module colimit.
Cofilteredness is the recorded site-point reconstruction theorem, not a hypothesis.
Source: Stacks, 0DEN (blueprint: lem-sfb-site-fp-stalk-realization). -/
def stalkModules (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R) ⥤
        ModuleCat.{u} (stalkRing J p R) :=
  letI := (site_point_reconstruction_sets J hJ p).2.2.1
  modules (neighborhoods J p) R (colimit.isColimit _)

/-- A neighborhood of `(U,x)` determines an object over `U`, by its underlying arrow.
Source: Stacks, 04H2 (blueprint: lem-sfb-site-fp-stalk-realization). -/
def localizedNeighborhoods (n : sitePointNeighbourhood J p) :
    Over n ⥤ Over n.1 :=
  Over.post (neighborhoods J p)

/-- The ring cocone on pointed neighborhoods of `(U,x)`, with vertex the original
stalk ring. Source: Stacks, 04H2 (blueprint: lem-sfb-site-fp-stalk-realization). -/
def localizedRingCocone (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (n : sitePointNeighbourhood J p) :
    Cocone (ringDiagram (localizedNeighborhoods J p n) (R.over n.1)) :=
  (colimit.cocone (ringDiagram (neighborhoods J p) R)).whisker (Over.forget n).op

/-- Initial restriction gives the colimit universal property of the localized ring
cocone. Source: Stacks, 04H2 (blueprint: lem-sfb-site-fp-stalk-realization). -/
def localizedRingIsColimit (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p) :
    IsColimit (localizedRingCocone J p R n) :=
  letI := (site_point_reconstruction_sets J hJ p).2.2.1
  (Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm (colimit.isColimit _)

/-- The canonical ring identification `q⁻¹ R_U ≅ R_p`, induced by restriction of
section germs. Source: Stacks, 04H2 (blueprint: lem-sfb-site-fp-stalk-realization). -/
def localizedRingIso (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p) :
    colimit (ringDiagram (localizedNeighborhoods J p n) (R.over n.1)) ≅ stalkRing J p R :=
  colimit.isoColimitCocone
    ⟨localizedRingCocone J p R n, localizedRingIsColimit J p hJ R n⟩

/-- Localized module stalks with scalars identified by the preceding canonical ring
cocone. Source: Stacks, 04H2 and 0DEN (blueprint: lem-sfb-site-fp-stalk-realization). -/
def localizedModules (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p) :
    ringedSiteModules.{u}
      (((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1) ⥤
        ModuleCat.{u} (stalkRing J p R) :=
  letI := (site_point_reconstruction_sets J hJ p).2.2.1
  modules (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n)

/-- Section-to-germ map in a varying-ring module colimit. Source: Stacks, 0DEN
(blueprint: lem-sfb-site-fp-stalk-realization). -/
def moduleGerm {N : Type u} [SmallCategory N] [IsCofiltered N] (d : N ⥤ C)
    {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c)
    (F : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    (n : N) (s : F.val.obj (op (d.obj n))) : (modules d R hc).obj F :=
  letI : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall N
  PresheafOfModules.ModuleColimit.ιM (hcR := hc) (hcM := colimit.isColimit _) s

/-- The point module germ, with cofilteredness supplied by site-point reconstruction.
Source: Stacks, 0DEN (blueprint: lem-sfb-site-fp-stalk-realization). -/
def stalkModuleGerm (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (F : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R))
    (n : sitePointNeighbourhood J p) (s : F.val.obj (op n.1)) :
    (stalkModules J p hJ R).obj F :=
  letI := (site_point_reconstruction_sets J hJ p).2.2.1
  moduleGerm (neighborhoods J p) R (colimit.isColimit _) F n s

/-- The slice module germ, with its scalars already canonically identified with `R_p`.
Source: Stacks, 04H2 (blueprint: lem-sfb-site-fp-stalk-realization). -/
def localizedModuleGerm (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p)
    (F : ringedSiteModules.{u}
      (((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1))
    (z : Over n) (s : F.val.obj (op ((localizedNeighborhoods J p n).obj z))) :
    (localizedModules J p hJ R n).obj F :=
  letI := (site_point_reconstruction_sets J hJ p).2.2.1
  moduleGerm (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n) F z s

/-- A finite-presentation module over a point's stalk ring is the stalk of a finite
matrix cokernel on a pointed localization.

Source: Stacks Project, Cohomology on Sites, Tag 0DEN, proof of (1), paragraph
beginning “Let M be a finitely presented O_p-module”; Sites, Tag 04H2
(blueprint: lem-sfb-site-fp-stalk-realization).

The object `n` is precisely the pair `(U,x)`. The inverse image of `q` is specified
as the section colimit over neighborhoods mapping to `(U,x)`, so it is the point
specified by `x`. The ring comparison is `localizedRingIso`, and `localizedModules`
uses its colimit cocone to transport scalars to `R_p`. The set and module comparison
isomorphisms are normalized on every section germ, excluding arbitrary comparisons.

Proof, following the five steps of the node:
1. Apply lem-trf-site-point-reconstruction-sets: pointed neighborhoods are nonempty
and cofiltered and their section colimit is `p.inverse`, with germ `p⁻¹(s)(x)`.
This identifies the colimit ring and module constructions with algebraic inverse
image, for the given variable ring sheaf.
2. Choose a finite free presentation of `M` (def-sc-finitely-presented-module).
Represent each of its finitely many matrix coefficients by a section. Choose a
common pointed neighborhood by cofilteredness. Ring germs preserve addition and
multiplication by the finite-product preservation of `p.inverse`. For an empty
matrix choose any pointed neighborhood, using nonemptiness.
3. Apply lem-weil-pbc-localized-sheaves-over-representable and the left-exact
slice-adjoint lemma lem-sfb-left-exact-left-adjoint-slices. Compose its inverse
image with the fiber over `x`; its right adjoint has the prescribed fiber at `x`
and singleton fibers elsewhere. This constructs `q`. Its neighborhoods are exactly
arrows to `(U,x)`, giving the displayed section-colimit inverse image.
4. Restriction corresponds to the product with the sheafified representable.
Applying the point and taking the `x`-fiber gives the natural set comparison,
normalized on germs. The same calculation preserves ring and module operations.
Initiality of the neighborhood forgetful functor gives `localizedRingIso` and the
natural module comparison, with exactly the displayed germ formula.
5. Define `α` by the lifted matrix and let `F` be its sheaf cokernel in the abelian
module-sheaf category. Algebraic inverse image preserves cokernels
(lem-trf-geometric-inverse-image-exact) and finite free modules, including rank zero.
Its matrix is the original presentation matrix by step 4, so its cokernel is `M`.
-/
theorem exists_fp_stalk_realization (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (M : ModuleCat.{u} (stalkRing J p R))
    [Module.FinitePresentation (stalkRing J p R) M] :
    ∃ (n : sitePointNeighbourhood J p)
      (q : GeometricMorphism (Type u)
        (Sheaf (J.toGrothendieck.over n.1) (Type u)))
      (e : J.toGrothendieck.overPullback (Type u) n.1 ⋙
        sets (localizedNeighborhoods J p n) (J.toGrothendieck.over n.1) ≅ p.inverse)
      (comparison : SheafOfModules.overFunctor
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R) n.1 ⋙
          localizedModules J p hJ R n ≅ stalkModules J p hJ R)
      (F : ringedSiteModules.{u}
        (((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1))
      (a b : ℕ) (A : Fin b → Fin a → R.obj.obj (op n.1))
      (α : SheafOfModules.free (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
            (ULift.{u} (Fin a)) ⟶ SheafOfModules.free (ULift.{u} (Fin b))),
      q.inverse = sets (localizedNeighborhoods J p n) (J.toGrothendieck.over n.1) ∧
      (∀ (G : Sheaf J.toGrothendieck (Type u)) (z : Over n)
        (s : G.obj.obj (op z.left.1)),
        e.hom.app G
          (colimit.ι ((localizedNeighborhoods J p n).op ⋙ (G.over n.1).obj) (op z) s) =
            p.inverse.map (sitePointSectionHom J G s) z.left.2) ∧
      (∀ (G : ringedSiteModules.{u}
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R))
        (z : Over n) (s : G.val.obj (op z.left.1)),
        (comparison.hom.app G)
          (localizedModuleGerm J p hJ R n (G.over n.1) z s) =
            stalkModuleGerm J p hJ R G z.left s) ∧
      Nonempty ((localizedModules J p hJ R n).obj F ≅ M) ∧
      Nonempty (F ≅ cokernel α) ∧
      (∀ (i : Fin a) (V : Over n.1),
        (SheafOfModules.freeHomEquiv _ α ⟨i⟩).val (op V) =
          ∑ j : Fin b, R.obj.map V.hom.op (A j i) •
            @id ((SheafOfModules.free (R :=
              ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
                (ULift.{u} (Fin b))).val.obj (op V))
              ((SheafOfModules.freeSection (R :=
                ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
                  (I := ULift.{u} (Fin b)) ⟨j⟩).val (op V))) := by
  sorry

end CategoryTheory.SiteFpStalkRealization
