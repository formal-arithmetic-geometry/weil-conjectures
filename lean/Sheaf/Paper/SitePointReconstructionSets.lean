/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Sheaf.CategoryTheory.Sites.SitePointRepresentableEqualizers

/-!
# Reconstruction of a set-valued point from pointed site objects

Source: Stacks Project, Sites, Tags 00YA, 00YB and 00YC
(blueprint: lem-trf-site-point-reconstruction-sets).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

open Limits Opposite

/-- The functor of pointed sheafified representables attached to a geometric morphism.
Source: Stacks Project, Sites, Tag 00YA (blueprint: lem-trf-site-point-reconstruction-sets). -/
noncomputable def sitePointFunctor {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v))) : C ⥤ Type v :=
  yoneda ⋙ presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse

/-- The category of pointed objects of `sitePointFunctor`.
Source: Stacks Project, Sites, Tags 00YB and 00YC
(blueprint: lem-trf-site-point-reconstruction-sets). -/
abbrev sitePointNeighbourhood {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v))) :=
  (sitePointFunctor J p).Elements

/-- The diagram of sections indexed by pointed site objects.
Source: Stacks Project, Sites, Tag 00YA (blueprint: lem-trf-site-point-reconstruction-sets). -/
noncomputable def sitePointSectionDiagram {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v)))
    (F : Sheaf J.toGrothendieck (Type v)) :
    (sitePointNeighbourhood J p)ᵒᵖ ⥤ Type v where
  obj X := F.obj.obj (op X.unop.1)
  map f := F.obj.map f.unop.val.op
  map_id := by
    intro X
    simp
  map_comp := by
    intro X Y Z f g
    simp

/-- The sheaf morphism represented by a section of a sheaf on an object.
Source: Stacks Project, Sites, Tags 00Y6 and 00YA
(blueprint: lem-trf-site-point-reconstruction-sets). -/
noncomputable def sitePointSectionHom {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (F : Sheaf J.toGrothendieck (Type v))
    {U : C} (s : F.obj.obj (op U)) :
    (presheafToSheaf J.toGrothendieck (Type v)).obj (yoneda.obj U) ⟶ F :=
  ((sheafificationAdjunction J.toGrothendieck (Type v)).homEquiv
      (yoneda.obj U) F).symm (yonedaEquiv.symm s)

private noncomputable def sectionEquiv {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (F : Sheaf J.toGrothendieck (Type v)) (U : C) :
    ((presheafToSheaf J.toGrothendieck (Type v)).obj (yoneda.obj U) ⟶ F) ≃
      F.obj.obj (op U) :=
  ((sheafificationAdjunction J.toGrothendieck (Type v)).homEquiv _ _).trans yonedaEquiv

private lemma sectionHom_post {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    {F G : Sheaf J.toGrothendieck (Type v)} (α : F ⟶ G)
    {U : C} (s : F.obj.obj (op U)) :
    sitePointSectionHom J G (α.hom.app (op U) s) = sitePointSectionHom J F s ≫ α := by
  unfold sitePointSectionHom
  rw [← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  exact (yonedaEquiv_symm_naturality_right U α.hom s).symm

private lemma sectionHom_pre {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (F : Sheaf J.toGrothendieck (Type v)) {U V : C} (f : U ⟶ V)
    (s : F.obj.obj (op V)) :
    sitePointSectionHom J F (F.obj.map f.op s) =
      (presheafToSheaf J.toGrothendieck (Type v)).map (yoneda.map f) ≫
        sitePointSectionHom J F s := by
  unfold sitePointSectionHom
  rw [← Adjunction.homEquiv_naturality_left_symm]
  congr 1
  exact (yonedaEquiv_symm_naturality_left f F.obj s).symm

/-- Adjunction and Yoneda identify direct-image sections with functions on pointed objects. -/
private noncomputable def directSectionEquiv {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (E : Type v) (U : C) :
    (p.direct.obj E).obj.obj (op U) ≃ ((sitePointFunctor J p).obj U ⟶ E) :=
  (sectionEquiv J (p.direct.obj E) U).symm.trans (p.adj.homEquiv _ E).symm

private lemma directSectionEquiv_pre {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (E : Type v) {U V : C} (f : U ⟶ V) (s : (p.direct.obj E).obj.obj (op V)) :
    directSectionEquiv J p E U ((p.direct.obj E).obj.map f.op s) =
      (sitePointFunctor J p).map f ≫ directSectionEquiv J p E V s := by
  change (p.adj.homEquiv _ _).symm (sitePointSectionHom J _ _) = _
  rw [sectionHom_pre, Adjunction.homEquiv_naturality_left_symm]
  rfl

private lemma directSectionEquiv_post {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (E : Type v) {F : Sheaf J.toGrothendieck (Type v)} (t : F ⟶ p.direct.obj E)
    (U : C) (s : F.obj.obj (op U)) :
    directSectionEquiv J p E U (t.hom.app (op U) s) =
      p.inverse.map (sitePointSectionHom J F s) ≫ (p.adj.homEquiv F E).symm t := by
  change (p.adj.homEquiv _ _).symm (sitePointSectionHom J _ _) = _
  rw [sectionHom_post, Adjunction.homEquiv_naturality_left_symm]

/-- Separatedness detects a missing point by comparing its characteristic function with zero.
No local representative or universe enlargement is needed. -/
private lemma pointed_cover_surjective {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (I : Type (max u v)) (U : C) (Ui : I → C) (f : ∀ i, Ui i ⟶ U)
    (hf : Presieve.ofArrows Ui f ∈ J U) (x : (sitePointFunctor J p).obj U) :
    ∃ (i : I) (y : (sitePointFunctor J p).obj (Ui i)),
      (sitePointFunctor J p).map (f i) y = x := by
  classical
  by_contra hx
  let a : (sitePointFunctor J p).obj U ⟶ ULift.{v} Bool := ↾fun _ ↦ ⟨false⟩
  let b : (sitePointFunctor J p).obj U ⟶ ULift.{v} Bool :=
    ↾fun z ↦ ⟨if z = x then true else false⟩
  have he : (directSectionEquiv J p _ U).symm a =
      (directSectionEquiv J p _ U).symm b := by
    apply ((isSheaf_iff_isSheaf_of_type _ _).mp (p.direct.obj _).property
      |>.isSheafFor_of_mem_precoverage hf).isSeparatedFor.ext
    intro V g hg
    obtain ⟨i⟩ := hg
    apply (directSectionEquiv J p _ _).injective
    rw [directSectionEquiv_pre, directSectionEquiv_pre,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext y
    have hne : (sitePointFunctor J p).map (f i) y ≠ x := fun h ↦ hx ⟨i, y, h⟩
    simp [a, b, hne]
  have he' := congrArg (fun t ↦ directSectionEquiv J p _ U t x) he
  simp [a, b] at he'

private noncomputable def pointCocone {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (F : Sheaf J.toGrothendieck (Type v)) : Cocone (sitePointSectionDiagram J p F) where
  pt := p.inverse.obj F
  ι.app X := ↾fun s ↦ p.inverse.map (sitePointSectionHom J F s) X.unop.2
  ι.naturality := by
    intro X Y f
    ext s
    change p.inverse.map (sitePointSectionHom J F (F.obj.map f.unop.val.op s))
      Y.unop.2 = p.inverse.map (sitePointSectionHom J F s) X.unop.2
    rw [sectionHom_pre, p.inverse.map_comp]
    change p.inverse.map (sitePointSectionHom J F s)
      ((sitePointFunctor J p).map f.unop.val Y.unop.2) = _
    rw [f.unop.prop]

/-- Curry the cocone legs using the direct-image section equivalence.
Cocone naturality becomes naturality of this sheaf morphism. -/
private noncomputable def coconeTranspose {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (F : Sheaf J.toGrothendieck (Type v)) (c : Cocone (sitePointSectionDiagram J p F)) :
    F ⟶ p.direct.obj c.pt :=
  ⟨{ app := fun U ↦ ↾fun s ↦ (directSectionEquiv J p c.pt U.unop).symm
        (↾fun a ↦ c.ι.app (op ⟨U.unop, a⟩) s)
     naturality := by
       intro U V f
       ext s
       apply (directSectionEquiv J p c.pt V.unop).injective
       change directSectionEquiv J p c.pt V.unop
         ((directSectionEquiv J p c.pt V.unop).symm
           (↾fun a ↦ c.ι.app (op ((sitePointFunctor J p).elementsMk V.unop a))
             (F.obj.map f s))) =
         directSectionEquiv J p c.pt V.unop
           ((p.direct.obj c.pt).obj.map f
             ((directSectionEquiv J p c.pt U.unop).symm
               (↾fun a ↦ c.ι.app (op ((sitePointFunctor J p).elementsMk U.unop a)) s)))
       refine (Equiv.apply_symm_apply _ _).trans ?_
       refine Eq.trans ?_ (directSectionEquiv_pre J p c.pt f.unop _).symm
       rw [Equiv.apply_symm_apply]
       ext a
       exact congrArg (fun t ↦ t s)
         (c.w (CategoryOfElements.homMk ⟨V.unop, a⟩
           ⟨U.unop, (sitePointFunctor J p).map f.unop a⟩ f.unop rfl).op) }⟩

/-- Transposition and the geometric-morphism adjunction supply the universal descent map.
The explicitly chosen vertex stays in `Type v` even for a larger indexing category. -/
private noncomputable def pointCocone_isColimit {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (F : Sheaf J.toGrothendieck (Type v)) : IsColimit (pointCocone J p F) where
  desc c := (p.adj.homEquiv F c.pt).symm (coconeTranspose J p F c)
  fac c X := by
    ext s
    have h := directSectionEquiv_post J p c.pt (coconeTranspose J p F c) X.unop.1 s
    change directSectionEquiv J p c.pt X.unop.1
      ((directSectionEquiv J p c.pt X.unop.1).symm
        (↾fun a ↦ c.ι.app (op ((sitePointFunctor J p).elementsMk X.unop.1 a)) s)) = _ at h
    rw [Equiv.apply_symm_apply] at h
    exact (congrArg (fun t ↦ t X.unop.2) h).symm
  uniq c m hm := by
    change p.inverse.obj F ⟶ c.pt at m
    apply (p.adj.homEquiv F c.pt).injective
    rw [Equiv.apply_symm_apply]
    apply Sheaf.hom_ext
    ext U s
    apply (directSectionEquiv J p c.pt U.unop).injective
    refine (directSectionEquiv_post J p c.pt (p.adj.homEquiv F c.pt m) U.unop s).trans ?_
    rw [Equiv.symm_apply_apply]
    change p.inverse.map (sitePointSectionHom J F s) ≫ m =
      (directSectionEquiv J p c.pt U.unop)
        ((directSectionEquiv J p c.pt U.unop).symm
          (↾fun a ↦ c.ι.app (op ((sitePointFunctor J p).elementsMk U.unop a)) s))
    rw [Equiv.apply_symm_apply]
    ext a
    exact congrArg (fun t ↦ t s) (hm (op ⟨U.unop, a⟩))

/-- The representable terminal presheaf is already a sheaf, so its reflection is unchanged. -/
private lemma point_preservesTerminal {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasFiniteLimits C]
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v))) :
    PreservesLimit (Functor.empty.{0} C) (sitePointFunctor J p) := by
  have := p.leftExact
  let S := presheafToSheaf J.toGrothendieck (Type v)
  let R := sheafToPresheaf J.toGrothendieck (Type v)
  have ht := terminalIsTerminal.isTerminalObj yoneda (⊤_ C)
  have hs : Presheaf.IsSheaf J.toGrothendieck (yoneda.obj (⊤_ C)) :=
    (Presheaf.isSheaf_of_iso_iff
      (ht.uniqueUpToIso (terminalIsTerminal.isTerminalObj R _))).mpr
        (⊤_ (Sheaf J.toGrothendieck (Type v))).property
  have : IsIso (toSheafify J.toGrothendieck (yoneda.obj (⊤_ C))) :=
    isIso_toSheafify _ hs
  have ht' : IsTerminal (R.obj (S.obj (yoneda.obj (⊤_ C)))) :=
    ht.ofIso (asIso (toSheafify J.toGrothendieck (yoneda.obj (⊤_ C))))
  have ht'' := ht'.isTerminalOfObj R (S.obj (yoneda.obj (⊤_ C)))
  exact preservesTerminal_of_iso _
    ((ht''.isTerminalObj p.inverse _).uniqueUpToIso terminalIsTerminal)

/- The internal Hom into `p.direct E` is v-small by the composite adjunction,
even when the site objects live in a larger universe. Shrinking it gives a sheaf
that detects stability of weak equivalences under products. This proves binary
product preservation without assuming left-exact sheafification. -/
namespace BinaryProductProof

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

private def pointwiseProduct (F G : Cᵒᵖ ⥤ Type v) : Cᵒᵖ ⥤ Type v where
  obj X := F.obj X × G.obj X
  map f := ↾fun s ↦ (F.map f s.1, G.map f s.2)
  map_id X := by ext s <;> simp
  map_comp f g := by ext s <;> simp

private def localHomEquiv (P G : Cᵒᵖ ⥤ Type v) (U : C) :
    (presheafHom P G).obj (op U) ≃ (pointwiseProduct (yoneda.obj U) P ⟶ G) where
  toFun α :=
    { app V := ↾fun x ↦ α.app (op (Over.mk x.1)) x.2
      naturality V W f := by
        ext ⟨g, x⟩
        exact congrArg (fun h ↦ h x) (α.naturality
          (Over.homMk f.unop : Over.mk (f.unop ≫ g) ⟶ Over.mk g).op) }
  invFun β :=
    { app V := ↾fun x ↦ β.app (op V.unop.left) (V.unop.hom, x)
      naturality V W f := by
        ext x
        have h := congrArg (fun k ↦ k (V.unop.hom, x))
          (β.naturality f.unop.left.op)
        simpa [pointwiseProduct, Over.w f.unop] using h }
  left_inv α := by rfl
  right_inv β := by rfl

private lemma localHom_small (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) (E : Type v) (U : C) :
    Small.{v} ((presheafHom P (p.direct.obj E).obj).obj (op U)) := by
  let D := pointwiseProduct (yoneda.obj U) P
  let e : (D ⟶ (p.direct.obj E).obj) ≃
      (p.inverse.obj ((presheafToSheaf J.toGrothendieck (Type v)).obj D) ⟶ E) :=
    ((sheafificationAdjunction J.toGrothendieck (Type v)).homEquiv D _).symm.trans
      (p.adj.homEquiv _ E).symm
  exact small_of_injective ((localHomEquiv P (p.direct.obj E).obj U).trans e).injective

private noncomputable def smallHom (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) (E : Type v) : Cᵒᵖ ⥤ Type v := by
  let H := presheafHom P (p.direct.obj E).obj
  letI (X : Cᵒᵖ) : Small.{v} (H.obj X) := localHom_small J p P E X.unop
  exact FunctorToTypes.shrink H

private lemma smallHom_isSheaf (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) (E : Type v) :
    Presheaf.IsSheaf J.toGrothendieck (smallHom J p P E) := by
  let H := presheafHom P (p.direct.obj E).obj
  have (X : Cᵒᵖ) : Small.{v} (H.obj X) := localHom_small J p P E X.unop
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf J.toGrothendieck (FunctorToTypes.shrink H)
  rw [Presieve.isSheaf_iff_of_nat_equiv (fun X ↦ (equivShrink (H.obj (op X))).symm)
    (by intros; simp)]
  exact (isSheaf_iff_isSheaf_of_type _ _).mp ((p.direct.obj E).property.hom P)

private noncomputable def smallHomEquiv (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) (E : Type v) (U : C) :
    (smallHom J p P E).obj (op U) ≃
      (presheafHom P (p.direct.obj E).obj).obj (op U) := by
  letI := localHom_small J p P E U
  exact (equivShrink _).symm

private lemma smallHomEquiv_map (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) (E : Type v) {U V : C} (f : U ⟶ V)
    (x : (smallHom J p P E).obj (op V)) :
    smallHomEquiv J p P E U ((smallHom J p P E).map f.op x) =
      (presheafHom P (p.direct.obj E).obj).map f.op (smallHomEquiv J p P E V x) := by
  simp [smallHomEquiv, smallHom]

private def curryLocal (P H G : Cᵒᵖ ⥤ Type v) (α : pointwiseProduct P H ⟶ G)
    (U : C) (x : H.obj (op U)) : (presheafHom P G).obj (op U) where
  app V := ↾fun z ↦ α.app (op V.unop.left) (z, H.map V.unop.hom.op x)
  naturality V W f := by
    ext z
    have h := congrArg (fun k ↦ k (z, H.map V.unop.hom.op x))
      (α.naturality f.unop.left.op)
    change α.app (op W.unop.left)
        (P.map f.unop.left.op z, H.map W.unop.hom.op x) =
      G.map f.unop.left.op (α.app (op V.unop.left) (z, H.map V.unop.hom.op x))
    have he : H.map W.unop.hom.op x =
        H.map f.unop.left.op (H.map V.unop.hom.op x) := by
      rw [← Functor.map_comp_apply, ← op_comp, Over.w]
    rw [he]
    exact h

private lemma curryLocal_map (P H G : Cᵒᵖ ⥤ Type v) (α : pointwiseProduct P H ⟶ G)
    {U V : C} (f : U ⟶ V) (x : H.obj (op V)) :
    curryLocal P H G α U (H.map f.op x) =
      (presheafHom P G).map f.op (curryLocal P H G α V x) := by
  apply NatTrans.ext
  funext W
  ext z
  change α.app _ (z, H.map _ (H.map f.op x)) = α.app _ (z, H.map _ x)
  rw [← Functor.map_comp_apply]
  rfl

private noncomputable def curryMap (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P H : Cᵒᵖ ⥤ Type v) (E : Type v)
    (α : pointwiseProduct P H ⟶ (p.direct.obj E).obj) : H ⟶ smallHom J p P E where
  app U := ↾fun x ↦ (smallHomEquiv J p P E U.unop).symm
    (curryLocal P H _ α U.unop x)
  naturality U V f := by
    ext x
    change (smallHomEquiv J p P E V.unop).symm
        (curryLocal P H _ α V.unop (H.map f x)) =
      (smallHom J p P E).map f ((smallHomEquiv J p P E U.unop).symm
        (curryLocal P H _ α U.unop x))
    apply (smallHomEquiv J p P E V.unop).injective
    have he := smallHomEquiv_map J p P E f.unop
      ((smallHomEquiv J p P E U.unop).symm (curryLocal P H _ α U.unop x))
    simp only [Quiver.Hom.op_unop, Equiv.apply_symm_apply] at he
    exact (Equiv.apply_symm_apply _ _).trans
      ((curryLocal_map P H _ α f.unop x).trans he.symm)

private noncomputable def uncurryMap (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P H : Cᵒᵖ ⥤ Type v) (E : Type v)
    (β : H ⟶ smallHom J p P E) : pointwiseProduct P H ⟶ (p.direct.obj E).obj where
  app U := ↾fun x ↦ (smallHomEquiv J p P E U.unop (β.app U x.2)).app
    (op (Over.mk (𝟙 U.unop))) x.1
  naturality U V f := by
    ext ⟨z, x⟩
    have hb := congrArg (smallHomEquiv J p P E V.unop) (β.naturality_apply f x)
    have he := smallHomEquiv_map J p P E f.unop (β.app U x)
    simp only [Quiver.Hom.op_unop] at he
    have hb' := hb.trans he
    change (smallHomEquiv J p P E V.unop (β.app V (H.map f x))).app
        (op (Over.mk (𝟙 V.unop))) (P.map f z) =
      (p.direct.obj E).obj.map f
        ((smallHomEquiv J p P E U.unop (β.app U x)).app
          (op (Over.mk (𝟙 U.unop))) z)
    rw [hb']
    have hv := presheafHom_map_app_op_mk_id f.unop
      (smallHomEquiv J p P E U.unop (β.app U x))
    simp only [Quiver.Hom.op_unop] at hv
    refine (congrArg (fun k ↦ k (P.map f z)) hv).trans ?_
    exact congrArg (fun k ↦ k z)
      ((smallHomEquiv J p P E U.unop (β.app U x)).naturality
        (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op)

private noncomputable def curryEquiv (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P H : Cᵒᵖ ⥤ Type v) (E : Type v) :
    (pointwiseProduct P H ⟶ (p.direct.obj E).obj) ≃ (H ⟶ smallHom J p P E) where
  toFun := curryMap J p P H E
  invFun := uncurryMap J p P H E
  left_inv α := by
    ext U ⟨z, x⟩
    simp [curryMap, uncurryMap, curryLocal]
  right_inv β := by
    ext U x
    apply (smallHomEquiv J p P E U.unop).injective
    simp only [curryMap, TypeCat.hom_ofHom,
      Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext V
    ext z
    change (smallHomEquiv J p P E V.unop.left
        (β.app (op V.unop.left) (H.map V.unop.hom.op x))).app
          (op (Over.mk (𝟙 V.unop.left))) z =
      (smallHomEquiv J p P E U.unop (β.app U x)).app V z
    have hb := congrArg (smallHomEquiv J p P E V.unop.left)
      (β.naturality_apply V.unop.hom.op x)
    have he := smallHomEquiv_map J p P E V.unop.hom (β.app U x)
    have heval := congrArg (fun k ↦ k.app (op (Over.mk (𝟙 V.unop.left))) z)
      (hb.trans he)
    have hv := presheafHom_map_app_op_mk_id V.unop.hom
      (smallHomEquiv J p P E U.unop (β.app U x))
    exact heval.trans (congrArg (fun k ↦ k z) hv)

private def productMapRight (P : Cᵒᵖ ⥤ Type v) {H H' : Cᵒᵖ ⥤ Type v} (f : H ⟶ H') :
    pointwiseProduct P H ⟶ pointwiseProduct P H' where
  app U := ↾fun x ↦ (x.1, f.app U x.2)
  naturality U V g := by
    ext ⟨z, x⟩
    exact congrArg (fun y ↦ (P.map g z, y)) (f.naturality_apply g x)

private lemma curryMap_pre (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) {H H' : Cᵒᵖ ⥤ Type v} (E : Type v) (f : H ⟶ H')
    (α : pointwiseProduct P H' ⟶ (p.direct.obj E).obj) :
    curryMap J p P H E (productMapRight P f ≫ α) = f ≫ curryMap J p P H' E α := by
  ext U x
  change (smallHomEquiv J p P E U.unop).symm
      (curryLocal P H _ (productMapRight P f ≫ α) U.unop x) =
    (smallHomEquiv J p P E U.unop).symm
      (curryLocal P H' _ α U.unop (f.app U x))
  apply congrArg (smallHomEquiv J p P E U.unop).symm
  apply NatTrans.ext
  funext V
  ext z
  change α.app _ (z, f.app _ (H.map V.unop.hom.op x)) =
    α.app _ (z, H'.map V.unop.hom.op (f.app U x))
  exact congrArg (fun y ↦ α.app (op V.unop.left) (z, y))
    (f.naturality_apply V.unop.hom.op x)

private lemma relative_product_local_iso (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) {H H' : Cᵒᵖ ⥤ Type v} (f : H ⟶ H')
    (hf : J.toGrothendieck.W f) :
    IsIso ((presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse).map
      (productMapRight P f)) := by
  apply isIso_of_coyoneda_map_bijective
  intro E
  rw [(sheafificationAdjunction J.toGrothendieck (Type v)).comp p.adj
    |>.map_comp_bijective_iff]
  have hw := hf (smallHom J p P E) (smallHom_isSheaf J p P E)
  let e := curryEquiv J p P H E
  let e' := curryEquiv J p P H' E
  rw [← Function.Bijective.of_comp_iff' e.bijective,
    ← Function.Bijective.of_comp_iff _ e'.symm.bijective]
  convert hw using 1
  funext α
  change curryMap J p P H E (productMapRight P f ≫ e'.symm α) = f ≫ α
  rw [curryMap_pre]
  change f ≫ (e' (e'.symm α)) = _
  rw [Equiv.apply_symm_apply]

private lemma relative_whiskerLeft_local_iso (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) {H H' : Cᵒᵖ ⥤ Type v} (f : H ⟶ H')
    (hf : J.toGrothendieck.W f) :
    IsIso ((presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse).map (P ◁ f)) := by
  exact relative_product_local_iso J p P f hf

private lemma relative_whiskerRight_local_iso (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (P : Cᵒᵖ ⥤ Type v) {H H' : Cᵒᵖ ⥤ Type v} (f : H ⟶ H')
    (hf : J.toGrothendieck.W f) :
    IsIso ((presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse).map (f ▷ P)) := by
  let T := presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse
  have : IsIso (T.map (P ◁ f)) := relative_whiskerLeft_local_iso J p P f hf
  have h : f ▷ P = (β_ H P).hom ≫ (P ◁ f) ≫ (β_ H' P).inv := by
    ext U ⟨x, y⟩ <;> rfl
  rw [h, T.map_comp, T.map_comp]
  infer_instance

private lemma relative_units_tensor_iso (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v)))
    (F G : Cᵒᵖ ⥤ Type v) :
    IsIso ((presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse).map
      (toSheafify J.toGrothendieck F ⊗ₘ toSheafify J.toGrothendieck G)) := by
  let T := presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse
  have : IsIso (T.map (toSheafify J.toGrothendieck F ▷ G)) :=
    relative_whiskerRight_local_iso J p G _ (J.toGrothendieck.W_toSheafify F)
  have : IsIso (T.map (sheafify J.toGrothendieck F ◁ toSheafify J.toGrothendieck G)) :=
    relative_whiskerLeft_local_iso J p _ _ (J.toGrothendieck.W_toSheafify G)
  rw [tensorHom_def, T.map_comp]
  infer_instance

private lemma sheafification_tensor_comparison (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (F G : Cᵒᵖ ⥤ Type v) :
    (presheafToSheaf J.toGrothendieck (Type v)).map
        (toSheafify J.toGrothendieck F ⊗ₘ toSheafify J.toGrothendieck G) ≫
      (sheafificationAdjunction J.toGrothendieck (Type v)).counit.app
        ((presheafToSheaf J.toGrothendieck (Type v)).obj F ⊗
          (presheafToSheaf J.toGrothendieck (Type v)).obj G) =
      CartesianMonoidalCategory.prodComparison (presheafToSheaf J.toGrothendieck (Type v)) F G := by
  let S := presheafToSheaf J.toGrothendieck (Type v)
  let R := sheafToPresheaf J.toGrothendieck (Type v)
  let adj := sheafificationAdjunction J.toGrothendieck (Type v)
  apply CartesianMonoidalCategory.hom_ext
  · have hn : S.map (R.map (fst (S.obj F) (S.obj G))) ≫ adj.counit.app (S.obj F) =
        adj.counit.app (S.obj F ⊗ S.obj G) ≫ fst (S.obj F) (S.obj G) := by
      simpa only [Functor.comp_map, Functor.id_map] using
        adj.counit.naturality (fst (S.obj F) (S.obj G))
    rw [Category.assoc, ← hn, ← Category.assoc, ← S.map_comp]
    have h : (toSheafify J.toGrothendieck F ⊗ₘ toSheafify J.toGrothendieck G) ≫
        R.map (fst (S.obj F) (S.obj G)) = fst F G ≫ toSheafify J.toGrothendieck F := by
      ext U ⟨x, y⟩; rfl
    rw [h, S.map_comp, Category.assoc, adj.left_triangle_components]
    simp only [CartesianMonoidalCategory.prodComparison_fst]
    exact Category.comp_id _
  · have hn : S.map (R.map (snd (S.obj F) (S.obj G))) ≫ adj.counit.app (S.obj G) =
        adj.counit.app (S.obj F ⊗ S.obj G) ≫ snd (S.obj F) (S.obj G) := by
      simpa only [Functor.comp_map, Functor.id_map] using
        adj.counit.naturality (snd (S.obj F) (S.obj G))
    rw [Category.assoc, ← hn, ← Category.assoc, ← S.map_comp]
    have h : (toSheafify J.toGrothendieck F ⊗ₘ toSheafify J.toGrothendieck G) ≫
        R.map (snd (S.obj F) (S.obj G)) = snd F G ≫ toSheafify J.toGrothendieck G := by
      ext U ⟨x, y⟩; rfl
    rw [h, S.map_comp, Category.assoc, adj.left_triangle_components]
    simp only [CartesianMonoidalCategory.prodComparison_snd]
    exact Category.comp_id _

private lemma relative_preservesBinaryProducts (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v))) :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse) := by
  have := p.leftExact
  let S := presheafToSheaf J.toGrothendieck (Type v)
  let T := S ⋙ p.inverse
  have hc (F G : Cᵒᵖ ⥤ Type v) :
      IsIso (p.inverse.map (CartesianMonoidalCategory.prodComparison S F G)) := by
    rw [← sheafification_tensor_comparison J F G, p.inverse.map_comp]
    have : IsIso (p.inverse.map (S.map
        (toSheafify J.toGrothendieck F ⊗ₘ toSheafify J.toGrothendieck G))) :=
      relative_units_tensor_iso J p F G
    infer_instance
  have (F G : Cᵒᵖ ⥤ Type v) :
      IsIso (CartesianMonoidalCategory.prodComparison T F G) := by
    rw [CartesianMonoidalCategory.prodComparison_comp]
    have := hc F G
    infer_instance
  exact
    CartesianMonoidalCategory.preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison T

private lemma representable_preservesBinaryProducts (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v) (Sheaf J.toGrothendieck (Type v))) :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (yoneda ⋙ presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse) := by
  have := relative_preservesBinaryProducts J p
  infer_instance

end BinaryProductProof

/-- Set-valued site-point reconstruction from sheafified representables.
Source: Stacks Project, Sites, Tags 00YA (lemma-point-site-topos (2)), 00YB
(lemma-neighbourhoods-directed), and 00YC (proposition-point-limits)
(blueprint: lem-trf-site-point-reconstruction-sets).

Proof: terminal preservation is proved directly using the already-sheaf terminal
representable. The composite adjunction makes internal Homs into a direct-image
sheaf small; currying then proves binary-product preservation. Combine these with
the separate equalizer step of 00YA (2) and Mathlib's cofiltered-elements theorem.
For a covering, transpose a hypothetical
missing point's Boolean characteristic function into a direct-image sheaf; its
separatedness forces that function to equal zero, a contradiction. For the colimit,
curry the cocone legs into a map to the direct-image sheaf and transpose through
the adjunction. Naturality and uniqueness follow from the two adjunctions and Yoneda.

The fourth clause says that the colimit `c` of the sections over pointed objects exists
(in `Type v`, with no `HasColimit` hypothesis, which is not automatic when the objects of
the site lie in a larger universe than `v`) and that the canonical map `e.hom` from it,
`(U, a, s) ↦ p⁻¹(s)(a)`, is a bijection.
-/
theorem site_point_reconstruction_sets {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    [HasFiniteLimits C]
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v))) :
    PreservesFiniteLimits (sitePointFunctor J p) ∧
      (∀ (I : Type (max u v)) (U : C) (Ui : I → C)
        (f : ∀ i, Ui i ⟶ U),
        Presieve.ofArrows Ui f ∈ J U →
          ∀ x : (sitePointFunctor J p).obj U,
            ∃ (i : I) (y : (sitePointFunctor J p).obj (Ui i)),
              (sitePointFunctor J p).map (f i) y = x) ∧
      IsCofiltered (sitePointNeighbourhood J p) ∧
      (∀ (F : Sheaf J.toGrothendieck (Type v)),
        ∃ (c : Cocone (sitePointSectionDiagram J p F))
          (e : c.pt ≅ p.inverse.obj F),
          Nonempty (IsColimit c) ∧
          (∀ (U : C) (a : (sitePointFunctor J p).obj U)
            (s : F.obj.obj (op U)),
            e.hom (c.ι.app (Opposite.op ⟨U, a⟩) s) =
              (p.inverse.map (sitePointSectionHom J F s)) a)) ∧
      (∀ (F G : Sheaf J.toGrothendieck (Type v)) (α : F ⟶ G)
        (U : C) (s : F.obj.obj (op U)),
        sitePointSectionHom J G ((Sheaf.homEquiv α).app (op U) s) =
          sitePointSectionHom J F s ≫ α) := by
  have hlex : PreservesFiniteLimits (sitePointFunctor J p) := by
    have := point_preservesTerminal J p
    have := preservesLimitsOfShape_pempty_of_preservesTerminal (sitePointFunctor J p)
    have : PreservesLimitsOfShape (Discrete WalkingPair) (sitePointFunctor J p) :=
      BinaryProductProof.representable_preservesBinaryProducts J p
    have : PreservesFiniteProducts (sitePointFunctor J p) :=
      .of_preserves_binary_and_terminal _
    have : PreservesLimitsOfShape WalkingParallelPair (sitePointFunctor J p) :=
      sitePoint_representable_preservesEqualizers J hJ p
    exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _
  have := hlex
  refine ⟨hlex, pointed_cover_surjective J p, Functor.isCofiltered_elements _, ?_, ?_⟩
  · intro F
    exact ⟨pointCocone J p F, Iso.refl _, ⟨pointCocone_isColimit J p F⟩,
      fun _ _ _ ↦ rfl⟩
  · intro F G α U s
    exact sectionHom_post J α s


end CategoryTheory
