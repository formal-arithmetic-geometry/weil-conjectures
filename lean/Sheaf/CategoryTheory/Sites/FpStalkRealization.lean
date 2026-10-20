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
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

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

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


universe u v

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

section Proofs

private theorem fastRingSheafCompose {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) :
    K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  hasSheafCompose_of_preservesLimitsOfSize K

attribute [local instance 20000] fastRingSheafCompose


private theorem fastAbelianSheafify {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) : HasSheafify K AddCommGrpCat.{u} := by
  infer_instance

private theorem fastSetSheafify {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) : HasSheafify K (Type u) := by
  infer_instance

private theorem fastRingAbCompose {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) :
    K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  hasSheafCompose_of_preservesLimitsOfSize K

private theorem fastAbSetCompose {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) : K.HasSheafCompose (forget AddCommGrpCat.{u}) :=
  hasSheafCompose_of_preservesLimitsOfSize K

attribute [local instance 20000] fastAbelianSheafify fastSetSheafify
  fastRingAbCompose fastAbSetCompose

omit [HasFiniteLimits C] in
private def finiteFreeIso (S : Type u) [Ring S] (b : ℕ) :
    (ModuleCat.free S).obj (ULift.{u} (Fin b)) ≅ ModuleCat.of S (Fin b → S) :=
  (Finsupp.domLCongr Equiv.ulift ≪≫ₗ Finsupp.linearEquivFunOnFinite S S (Fin b)).toModuleIso

omit [HasFiniteLimits C] in
private theorem finiteFreeIso_basis (S : Type u) [Ring S] (b : ℕ) (i : Fin b) :
    (finiteFreeIso S b).hom (ModuleCat.freeMk ⟨i⟩) = Pi.single i 1 := by
  classical
  change (Finsupp.linearEquivFunOnFinite S S (Fin b))
    ((Finsupp.domLCongr Equiv.ulift : (ULift.{u} (Fin b) →₀ S) ≃ₗ[S] _)
      (Finsupp.single ⟨i⟩ 1)) = _
  rw [Finsupp.domLCongr_single, Finsupp.linearEquivFunOnFinite_single]
  rfl

omit [HasFiniteLimits C] in
private theorem linearMapConjugacy (S : Type u) [Ring S]
    {P Q : ModuleCat.{u} S} (f : P ⟶ Q) (a b : ℕ)
    (ea : (ModuleCat.free S).obj (ULift.{u} (Fin a)) ≅ P)
    (eb : (ModuleCat.free S).obj (ULift.{u} (Fin b)) ≅ Q)
    (g : (Fin a → S) →ₗ[S] (Fin b → S))
    (h : ∀ i : Fin a, f (ea.hom (ModuleCat.freeMk ⟨i⟩)) =
      ∑ j : Fin b, g (Pi.single i 1) j • @id Q (eb.hom (ModuleCat.freeMk ⟨j⟩))) :
    f ≫ (eb.symm ≪≫ finiteFreeIso S b).hom =
      (ea.symm ≪≫ finiteFreeIso S a).hom ≫ ModuleCat.ofHom g := by
  classical
  apply (cancel_epi ea.hom).1
  apply ModuleCat.free_hom_ext
  rintro ⟨i⟩
  change (finiteFreeIso S b).hom.hom (eb.inv.hom (f (ea.hom (ModuleCat.freeMk ⟨i⟩)))) =
    g ((finiteFreeIso S a).hom (ea.inv (ea.hom (ModuleCat.freeMk ⟨i⟩))))
  rw [ModuleCat.inv_hom_apply, finiteFreeIso_basis, h]
  simp only [map_sum, map_smul]
  have hu (j : Fin b) : (finiteFreeIso S b).hom.hom (ModuleCat.freeMk ⟨j⟩) =
      Pi.single j 1 := finiteFreeIso_basis S b j
  ext j
  simp [hu, Pi.single_apply]



omit [HasFiniteLimits C] in
private def presentationCokernelIso (S : Type u) [Ring S]
    {D : Type v} [Category.{u} D] [HasZeroMorphisms D]
    (T : D ⥤ ModuleCat.{u} S) [T.PreservesZeroMorphisms]
    {P Q : D} (α : P ⟶ Q) [HasCokernel α]
    [PreservesColimit (parallelPair α 0) T]
    {a b : ℕ} {M : ModuleCat.{u} S}
    (f : (Fin b → S) →ₗ[S] M) (g : (Fin a → S) →ₗ[S] (Fin b → S))
    (hf : Function.Surjective f) (hgf : Function.Exact g f)
    (ep : T.obj P ≅ ModuleCat.of S (Fin a → S))
    (eq : T.obj Q ≅ ModuleCat.of S (Fin b → S))
    (w : T.map α ≫ eq.hom = ep.hom ≫ ModuleCat.ofHom g) :
    T.obj (cokernel α) ≅ M := by
  let hc := ModuleCat.isColimitCokernelCofork (ModuleCat.ofHom g) (ModuleCat.ofHom f) hgf hf
  exact PreservesCokernel.iso T α ≪≫
    cokernel.mapIso (T.map α) (ModuleCat.ofHom g) ep eq w ≪≫
      (cokernelIsCokernel (ModuleCat.ofHom g)).coconePointUniqueUpToIso hc

omit [HasFiniteLimits C] in
private def colimitOverMap {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R}
    (hc : IsColimit c) (n : N) [InitiallySmall.{u} (Over n)]
    (M : PresheafOfModules.{u} R) :
    (PresheafOfModules.colimitFunctor
      ((Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc)).obj
        ((PresheafOfModules.pushforward₀ (Over.forget n) R).obj M) ⟶
      (PresheafOfModules.colimitFunctor hc).obj M := by
  let hc' := (Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc
  let P := (PresheafOfModules.pushforward₀ (Over.forget n) R).obj M
  let e : colimit P.presheaf ≅ colimit M.presheaf :=
    Functor.Final.colimitIso (Over.forget n).op M.presheaf
  refine ConcreteCategory.ofHom (C := ModuleCat c.pt)
    (X := (PresheafOfModules.colimitFunctor hc').obj P)
    (Y := (PresheafOfModules.colimitFunctor hc).obj M)
    { toFun := e.hom
      map_add' := fun x y ↦ e.hom.hom.map_add x y
      map_smul' := ?_ }
  intro r m
  obtain ⟨z, a, t, rfl, rfl⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (M := P) (hcR := hc') (hcM := colimit.isColimit P.presheaf) r m
  have he (t : M.obj (op z.unop.left)) :
      e.hom (PresheafOfModules.ModuleColimit.ιM
        (hcR := hc') (hcM := colimit.isColimit P.presheaf) t) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hc) (hcM := colimit.isColimit M.presheaf) t :=
    ConcreteCategory.congr_hom
      (Functor.Final.ι_colimitIso_hom (Over.forget n).op M.presheaf z) t
  rw [PresheafOfModules.ModuleColimit.smul_eq]
  exact (he (a • t)).trans
    ((PresheafOfModules.ModuleColimit.smul_eq hc
      (colimit.isColimit M.presheaf) (U := op z.unop.left) a t).symm.trans
        (congrArg (fun m : (PresheafOfModules.colimitFunctor hc).obj M ↦
          (c.ι.app (op z.unop.left) a) • m) (he t).symm))

omit [HasFiniteLimits C] in
private theorem colimitOverMap_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R}
    (hc : IsColimit c) (n : N) [InitiallySmall.{u} (Over n)]
    (M : PresheafOfModules.{u} R) (z : Over n) (t : M.obj (op z.left)) :
    colimitOverMap R hc n M
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := (Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc)
        (hcM := colimit.isColimit
          ((PresheafOfModules.pushforward₀ (Over.forget n) R).obj M).presheaf) t) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hc) (hcM := colimit.isColimit M.presheaf) t := by
  exact ConcreteCategory.congr_hom
    (Functor.Final.ι_colimitIso_hom (Over.forget n).op M.presheaf (op z)) t

omit [HasFiniteLimits C] in
private theorem colimitOverMap_bijective {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R}
    (hc : IsColimit c) (n : N) [InitiallySmall.{u} (Over n)]
    (M : PresheafOfModules.{u} R) : Function.Bijective (colimitOverMap R hc n M) := by
  exact ConcreteCategory.bijective_of_isIso
    (Functor.Final.colimitIso (Over.forget n).op M.presheaf).hom

omit [HasFiniteLimits C] in
private def colimitOverComparison {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R}
    (hc : IsColimit c) (n : N) [InitiallySmall.{u} (Over n)] :
    PresheafOfModules.pushforward₀ (Over.forget n) R ⋙
      PresheafOfModules.colimitFunctor
        ((Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc) ≅
      PresheafOfModules.colimitFunctor hc := by
  have hi (M : PresheafOfModules.{u} R) : IsIso (colimitOverMap R hc n M) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (colimitOverMap_bijective R hc n M)
  refine NatIso.ofComponents (fun M ↦ asIso (colimitOverMap R hc n M)) ?_
  intro M M' f
  apply (forget₂ (ModuleCat c.pt) AddCommGrpCat).map_injective
  exact (Functor.Final.colimIso (Over.forget n).op).hom.naturality
    ((PresheafOfModules.toPresheaf R).map f)

omit [HasFiniteLimits C] in
private theorem colimitOverComparison_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R}
    (hc : IsColimit c) (n : N) [InitiallySmall.{u} (Over n)]
    (M : PresheafOfModules.{u} R) (z : Over n) (t : M.obj (op z.left)) :
    (colimitOverComparison R hc n).hom.app M
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := (Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc)
        (hcM := colimit.isColimit
          ((PresheafOfModules.pushforward₀ (Over.forget n) R).obj M).presheaf) t) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hc) (hcM := colimit.isColimit M.presheaf) t := by
  exact colimitOverMap_germ R hc n M z t

attribute [irreducible] colimitOverMap colimitOverComparison

omit [HasFiniteLimits C] in
private def colimitUnitMap {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R} (hc : IsColimit c) :
    (PresheafOfModules.colimitFunctor hc).obj (PresheafOfModules.unit R) ⟶
      ModuleCat.of c.pt c.pt := by
  let cA := (forget₂ RingCat AddCommGrpCat).mapCocone c
  let hA := isColimitOfPreserves (forget₂ RingCat AddCommGrpCat) hc
  let e := colimit.isoColimitCocone ⟨cA, hA⟩
  let M := PresheafOfModules.unit R
  refine ConcreteCategory.ofHom (C := ModuleCat c.pt)
    (X := (PresheafOfModules.colimitFunctor hc).obj M) (Y := ModuleCat.of c.pt c.pt)
    { toFun := fun m ↦ e.hom m
      map_add' := fun x y ↦ e.hom.hom.map_add x y
      map_smul' := ?_ }
  intro r m
  obtain ⟨z, a, t, rfl, rfl⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₂
      (M := M) (hcR := hc) (hcM := colimit.isColimit M.presheaf) r m
  have he (t : R.obj z) :
      e.hom (PresheafOfModules.ModuleColimit.ιM
        (hcR := hc) (hcM := colimit.isColimit M.presheaf) t) = c.ι.app z t :=
    ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom ⟨cA, hA⟩ z) t
  rw [PresheafOfModules.ModuleColimit.smul_eq]
  exact (he (a • t)).trans ((c.ι.app z).hom.map_mul a t |>.trans
    (congrArg (fun t : c.pt ↦ @Mul.mul c.pt inferInstance (c.ι.app z a) t) (he t).symm))

omit [HasFiniteLimits C] in
private theorem colimitUnitMap_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R} (hc : IsColimit c)
    (z : Nᵒᵖ) (t : R.obj z) :
    colimitUnitMap R hc (PresheafOfModules.ModuleColimit.ιM
      (hcR := hc) (hcM := colimit.isColimit (PresheafOfModules.unit R).presheaf) t) =
        c.ι.app z t := by
  let cA := (forget₂ RingCat AddCommGrpCat).mapCocone c
  let hA := isColimitOfPreserves (forget₂ RingCat AddCommGrpCat) hc
  exact ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom ⟨cA, hA⟩ z) t

omit [HasFiniteLimits C] in
private def colimitUnitIso {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R} (hc : IsColimit c) :
    (PresheafOfModules.colimitFunctor hc).obj (PresheafOfModules.unit R) ≅
      ModuleCat.of c.pt c.pt := by
  let cA := (forget₂ RingCat AddCommGrpCat).mapCocone c
  let hA := isColimitOfPreserves (forget₂ RingCat AddCommGrpCat) hc
  have : IsIso (colimitUnitMap R hc) := (ConcreteCategory.isIso_iff_bijective _).2
    (ConcreteCategory.bijective_of_isIso (colimit.isoColimitCocone ⟨cA, hA⟩).hom)
  exact asIso (colimitUnitMap R hc)

omit [HasFiniteLimits C] in
private theorem colimitUnitIso_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N] (R : Nᵒᵖ ⥤ RingCat.{u}) {c : Cocone R} (hc : IsColimit c)
    (z : Nᵒᵖ) (t : R.obj z) :
    (colimitUnitIso R hc).hom (PresheafOfModules.ModuleColimit.ιM
      (hcR := hc) (hcM := colimit.isColimit (PresheafOfModules.unit R).presheaf) t) =
        c.ι.app z t := by
  exact colimitUnitMap_germ R hc z t

attribute [irreducible] colimitUnitMap colimitUnitIso

omit [HasFiniteLimits C] in
private theorem colimit_matrix_lift {N : Type u} [SmallCategory N] [IsFiltered N]
    (D : N ⥤ RingCat.{u}) {a b : ℕ} (A : Fin b → Fin a → (colimit D : RingCat.{u})) :
    ∃ (n : N) (B : Fin b → Fin a → D.obj n),
      ∀ j i, colimit.ι D n (B j i) = A j i := by
  classical
  have h (ji : Fin b × Fin a) := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) (colimit.isColimit D)) (A ji.1 ji.2)
  choose z t ht using h
  obtain ⟨n, hn⟩ := IsFiltered.sup_objs_exists (Finset.univ.image z)
  have hf (ji : Fin b × Fin a) : Nonempty (z ji ⟶ n) :=
    hn (Finset.mem_image.mpr ⟨ji, Finset.mem_univ _, rfl⟩)
  let f := fun ji ↦ (hf ji).some
  refine ⟨n, (fun j i ↦ D.map (f (j, i)) (t (j, i))), ?_⟩
  intro j i
  exact (ConcreteCategory.congr_hom (colimit.w D (f (j, i))) (t (j, i))).trans (ht (j, i))

private theorem covering_refinement {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings) {U : C} {S : Sieve U}
    (hS : S ∈ J.toGrothendieck U) : ∃ T ∈ J U, T ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X =>
    exact ⟨Presieve.singleton (𝟙 X), J.mem_coverings_of_isIso (𝟙 X), by simp⟩
  | pullback X S hS Y f ih =>
    obtain ⟨R, hR, hle⟩ := ih
    let I := Σ Z : C, {a : Z ⟶ X // R a}
    let V : I → C := fun i ↦ i.1
    let a : ∀ i : I, V i ⟶ X := fun i ↦ i.2.1
    have heq : Presieve.ofArrows V a = R := by
      funext Z b
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.2.2
      · intro hb
        exact Presieve.ofArrows.mk (Y := V) (f := a) ⟨Z, b, hb⟩
    obtain ⟨P, p, q, hpq, hp⟩ := hJ.2.2 I X V a (heq ▸ hR) Y f
    refine ⟨Presieve.ofArrows P p, hp, ?_⟩
    rintro Z b ⟨i⟩
    change S (p i ≫ f)
    rw [(hpq i).w]
    exact S.downward_closed (hle _ _ i.2.2) (q i)
  | transitive X S T hS hT ihS ihT =>
    obtain ⟨R, hR, hle⟩ := ihS
    have hh : ∀ (Y : C) (f : Y ⟶ X) (_ : R f),
        ∃ Q ∈ J Y, Q ≤ (T.pullback f).arrows := by
      intro Y f hf
      exact ihT (hle _ _ hf)
    choose Q hQ hQT using hh
    refine ⟨R.bind (fun {Y f} hf ↦ Q Y f hf),
      hJ.2.1 X R (fun {Y} f hf ↦ Q Y f hf) hR hQ, ?_⟩
    intro Z f hf
    obtain ⟨Y, g, a, ha, hg, rfl⟩ := hf
    exact hQT Y a ha _ _ hg


private def reconstructedPoint (hJ : J.IsSiteForCoverings) :
    J.toGrothendieck.Point.{u} where
  fiber := sitePointFunctor J p
  isCofiltered := (site_point_reconstruction_sets J hJ p).2.2.1
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective S hS x := by
    obtain ⟨T, hT, hTS⟩ := covering_refinement J hJ hS
    obtain ⟨I, V, f, rfl⟩ := T.exists_eq_ofArrows
    obtain ⟨i, y, hy⟩ := (site_point_reconstruction_sets J hJ p).2.1 I _ V f hT x
    exact ⟨V i, f i, hTS _ _ ⟨i⟩, y, hy⟩

omit [HasFiniteLimits C] in
private def pointOverFiberIso {K : GrothendieckTopology C} (Φ : K.Point.{u})
    {U : C} (x : Φ.fiber.obj U) (A : Type (u + 1)) [Category.{u} A]
    [HasColimitsOfSize.{u, u} A] :
    (Φ.over x).sheafFiber (A := A) ≅
      sheafToPresheaf (K.over U) A ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Over.post (X := Φ.fiber.elementsMk U x) (CategoryOfElements.π Φ.fiber)).op ⋙
            colim := by
  let d := Over.post (X := Φ.fiber.elementsMk U x) (CategoryOfElements.π Φ.fiber)
  let E := FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x
  change sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π (Φ.over x).fiber).op ⋙ colim ≅ _
  have hd : CategoryOfElements.π (Φ.over x).fiber = E.functor ⋙ d := by
    apply Functor.ext
    · intro X Y f
      apply Over.OverMorphism.ext
      simp
      rfl
    · rintro ⟨⟨V, ⟨⟨⟩⟩, a⟩, y⟩
      rfl
  rw [hd]
  exact Functor.isoWhiskerLeft
    (sheafToPresheaf (K.over U) A ⋙ (Functor.whiskeringLeft _ _ _).obj d.op)
      (Functor.Final.colimIso E.functor.op)

private def localizedFiberIso (hJ : J.IsSiteForCoverings)
    (n : sitePointNeighbourhood J p) (A : Type (u + 1)) [Category.{u} A]
    [HasColimitsOfSize.{u, u} A] :
    ((reconstructedPoint J p hJ).over n.2).sheafFiber (A := A) ≅
      sheafToPresheaf (J.toGrothendieck.over n.1) A ⋙
        (Functor.whiskeringLeft _ _ _).obj (localizedNeighborhoods J p n).op ⋙ colim :=
  pointOverFiberIso (reconstructedPoint J p hJ) n.2 A


private def localizedPoint (hJ : J.IsSiteForCoverings)
    (n : sitePointNeighbourhood J p) :
    GeometricMorphism (Type u) (Sheaf (J.toGrothendieck.over n.1) (Type u)) where
  inverse := sets (localizedNeighborhoods J p n) (J.toGrothendieck.over n.1)
  direct := ((reconstructedPoint J p hJ).over n.2).skyscraperSheafFunctor
  adj := ((reconstructedPoint J p hJ).over n.2).skyscraperSheafAdjunction.ofNatIsoLeft
    (localizedFiberIso J p hJ n (Type u))
  leftExact := by
    let := (site_point_reconstruction_sets J hJ p).2.2.1
    dsimp [sets]
    infer_instance

private def pointSetComponent (hJ : J.IsSiteForCoverings)
    (F : Sheaf J.toGrothendieck (Type u)) :
    (sets (neighborhoods J p) J.toGrothendieck).obj F ≅ p.inverse.obj F := by
  let h := (site_point_reconstruction_sets J hJ p).2.2.2.1 F
  exact colimit.isoColimitCocone
    ⟨h.choose, h.choose_spec.choose_spec.1.some⟩ ≪≫ h.choose_spec.choose

private theorem pointSetComponent_germ (hJ : J.IsSiteForCoverings)
    (F : Sheaf J.toGrothendieck (Type u)) (n : sitePointNeighbourhood J p)
    (s : F.obj.obj (op n.1)) :
    (pointSetComponent J p hJ F).hom
      (colimit.ι ((neighborhoods J p).op ⋙ F.obj) (op n) s) =
        p.inverse.map (sitePointSectionHom J F s) n.2 := by
  let h := (site_point_reconstruction_sets J hJ p).2.2.2.1 F
  change h.choose_spec.choose.hom
    ((colimit.isoColimitCocone ⟨h.choose, h.choose_spec.choose_spec.1.some⟩).hom
      (colimit.ι ((neighborhoods J p).op ⋙ F.obj) (op n) s)) = _
  have hh := ConcreteCategory.congr_hom
    (colimit.isoColimitCocone_ι_hom
      ⟨h.choose, h.choose_spec.choose_spec.1.some⟩ (op n)) s
  exact (congrArg h.choose_spec.choose.hom hh).trans
    (h.choose_spec.choose_spec.2 n.1 n.2 s)

private def pointSetIso (hJ : J.IsSiteForCoverings) :
    sets (neighborhoods J p) J.toGrothendieck ≅ p.inverse := by
  refine NatIso.ofComponents (pointSetComponent J p hJ) ?_
  intro F G f
  apply colimit.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change (pointSetComponent J p hJ G).hom
    (colim.map (Functor.whiskerLeft (neighborhoods J p).op f.hom)
      (colimit.ι ((neighborhoods J p).op ⋙ F.obj) n s)) =
        p.inverse.map f ((pointSetComponent J p hJ F).hom
          (colimit.ι ((neighborhoods J p).op ⋙ F.obj) n s))
  have hh := ConcreteCategory.congr_hom
    (ι_colimMap (Functor.whiskerLeft (neighborhoods J p).op f.hom) n) s
  change colim.map (Functor.whiskerLeft (neighborhoods J p).op f.hom)
    (colimit.ι ((neighborhoods J p).op ⋙ F.obj) n s) =
      colimit.ι ((neighborhoods J p).op ⋙ G.obj) n (f.hom.app (op n.unop.1) s) at hh
  rw [hh]
  change (pointSetComponent J p hJ G).hom
    (colimit.ι ((neighborhoods J p).op ⋙ G.obj) n (f.hom.app (op n.unop.1) s)) = _
  rw [pointSetComponent_germ, pointSetComponent_germ]
  have ht := (site_point_reconstruction_sets J hJ p).2.2.2.2 F G f n.unop.1 s
  change sitePointSectionHom J G (f.hom.app (op n.unop.1) s) =
    sitePointSectionHom J F s ≫ f at ht
  rw [ht, p.inverse.map_comp]
  rfl

private def localizedSetComparison (hJ : J.IsSiteForCoverings)
    (n : sitePointNeighbourhood J p) :
    J.toGrothendieck.overPullback (Type u) n.1 ⋙
      sets (localizedNeighborhoods J p n) (J.toGrothendieck.over n.1) ≅ p.inverse := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  exact Functor.isoWhiskerLeft
    (sheafToPresheaf J.toGrothendieck (Type u) ⋙
      (Functor.whiskeringLeft _ _ _).obj (neighborhoods J p).op)
    (Functor.Final.colimIso (Over.forget n).op) ≪≫ pointSetIso J p hJ

private theorem localizedSetComparison_germ (hJ : J.IsSiteForCoverings)
    (n : sitePointNeighbourhood J p) (G : Sheaf J.toGrothendieck (Type u))
    (z : Over n) (s : G.obj.obj (op z.left.1)) :
    (localizedSetComparison J p hJ n).hom.app G
      (colimit.ι ((localizedNeighborhoods J p n).op ⋙ (G.over n.1).obj) (op z) s) =
        p.inverse.map (sitePointSectionHom J G s) z.left.2 := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  have h := ConcreteCategory.congr_hom
    (Functor.Final.ι_colimitIso_hom (Over.forget n).op
      ((neighborhoods J p).op ⋙ G.obj) (op z)) s
  exact (congrArg (pointSetComponent J p hJ G).hom h).trans
    (pointSetComponent_germ J p hJ G z.left s)

private def modulesForgetIso {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c) :
    modules d R hc ⋙ forget₂ (ModuleCat c.pt) AddCommGrpCat ≅
      SheafOfModules.toSheaf
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⋙
          sheafToPresheaf K AddCommGrpCat ⋙
            (Functor.whiskeringLeft _ _ _).obj d.op ⋙ colim :=
  Iso.refl _

omit [HasFiniteLimits C] in
private theorem modules_map_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c)
    {F G : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ G) (n : N) (s : F.val.obj (op (d.obj n))) :
    (modules d R hc).map f (moduleGerm d R hc F n s) =
      moduleGerm d R hc G n (f.val.app (op (d.obj n)) s) := by
  let : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall _
  exact PresheafOfModules.ModuleColimit.map_apply (C := N) hc
    (colimit.isColimit _) (colimit.isColimit _)
      ((PresheafOfModules.pushforward₀ d _).map f.val) s

omit [HasFiniteLimits C] in
private theorem moduleGerm_sum_smul {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c)
    (F : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    (n : N) {I : Type v} [Fintype I]
    (a : I → R.obj.obj (op (d.obj n))) (m : I → F.val.obj (op (d.obj n))) :
    moduleGerm d R hc F n (∑ i, a i • m i) =
      ∑ i, c.ι.app (op n) (a i) • moduleGerm d R hc F n (m i) := by
  classical
  let : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall _
  let P := (PresheafOfModules.pushforward₀ d _).obj F.val
  unfold moduleGerm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (PresheafOfModules.ModuleColimit.smul_eq (M := P) hc
    (colimit.isColimit P.presheaf) (U := op n) (a i) (m i)).symm

omit [HasFiniteLimits C] in
private theorem modules_freeHomEquiv_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c)
    (F : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    {I : Type u} (f : SheafOfModules.free (R :=
      (sheafCompose K (forget₂ CommRingCat RingCat)).obj R) I ⟶ F) (n : N) (i : I) :
    (modules d R hc).map f
      (moduleGerm d R hc (SheafOfModules.free (R :=
        (sheafCompose K (forget₂ CommRingCat RingCat)).obj R) I) n
        ((SheafOfModules.freeSection (R :=
          (sheafCompose K (forget₂ CommRingCat RingCat)).obj R)
            (I := I) i).val (op (d.obj n)))) =
      moduleGerm d R hc F n ((SheafOfModules.freeHomEquiv F f i).val (op (d.obj n))) := by
  rw [modules_map_germ]
  have h := congrArg (fun t : F.sections ↦ t.val (op (d.obj n)))
    (SheafOfModules.freeHomEquiv_apply f i).symm
  exact congrArg (moduleGerm d R hc F n) h

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private def moduleRestrictionIso {N : Type u} [SmallCategory N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u}) (n : N) :
    SheafOfModules.overFunctor
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) (d.obj n) ⋙
        SheafOfModules.forget
          (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over (d.obj n)) ⋙
            PresheafOfModules.pushforward₀ (Over.post d)
              (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).over (d.obj n)).obj ≅
      SheafOfModules.forget ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⋙
        PresheafOfModules.pushforward₀ d
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).obj ⋙
            PresheafOfModules.pushforward₀ (Over.forget n) (ringDiagram d R) := by
  refine NatIso.ofComponents (fun G ↦
    PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intro V W f; ext t; rfl)) ?_
  intro G H f
  ext V t
  rfl

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private def moduleComparison {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c) (n : N) :
    SheafOfModules.overFunctor
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) (d.obj n) ⋙
        modules (Over.post d) (R.over (d.obj n))
          ((Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc) ≅
      modules d R hc := by
  let : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall _
  let : InitiallySmall.{u} (Over n) := initiallySmall_of_essentiallySmall _
  exact Functor.isoWhiskerRight (moduleRestrictionIso d R n)
    (PresheafOfModules.colimitFunctor
      ((Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc)) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.forget ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⋙
        PresheafOfModules.pushforward₀ d
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).obj)
      (colimitOverComparison (ringDiagram d R) hc n)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private theorem moduleComparison_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c) (n : N)
    (G : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
    (z : Over n) (t : G.val.obj (op (d.obj z.left))) :
    (moduleComparison d R hc n).hom.app G
      (moduleGerm (Over.post d) (R.over (d.obj n))
        ((Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc)
          (G.over (d.obj n)) z t) = moduleGerm d R hc G z.left t := by
  let : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall _
  let : InitiallySmall.{u} (Over n) := initiallySmall_of_essentiallySmall _
  let hc' := (Functor.Final.isColimitWhiskerEquiv (Over.forget n).op _).symm hc
  let P := (PresheafOfModules.pushforward₀ (Over.post d) _).obj (G.over (d.obj n)).val
  let M := (PresheafOfModules.pushforward₀ d _).obj G.val
  let Q := (PresheafOfModules.pushforward₀ (Over.forget n) (ringDiagram d R)).obj M
  have h := PresheafOfModules.ModuleColimit.map_apply (C := Over n) hc'
    (colimit.isColimit P.presheaf) (colimit.isColimit Q.presheaf)
      ((moduleRestrictionIso d R n).hom.app G) t
  change (PresheafOfModules.colimitFunctor hc').map
      ((moduleRestrictionIso d R n).hom.app G)
      (moduleGerm (Over.post d) (R.over (d.obj n)) hc' (G.over (d.obj n)) z t) =
    PresheafOfModules.ModuleColimit.ιM
      (hcR := hc') (hcM := colimit.isColimit Q.presheaf) t at h
  exact (congrArg ((colimitOverComparison (ringDiagram d R) hc n).hom.app M) h).trans
    (colimitOverComparison_germ (ringDiagram d R) hc n M z t)

attribute [irreducible] moduleComparison

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private def localizedModuleComparison (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p) :
    SheafOfModules.overFunctor
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R) n.1 ⋙
        localizedModules J p hJ R n ≅ stalkModules J p hJ R := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  exact moduleComparison (neighborhoods J p) R (colimit.isColimit _) n

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem localizedModuleComparison_germ (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p)
    (G : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R))
    (z : Over n) (t : G.val.obj (op z.left.1)) :
    (localizedModuleComparison J p hJ R n).hom.app G
      (localizedModuleGerm J p hJ R n (G.over n.1) z t) =
        stalkModuleGerm J p hJ R G z.left t := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  exact moduleComparison_germ (neighborhoods J p) R (colimit.isColimit _) n G z t

attribute [irreducible] localizedModuleComparison

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem localizedModules_preservesFiniteColimits (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p) :
    PreservesFiniteColimits (localizedModules J p hJ R n) := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  let S := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1
  let F := localizedModules J p hJ R n
  let V := forget₂ (ModuleCat (stalkRing J p R)) AddCommGrpCat
  let e : F ⋙ V ≅ SheafOfModules.toSheaf S ⋙
      ((reconstructedPoint J p hJ).over n.2).sheafFiber :=
    modulesForgetIso (localizedNeighborhoods J p n) (R.over n.1)
      (localizedRingIsColimit J p hJ R n) ≪≫
        Functor.isoWhiskerLeft (SheafOfModules.toSheaf S)
          (localizedFiberIso J p hJ n AddCommGrpCat).symm
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} S) :=
    (moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesFiniteColimits (F ⋙ V) := preservesFiniteColimits_of_natIso e.symm
  exact preservesFiniteColimits_of_reflects_of_preserves F V

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private def unitRestrictionIso {N : Type u} [SmallCategory N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u}) :
    (PresheafOfModules.pushforward₀ d _).obj
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)).val ≅
        PresheafOfModules.unit (ringDiagram d R) := by
  refine PresheafOfModules.isoMk (fun V ↦ Iso.refl _) ?_
  intro V W f
  rfl

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private def moduleUnitIso {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c) :
    (modules d R hc).obj (SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) ≅ ModuleCat.of c.pt c.pt := by
  let : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall _
  exact (PresheafOfModules.colimitFunctor hc).mapIso (unitRestrictionIso d R) ≪≫
    colimitUnitIso (ringDiagram d R) hc

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private theorem moduleUnitIso_germ {N : Type u} [SmallCategory N] [IsCofiltered N]
    (d : N ⥤ C) {K : GrothendieckTopology C} (R : Sheaf K CommRingCat.{u})
    {c : Cocone (ringDiagram d R)} (hc : IsColimit c) (n : N)
    (t : R.obj.obj (op (d.obj n))) :
    (moduleUnitIso d R hc).hom (moduleGerm d R hc (SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) n t) = c.ι.app (op n) t := by
  let : InitiallySmall.{u} N := initiallySmall_of_essentiallySmall _
  let P := (PresheafOfModules.pushforward₀ d _).obj
    (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)).val
  let M := PresheafOfModules.unit (ringDiagram d R)
  have h := PresheafOfModules.ModuleColimit.map_apply (C := N) hc
    (colimit.isColimit P.presheaf) (colimit.isColimit M.presheaf)
      (unitRestrictionIso d R).hom t
  change (PresheafOfModules.colimitFunctor hc).map (unitRestrictionIso d R).hom
      (moduleGerm d R hc (SheafOfModules.unit
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) n t) =
    PresheafOfModules.ModuleColimit.ιM
      (hcR := hc) (hcM := colimit.isColimit M.presheaf) t at h
  exact (congrArg (colimitUnitIso (ringDiagram d R) hc).hom h).trans
    (colimitUnitIso_germ (ringDiagram d R) hc (op n) t)

attribute [irreducible] moduleUnitIso

private def ringFreeCofan (S : Type u) [Ring S] (I : Type u) :
    Cofan (fun _ : I ↦ ModuleCat.of S S) :=
  Cofan.mk ((ModuleCat.free S).obj I)
    (fun i ↦ ModuleCat.ofHom (Finsupp.lsingle i (R := S) (M := S)))

private def ringFreeCofanIsColimit (S : Type u) [Ring S] (I : Type u) :
    IsColimit (ringFreeCofan S I) where
  desc s := ModuleCat.freeDesc (↾fun i ↦ s.ι.app ⟨i⟩ (1 : S))
  fac s i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact ModuleCat.freeDesc_apply _ i.as
  uniq s f h := by
    apply ModuleCat.free_hom_ext
    intro i
    exact (ConcreteCategory.congr_hom (h ⟨i⟩) (1 : S)).trans
      (ModuleCat.freeDesc_apply (↾fun j : I ↦ s.ι.app ⟨j⟩ (1 : S)) i).symm

omit [HasFiniteLimits C] in
private def freeModuleImageIso {K : GrothendieckTopology C}
    (S : Type u) [Ring S] (Q : Sheaf K RingCat.{u})
    (T : SheafOfModules.{u} Q ⥤ ModuleCat.{u} S) [PreservesFiniteColimits T]
    (e : T.obj (SheafOfModules.unit Q) ≅ ModuleCat.of S S) (b : ℕ) :
    (ModuleCat.free S).obj (ULift.{u} (Fin b)) ≅
      T.obj (SheafOfModules.free (R := Q) (ULift.{u} (Fin b))) :=
  (ringFreeCofanIsColimit S (ULift.{u} (Fin b))).coconePointsIsoOfNatIso
    (isColimitOfPreserves T (SheafOfModules.isColimitFreeCofan (R := Q)
      (ULift.{u} (Fin b)))) (Discrete.natIso fun _ ↦ e.symm)

omit [HasFiniteLimits C] in
private theorem freeModuleImageIso_basis {K : GrothendieckTopology C}
    (S : Type u) [Ring S] (Q : Sheaf K RingCat.{u})
    (T : SheafOfModules.{u} Q ⥤ ModuleCat.{u} S) [PreservesFiniteColimits T]
    (e : T.obj (SheafOfModules.unit Q) ≅ ModuleCat.of S S)
    (b : ℕ) (i : ULift.{u} (Fin b)) :
    (freeModuleImageIso S Q T e b).hom (ModuleCat.freeMk i) =
      T.map (SheafOfModules.ιFree (R := Q) (I := ULift.{u} (Fin b)) i) (e.inv 1) := by
  exact ConcreteCategory.congr_hom
    (IsColimit.comp_coconePointsIsoOfNatIso_hom
      (ringFreeCofanIsColimit S (ULift.{u} (Fin b)))
      (isColimitOfPreserves T (SheafOfModules.isColimitFreeCofan (R := Q)
        (ULift.{u} (Fin b)))) (Discrete.natIso fun _ ↦ e.symm) ⟨i⟩) (1 : S)

attribute [irreducible] freeModuleImageIso

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private def localizedFreeIso (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p)
    (b : ℕ) :
    (ModuleCat.free (stalkRing J p R)).obj (ULift.{u} (Fin b)) ≅
      (localizedModules J p hJ R n).obj (SheafOfModules.free (R :=
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
          (ULift.{u} (Fin b))) := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  have := localizedModules_preservesFiniteColimits J p hJ R n
  let S := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1
  exact freeModuleImageIso (stalkRing J p R) S (localizedModules J p hJ R n)
    (moduleUnitIso (localizedNeighborhoods J p n) (R.over n.1)
      (localizedRingIsColimit J p hJ R n)) b

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem localizedFreeIso_germ (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p)
    (b : ℕ) (i : ULift.{u} (Fin b)) (z : Over n) :
    (localizedFreeIso J p hJ R n b).hom
      (ModuleCat.freeMk (R := stalkRing J p R) (X := ULift.{u} (Fin b)) i) =
      localizedModuleGerm J p hJ R n
        (SheafOfModules.free (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
            (ULift.{u} (Fin b))) z
        ((SheafOfModules.freeSection (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
            (I := ULift.{u} (Fin b)) i).val (op ((localizedNeighborhoods J p n).obj z))) := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  let S := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1
  let F := localizedModules J p hJ R n
  have := localizedModules_preservesFiniteColimits J p hJ R n
  let e : F.obj (SheafOfModules.unit S) ≅ ModuleCat.of (stalkRing J p R) (stalkRing J p R) :=
    moduleUnitIso (localizedNeighborhoods J p n) (R.over n.1)
      (localizedRingIsColimit J p hJ R n)
  have hunit : e.inv 1 = localizedModuleGerm J p hJ R n (SheafOfModules.unit S) z
      (1 : R.obj.obj (op z.left.1)) := by
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    have hg : e.hom (localizedModuleGerm J p hJ R n (SheafOfModules.unit S) z
        (1 : R.obj.obj (op z.left.1))) = 1 :=
      (moduleUnitIso_germ (localizedNeighborhoods J p n) (R.over n.1)
        (localizedRingIsColimit J p hJ R n) z 1).trans (map_one _)
    exact (ModuleCat.hom_inv_apply e 1).trans hg.symm
  have h := freeModuleImageIso_basis (stalkRing J p R) S F e b i
  change (localizedFreeIso J p hJ R n b).hom
      (ModuleCat.freeMk (R := stalkRing J p R) (X := ULift.{u} (Fin b)) i) =
    F.map (SheafOfModules.ιFree (R := S) (I := ULift.{u} (Fin b)) i) (e.inv 1) at h
  exact h.trans ((congrArg (fun m : F.obj (SheafOfModules.unit S) ↦
    F.map (SheafOfModules.ιFree (R := S) (I := ULift.{u} (Fin b)) i) m) hunit).trans
      (modules_map_germ (localizedNeighborhoods J p n) (R.over n.1)
        (localizedRingIsColimit J p hJ R n)
        (SheafOfModules.ιFree (R := S) (I := ULift.{u} (Fin b)) i) z
          (1 : R.obj.obj (op z.left.1))))

attribute [irreducible] localizedFreeIso

private theorem exists_matrix_lift (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) {a b : ℕ}
    (A : Fin b → Fin a → stalkRing J p R) :
    ∃ (n : sitePointNeighbourhood J p) (B : Fin b → Fin a → R.obj.obj (op n.1)),
      ∀ j i, colimit.ι (ringDiagram (neighborhoods J p) R) (op n) (B j i) = A j i := by
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  obtain ⟨n, B, hB⟩ := colimit_matrix_lift (ringDiagram (neighborhoods J p) R) A
  exact ⟨n.unop, B, hB⟩

private theorem smul_section_map {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    (F : SheafOfModules.{u} S) (s : F.sections) {V W : Dᵒᵖ} (f : V ⟶ W)
    (r : S.obj.obj V) (t : S.obj.obj W) (h : S.obj.map f r = t) :
    F.val.map f (r • @id (F.val.obj V) (s.val V)) =
      t • @id (F.val.obj W) (s.val W) := by
  exact (F.val.map_smul f r (s.val V)).trans
    (congrArg₂ (fun (r : S.obj.obj W) (m : F.val.obj W) ↦
      @SMul.smul _ _ (F.val.obj W).isModule.toSMul r m) h
        (PresheafOfModules.sections_property s f))

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private def matrixSection (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (U : C) {a b : ℕ} (A : Fin b → Fin a → R.obj.obj (op U)) (i : Fin a) :
    (SheafOfModules.free (R :=
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
        (ULift.{u} (Fin b))).sections := by
  classical
  let S := ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U
  let F := SheafOfModules.free (R := S) (ULift.{u} (Fin b))
  refine PresheafOfModules.sectionsMk (M := F.val) (fun V ↦ ∑ j : Fin b,
    @SMul.smul (S.obj.obj V) (F.val.obj V) (F.val.obj V).isModule.toSMul
      (R.obj.map V.unop.hom.op (A j i))
      ((SheafOfModules.freeSection (R := S) (I := ULift.{u} (Fin b)) ⟨j⟩).val V)) ?_
  intro V W f
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply smul_section_map F (SheafOfModules.freeSection (R := S) (I := ULift.{u} (Fin b)) ⟨j⟩) f
  change R.obj.map f.unop.left.op (R.obj.map V.unop.hom.op (A j i)) =
    R.obj.map W.unop.hom.op (A j i)
  rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp, ← op_comp, Over.w f.unop]

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private theorem matrixSection_val (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (U : C) {a b : ℕ} (A : Fin b → Fin a → R.obj.obj (op U)) (i : Fin a)
    (V : Over U) :
    (matrixSection J R U A i).val (op V) =
      ∑ j : Fin b, @SMul.smul (R.obj.obj (op V.left))
        ((SheafOfModules.free (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
            (ULift.{u} (Fin b))).val.obj (op V))
        ((SheafOfModules.free (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
            (ULift.{u} (Fin b))).val.obj (op V)).isModule.toSMul
        (R.obj.map V.hom.op (A j i))
        ((SheafOfModules.freeSection (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
            (I := ULift.{u} (Fin b)) ⟨j⟩).val (op V)) := by
  rfl

attribute [irreducible] matrixSection

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private def matrixHom (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (U : C) {a b : ℕ} (A : Fin b → Fin a → R.obj.obj (op U)) :
    SheafOfModules.free (R :=
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
        (ULift.{u} (Fin a)) ⟶ SheafOfModules.free (ULift.{u} (Fin b)) :=
  (SheafOfModules.freeHomEquiv (I := ULift.{u} (Fin a))
    (SheafOfModules.free (R :=
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
        (ULift.{u} (Fin b)))).symm (fun i ↦ matrixSection J R U A i.down)

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
omit [HasFiniteLimits C] in
private theorem matrixHom_spec (R : Sheaf J.toGrothendieck CommRingCat.{u})
    (U : C) {a b : ℕ} (A : Fin b → Fin a → R.obj.obj (op U)) :
    SheafOfModules.freeHomEquiv (I := ULift.{u} (Fin a))
      (SheafOfModules.free (R :=
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
          (ULift.{u} (Fin b))) (matrixHom J R U A) =
      (fun i ↦ matrixSection J R U A i.down) := by
  exact (SheafOfModules.freeHomEquiv (I := ULift.{u} (Fin a))
    (SheafOfModules.free (R :=
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over U)
        (ULift.{u} (Fin b)))).apply_symm_apply
          (fun i ↦ matrixSection J R U A i.down)

attribute [irreducible] matrixHom

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 100000 in
-- Use the explicit module action and the proved APIs without unfolding the isomorphisms.
private theorem matrixHom_basis (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p)
    {a b : ℕ} (A : Fin b → Fin a → R.obj.obj (op n.1)) (i : Fin a) :
    (localizedModules J p hJ R n).map (matrixHom J R n.1 A)
      ((localizedFreeIso J p hJ R n a).hom
      (ModuleCat.freeMk (R := stalkRing J p R) (X := ULift.{u} (Fin a)) ⟨i⟩)) =
      (let B := (localizedModules J p hJ R n).obj (SheafOfModules.free (R :=
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
          (ULift.{u} (Fin b)))
       @Finset.sum (Fin b) B B.isAddCommGroup.toAddCommMonoid Finset.univ
        (fun j ↦ @SMul.smul (stalkRing J p R) B B.isModule.toSMul
          (colimit.ι (ringDiagram (neighborhoods J p) R) (op n) (A j i))
          ((localizedFreeIso J p hJ R n b).hom
            (ModuleCat.freeMk (R := stalkRing J p R) (X := ULift.{u} (Fin b)) ⟨j⟩)))) := by
  classical
  rcases n with ⟨U, x⟩
  let n : sitePointNeighbourhood J p := ⟨U, x⟩
  let := (site_point_reconstruction_sets J hJ p).2.2.1
  let : InitiallySmall.{u} (Over n) := initiallySmall_of_essentiallySmall _
  let z : Over n := Over.mk (𝟙 n)
  refine (congrArg (fun m : (localizedModules J p hJ R n).obj
      (SheafOfModules.free (R :=
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
          (ULift.{u} (Fin a))) ↦
      (localizedModules J p hJ R n).map (matrixHom J R n.1 A) m)
    (localizedFreeIso_germ J p hJ R n a ⟨i⟩ z)).trans ?_
  let F := SheafOfModules.free (R :=
    ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
      (ULift.{u} (Fin b))
  have h := modules_freeHomEquiv_germ (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n) F (matrixHom J R n.1 A) z ⟨i⟩
  have hs := congrArg (fun t : F.sections ↦
    t.val (op ((localizedNeighborhoods J p n).obj z)))
      (congrFun (matrixHom_spec J R n.1 A) ⟨i⟩)
  have h' := h.trans (congrArg (moduleGerm (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n) F z) hs)
  refine h'.trans ((congrArg (moduleGerm (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n) F z)
      (matrixSection_val J R n.1 A i ((localizedNeighborhoods J p n).obj z))).trans ?_)
  let V := op ((localizedNeighborhoods J p n).obj z)
  change moduleGerm (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n) F z
      (∑ j : Fin b, @SMul.smul (R.obj.obj (op n.1)) (F.val.obj V)
        (F.val.obj V).isModule.toSMul (R.obj.map (𝟙 n.1).op (A j i))
          ((SheafOfModules.freeSection (R :=
            ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
              (I := ULift.{u} (Fin b)) ⟨j⟩).val V)) = _
  simp only [op_id, R.obj.map_id, ConcreteCategory.id_apply]
  refine (moduleGerm_sum_smul (localizedNeighborhoods J p n) (R.over n.1)
    (localizedRingIsColimit J p hJ R n) F z (fun j ↦ A j i)
    (fun j ↦ @id (F.val.obj V) ((SheafOfModules.freeSection (R :=
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
        (I := ULift.{u} (Fin b)) ⟨j⟩).val V))).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun m : (localizedModules J p hJ R n).obj F ↦
    @SMul.smul (stalkRing J p R) ((localizedModules J p hJ R n).obj F)
      ((localizedModules J p hJ R n).obj F).isModule.toSMul
      (colimit.ι (ringDiagram (neighborhoods J p) R) (op n) (A j i)) m)
    (localizedFreeIso_germ J p hJ R n b ⟨j⟩ z).symm

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
private theorem matrixHom_conjugacy (hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) (n : sitePointNeighbourhood J p)
    {a b : ℕ} (A : Fin b → Fin a → R.obj.obj (op n.1))
    (g : (Fin a → stalkRing J p R) →ₗ[stalkRing J p R] (Fin b → stalkRing J p R))
    (hA : ∀ j i, colimit.ι (ringDiagram (neighborhoods J p) R) (op n) (A j i) =
      g (Pi.single i 1) j) :
    (localizedModules J p hJ R n).map (matrixHom J R n.1 A) ≫
        ((localizedFreeIso J p hJ R n b).symm ≪≫ finiteFreeIso (stalkRing J p R) b).hom =
      ((localizedFreeIso J p hJ R n a).symm ≪≫ finiteFreeIso (stalkRing J p R) a).hom ≫
        ModuleCat.ofHom g := by
  classical
  rcases n with ⟨U, x⟩
  let n : sitePointNeighbourhood J p := ⟨U, x⟩
  apply linearMapConjugacy (stalkRing J p R)
    ((localizedModules J p hJ R n).map (matrixHom J R n.1 A)) a b
    (localizedFreeIso J p hJ R n a) (localizedFreeIso J p hJ R n b) g
  intro i
  refine (matrixHom_basis J p hJ R n A i).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun r : stalkRing J p R ↦
    @SMul.smul (stalkRing J p R)
      ((localizedModules J p hJ R n).obj (SheafOfModules.free (R :=
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
          (ULift.{u} (Fin b))))
      ((localizedModules J p hJ R n).obj (SheafOfModules.free (R :=
        ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
          (ULift.{u} (Fin b)))).isModule.toSMul
      r ((localizedFreeIso J p hJ R n b).hom
      (ModuleCat.freeMk (R := stalkRing J p R) (X := ULift.{u} (Fin b)) ⟨j⟩))) (hA j i)


end Proofs

section RealizationProof

attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize
set_option maxHeartbeats 800000 in
-- Assemble the comparison isomorphisms through the chosen cokernel.
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

Proof:
1. Reconstruct Mathlib's site point with fiber `sitePointFunctor J p`. Its slice
point has a skyscraper right adjoint; the category-of-elements equivalence identifies
its sheaf fiber with the specified localized section colimit. Thus it gives `q`.
2. The reconstruction theorem identifies the original set section colimit with
`p.inverse`. Finality of the neighborhood forgetful functor gives the localized set
comparison. The same finality comparison on additive section colimits is linear
for the specified ring cocone and gives the natural module comparison. Both maps
have the asserted values on every section germ.
3. The module stalk preserves finite colimits: after forgetting to abelian groups
it is the composite of the module-to-abelian-sheaf functor with the slice point's
sheaf fiber. These preserve finite colimits, and module forgetting reflects them.
The unit sheaf has stalk the stalk ring; coproduct universal properties therefore
identify finite free sheaf stalks with free modules, compatibly with basis germs.
4. Choose a finite free presentation of `M`. Each matrix entry has a section
representative, and filteredness supplies a common neighborhood, including when
the matrix is empty. The lifted entries define a sheaf morphism using global
sections of the free sheaf; restriction preserves its finite sums and scalar action.
5. On basis elements its stalk matrix is the chosen presentation matrix. Stalks
preserve its cokernel, which is therefore isomorphic to `M`. Take this sheaf
cokernel as `F`; all the comparison and matrix normalization clauses follow.
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
  set_option backward.isDefEq.respectTransparency.types true in
  set_option backward.isDefEq.respectTransparency true in
  exact (by
    classical
    let := fastRingSheafCompose J.toGrothendieck
    let := fastAbelianSheafify J.toGrothendieck
    let := fastSetSheafify J.toGrothendieck
    let := fastRingAbCompose J.toGrothendieck
    let := fastAbSetCompose J.toGrothendieck
    let := (site_point_reconstruction_sets J hJ p).2.2.1
    obtain ⟨b, a, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' (stalkRing J p R) M
    obtain ⟨n, A, hA⟩ := exists_matrix_lift J p hJ R (fun j i ↦ g (Pi.single i 1) j)
    let := fastRingSheafCompose (J.toGrothendieck.over n.1)
    let := fastAbelianSheafify (J.toGrothendieck.over n.1)
    let := fastSetSheafify (J.toGrothendieck.over n.1)
    let := fastRingAbCompose (J.toGrothendieck.over n.1)
    let := fastAbSetCompose (J.toGrothendieck.over n.1)
    let T := localizedModules J p hJ R n
    let α := matrixHom J R n.1 A
    have := localizedModules_preservesFiniteColimits J p hJ R n
    let ep := (localizedFreeIso J p hJ R n a).symm ≪≫ finiteFreeIso (stalkRing J p R) a
    let eq := (localizedFreeIso J p hJ R n b).symm ≪≫ finiteFreeIso (stalkRing J p R) b
    have w : T.map α ≫ eq.hom = ep.hom ≫ ModuleCat.ofHom g :=
      matrixHom_conjugacy J p hJ R n A g hA
    let eM : T.obj (cokernel α) ≅ M :=
      presentationCokernelIso (stalkRing J p R) T α f g hf hgf ep eq w
    refine ⟨n, localizedPoint J p hJ n, localizedSetComparison J p hJ n,
      localizedModuleComparison J p hJ R n, cokernel α, a, b, A, α, rfl,
      localizedSetComparison_germ J p hJ n, ?_, ⟨eM⟩, ⟨Iso.refl _⟩, ?_⟩
    · intro G z s
      exact localizedModuleComparison_germ J p hJ R n G z s
    · intro i V
      have hs := congrArg (fun t : (SheafOfModules.free (R :=
          ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R).over n.1)
            (ULift.{u} (Fin b))).sections ↦ t.val (op V))
        (congrFun (matrixHom_spec J R n.1 A) ⟨i⟩)
      exact hs.trans (matrixSection_val J R n.1 A i V)
  )

end RealizationProof

end CategoryTheory.SiteFpStalkRealization
