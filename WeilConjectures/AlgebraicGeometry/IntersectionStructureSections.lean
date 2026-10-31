/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Topology.RingInverseImageUnderlyingSets
import WeilConjectures.Topology.SubspaceRingRestrictionUnitCoherence
import WeilConjectures.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation
import WeilConjectures.RingTheory.DirectedRingCoconeRecognition
import WeilConjectures.Topology.SetsInverseImageComposition
import WeilConjectures.Topology.SpectralLimitPullbackSections

/-!
# Structure-sheaf sections on intersections of quasi-compact opens

Source: Stacks Project, More on Groupoids in Spaces, equation
`equation-sections-of-intersection` preceding Tag 0APJ
(blueprint: lem-a1-sections-intersection-structure-colimit).

The auxiliary definitions construct the subspace, its inverse-image structure sheaf,
the unit restriction maps, and the diagram indexed by the distinct indicated opens.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The subspace inclusion of the intersection. Source: Stacks, equation
`equation-sections-of-intersection` (blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionInclusion (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual inverse-image structure sheaf on the subspace intersection. Source: Stacks,
equation `equation-sections-of-intersection`, Tags 008F/008I
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionStructureSheaf (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    (TopCat.of {x : X // ∀ i : I, x ∈ U i}).Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat (intersectionInclusion X U)).obj X.sheaf

/-- Global sections of the inverse-image structure sheaf, without any scheme structure on
the intersection. Source: Stacks, equation `equation-sections-of-intersection`
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionSections (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) : CommRingCat.{u} :=
  (intersectionStructureSheaf X U).obj.obj (op ⊤)

/-- Restriction from a neighbourhood of the intersection: the inverse-image unit followed
by restriction to the full subspace. Source: Stacks, equation
`equation-sections-of-intersection`, Tag 008F
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionRestriction (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (V : X.Opens) (hV : ∀ x : X, (∀ i : I, x ∈ U i) → x ∈ V) :
    X.presheaf.obj (op V) ⟶ intersectionSections X U :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion X U)).unit.app X.sheaf).hom.app (op V) ≫
      (intersectionStructureSheaf X U).obj.map
        (homOfLE (fun (x : {x : X // ∀ i : I, x ∈ U i}) _ ↦
          hV x.val x.property)).op

/-- The restriction diagram, with repeated opens identified, indexed by reverse inclusion.
Source: Stacks, equation `equation-sections-of-intersection`
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionOpenDiagram (X : Scheme.{u}) {I : Type v} (U : I → X.Opens) :
    {V : X.Opens // V ∈ Set.range U}ᵒᵖ ⥤ CommRingCat.{u} where
  obj V := X.presheaf.obj (op V.unop.val)
  map f := X.presheaf.map (homOfLE (leOfHom f.unop)).op
  map_id V := X.presheaf.map_id (op V.unop.val)
  map_comp _f _g := X.presheaf.map_comp _ _

/-- The continuous map between intersections induced by a scheme morphism carrying each
indicated open into the corresponding open. Source: Stacks, naturality of equation
`equation-sections-of-intersection`
(blueprint: lem-a1-sections-intersection-structure-colimit). -/
def intersectionMap {X Y : Scheme.{u}} (g : X ⟶ Y) {I : Type v}
    (U : I → X.Opens) (V : I → Y.Opens) (h : ∀ i : I, U i ≤ g ⁻¹ᵁ V i) :
    TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶
      TopCat.of {y : Y // ∀ i : I, y ∈ V i} :=
  TopCat.ofHom ⟨fun x ↦ ⟨g x.val, fun i ↦ h i (x.property i)⟩,
    (g.continuous.comp continuous_subtype_val).subtype_mk _⟩

/- Compare the chosen inverse-image functors via the unit-compatible constructed ones. -/
@[irreducible] private noncomputable def ringSetPullbackIso {T Z : TopCat.{u}} (f : T ⟶ Z) :
    (sheafCompose (Opens.grothendieckTopology Z) (CategoryTheory.forget CommRingCat) ⋙
      TopCat.Sheaf.pullback (Type u) f) ≅
    (TopCat.Sheaf.pullback CommRingCat f ⋙
      sheafCompose (Opens.grothendieckTopology T) (CategoryTheory.forget CommRingCat)) :=
  Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackIso (Type u) f) ≪≫
    (Classical.choose (Classical.choose_spec
      (TopCat.Sheaf.ringInverseImage_underlyingSets f))) ≪≫
    Functor.isoWhiskerRight (TopCat.Sheaf.pullbackIso CommRingCat f).symm _

private theorem ringSetPullbackIso_unit {T Z : TopCat.{u}} (f : T ⟶ Z)
    (G : Z.Sheaf CommRingCat.{u}) (B : TopologicalSpace.Opens Z)
    (s : G.obj.obj (op B)) :
    ((ringSetPullbackIso f).hom.app G).hom.app (op ((Opens.map f).obj B))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app
        ((sheafCompose (Opens.grothendieckTopology Z)
          (CategoryTheory.forget CommRingCat)).obj G)).hom.app (op B) s) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f).unit.app G).hom.app
        (op B) s := by
  let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) (Type u) (Opens.grothendieckTopology Z) (Opens.grothendieckTopology T)
  let aR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) CommRingCat (Opens.grothendieckTopology Z)
      (Opens.grothendieckTopology T)
  let H := (sheafCompose (Opens.grothendieckTopology Z)
    (CategoryTheory.forget CommRingCat)).obj G
  have hS := congrArg (fun m ↦ m.hom.app (op B) s)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit_leftAdjointUniq_hom_app aS H)
  have hR := congrArg (fun m ↦ m.hom.app (op B) s)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f).unit_leftAdjointUniq_hom_app aR G)
  have hunit := (Classical.choose_spec (Classical.choose_spec
    (TopCat.Sheaf.ringInverseImage_underlyingSets f))).2.2 G B s
  let e := (TopCat.Sheaf.pullbackIso CommRingCat f).app G
  have hinv (x : ((TopCat.Sheaf.pullback CommRingCat f).obj G).obj.obj
      (op ((Opens.map f).obj B))) :
      e.inv.hom.app (op ((Opens.map f).obj B))
        (e.hom.hom.app (op ((Opens.map f).obj B)) x) = x :=
    congrArg (fun m ↦ m.hom.app (op ((Opens.map f).obj B)) x) e.hom_inv_id
  unfold ringSetPullbackIso
  change e.inv.hom.app _
    (((Classical.choose (Classical.choose_spec
      (TopCat.Sheaf.ringInverseImage_underlyingSets f))).hom.app G).hom.app _
      (((TopCat.Sheaf.pullbackIso (Type u) f).hom.app H).hom.app _
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
          (op B) s))) = _
  rw [show ((TopCat.Sheaf.pullbackIso (Type u) f).hom.app H).hom.app _
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app H).hom.app
        (op B) s) = _ from hS]
  erw [hunit, ← hR]
  exact hinv _

private theorem sets_open_unit_bijective {Z : TopCat.{u}}
    (G : Z.Sheaf (Type u)) (V : TopologicalSpace.Opens Z) :
    Function.Bijective (TopCat.Sheaf.subspaceSectionMap (Type u) (V : Set Z) G V
      (fun _ hx ↦ hx)) := by
  have heq := (TopCat.Sheaf.subspace_sets_restriction_unit_coherence
    (V : Set Z) G).1 V V
  let η := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) V.inclusion').unit.app
    G).hom.app (op V)
  have hc : IsIso (V.isOpenEmbedding.isOpenMap.adjunction.counit.app V) := by
    apply homOfLE_isIso_of_eq
    exact TopologicalSpace.Opens.functor_map_eq_inf V V |>.trans (inf_idem V)
  have hη : IsIso η := by
    have : IsIso (η ≫
        ((V.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app G).hom.app
          (op ((Opens.map V.inclusion').obj V))) := by
      rw [show η ≫ _ = _ from heq]
      infer_instance
    exact IsIso.of_isIso_comp_right η
      (((V.isOpenEmbedding.sheafPullbackIso (Type u)).hom.app G).hom.app
        (op ((Opens.map V.inclusion').obj V)))
  have htop : (Opens.map V.inclusion').obj V = ⊤ :=
    Opens.inclusion'_map_eq_top V
  have hr : IsIso (homOfLE (fun (x : V) (_ : x ∈ (⊤ : TopologicalSpace.Opens V)) ↦
      x.property) : (⊤ : TopologicalSpace.Opens V) ⟶ (Opens.map V.inclusion').obj V) :=
    homOfLE_isIso_of_eq _ htop.symm
  have : IsIso (TopCat.Sheaf.subspaceSectionMap (Type u) (V : Set Z) G V
      (fun _ hx ↦ hx)) := by
    unfold TopCat.Sheaf.subspaceSectionMap
    change IsIso (η ≫ _)
    infer_instance
  exact (CategoryTheory.isIso_iff_bijective _).mp inferInstance

namespace IntersectionProof

/- Use the comparison maps and unit equations from SpectralLimitPullbackSections.
   Only the additional comparison isomorphism and its squares are constructed here.
   Irreducibility avoids expanding sheafification choices in every later equality. -/

open TopCat.Sheaf

@[irreducible] private noncomputable def compIso {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) f).obj ((pullback (Type u) g).obj G) ≅
      (pullback (Type u) k).obj G :=
  (Classical.choose (exists_sets_inverseImage_comp f g)).app G ≪≫
    eqToIso (congrArg (fun a ↦ (pullback (Type u) a).obj G) h)

private theorem compMap_compIso {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) :
    compMap f g k h G =
      (pullbackPushforwardAdjunction (Type u) f).unit.app _ ≫
        (pushforward (Type u) f).map (compIso f g k h G).hom := by
  unfold compMap compUnit compIso
  simp only [Iso.trans_hom]
  rw [Functor.map_comp, Category.assoc]
  rfl

private theorem compMap_associativity {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D)
    (fg : B ⟶ D) (hfg : f ≫ g = fg)
    (q : A ⟶ D) (hq : h ≫ fg = q) (hq' : (h ≫ f) ≫ g = q)
    (G : D.Sheaf (Type u)) :
    compMap f g fg hfg G ≫
      (pushforward (Type u) f).map (compMap h fg q hq G) =
    compMap (h ≫ f) g q hq' G := by
  subst fg
  subst q
  unfold compMap
  simp only [eqToHom_refl]
  exact TopCat.Sheaf.compUnit_comp h f g G

private theorem compIso_square {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D)
    (fg : B ⟶ D) (hfg : f ≫ g = fg)
    (hf : A ⟶ C) (hhf : h ≫ f = hf)
    (q : A ⟶ D) (hq : h ≫ fg = q) (hq' : hf ≫ g = q)
    (G : D.Sheaf (Type u)) :
    (compIso f g fg hfg G).hom ≫ compMap h fg q hq G =
      compMap h f hf hhf ((pullback (Type u) g).obj G) ≫
        (pushforward (Type u) h).map (compIso hf g q hq' G).hom := by
  subst hf
  apply ((pullbackPushforwardAdjunction (Type u) f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, ← compMap_compIso,
    compMap_associativity h f g fg hfg q hq hq']
  rw [Functor.map_comp, ← Category.assoc]
  have hu : (pullbackPushforwardAdjunction (Type u) f).unit.app
        ((pullback (Type u) g).obj G) ≫
      (pushforward (Type u) f).map
        (compMap h f (h ≫ f) rfl ((pullback (Type u) g).obj G)) =
      (pullbackPushforwardAdjunction (Type u) (h ≫ f)).unit.app
        ((pullback (Type u) g).obj G) := by
    unfold compMap
    simp only [eqToHom_refl]
    exact TopCat.Sheaf.compUnit_unit h f _
  rw [hu]
  exact compMap_compIso (h ≫ f) g q hq' G

/- Apply fixed-sheaf continuity at the full open, then change to an ambient sheaf. -/
private theorem fixed_spectral_sections
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (S : J → TopCat.{u}) [∀ j : J, SpectralSpace (S j)]
    (f : ∀ (j k : J), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : J) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : J, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : J) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (E : TopCat.{u}) (p : ∀ j : J, E ⟶ S j)
    (hpcomp : ∀ (j k : J) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : J, S j,
      (∀ (j k : J) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : E, ∀ j : J, p j x = a j)
    (htop : E.str = ⨅ j : J, TopologicalSpace.induced (p j) (S j).str)
    (i : J) (G : (S i).Sheaf (Type u)) :
    (∀ s : ((pullback (Type u) (p i)).obj G).obj.obj (op ⊤),
      ∃ (j : J) (hij : i ≤ j)
        (a : ((pullback (Type u) (f i j hij)).obj G).obj.obj (op ⊤)),
        (compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app (op ⊤) a = s) ∧
    (∀ (j : J) (hij : i ≤ j)
        (a b : ((pullback (Type u) (f i j hij)).obj G).obj.obj (op ⊤)),
      (compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app (op ⊤) a =
        (compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app (op ⊤) b →
      ∃ (k : J) (hjk : j ≤ k),
        (compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
          (hfcomp i j k hij hjk) G).hom.app (op ⊤) a =
        (compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
          (hfcomp i j k hij hjk) G).hom.app (op ⊤) b) := by
  have h := spectralLimit_pullback_sections S f hf hfid hfcomp E p hpcomp hlimit htop
    i G ⊤ isCompact_univ
    (fun j hij a ↦ (compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app (op ⊤) a)
    (fun j k hij hjk a ↦ (compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
      (hfcomp i j k hij hjk) G).hom.app (op ⊤) a)
    (by
      intro j hij a
      have h := compMap_heq (p j) (f i j hij) (p i) (hpcomp i j hij) G ⊤ a
      unfold compUnit at h
      exact h)
    (by
      intro j k hij hjk a
      have h := compMap_heq (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
        (hfcomp i j k hij hjk) G ⊤ a
      unfold compUnit at h
      exact h)
  exact h.2

private theorem ambient_spectral_sections
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (S : J → TopCat.{u}) [∀ j : J, SpectralSpace (S j)]
    (f : ∀ (j k : J), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : J) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : J, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : J) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (E : TopCat.{u}) (p : ∀ j : J, E ⟶ S j)
    (hpcomp : ∀ (j k : J) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : J, S j,
      (∀ (j k : J) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : E, ∀ j : J, p j x = a j)
    (htop : E.str = ⨅ j : J, TopologicalSpace.induced (p j) (S j).str)
    (Z : TopCat.{u}) (e : ∀ j : J, S j ⟶ Z) (q : E ⟶ Z)
    (he : ∀ (j k : J) (h : j ≤ k), f j k h ≫ e j = e k)
    (hq : ∀ j : J, p j ≫ e j = q) (i : J) (G : Z.Sheaf (Type u)) :
    (∀ s : ((pullback (Type u) q).obj G).obj.obj (op ⊤),
      ∃ (j : J) (_hij : i ≤ j)
        (a : ((pullback (Type u) (e j)).obj G).obj.obj (op ⊤)),
        (compMap (p j) (e j) q (hq j) G).hom.app (op ⊤) a = s) ∧
    (∀ (j : J) (_hij : i ≤ j)
        (a b : ((pullback (Type u) (e j)).obj G).obj.obj (op ⊤)),
      (compMap (p j) (e j) q (hq j) G).hom.app (op ⊤) a =
        (compMap (p j) (e j) q (hq j) G).hom.app (op ⊤) b →
      ∃ (k : J) (hjk : j ≤ k),
        (compMap (f j k hjk) (e j) (e k) (he j k hjk) G).hom.app (op ⊤) a =
        (compMap (f j k hjk) (e j) (e k) (he j k hjk) G).hom.app (op ⊤) b) := by
  let Gi := (pullback (Type u) (e i)).obj G
  let Ei := compIso (p i) (e i) q (hq i) G
  let Ej (j : J) (hij : i ≤ j) := compIso (f i j hij) (e i) (e j) (he i j hij) G
  have hEi := (CategoryTheory.isIso_iff_bijective (Ei.hom.hom.app (op ⊤))).mp
    inferInstance
  have hEj (j : J) (hij : i ≤ j) :=
    (CategoryTheory.isIso_iff_bijective ((Ej j hij).hom.hom.app (op ⊤))).mp inferInstance
  have square (j : J) (hij : i ≤ j)
      (a : ((pullback (Type u) (f i j hij)).obj Gi).obj.obj (op ⊤)) :
      (compMap (p j) (e j) q (hq j) G).hom.app (op ⊤)
          ((Ej j hij).hom.hom.app (op ⊤) a) =
        Ei.hom.hom.app (op ⊤)
          ((compMap (p j) (f i j hij) (p i) (hpcomp i j hij) Gi).hom.app (op ⊤) a) :=
    congrArg (fun m ↦ m.hom.app (op ⊤) a)
      (compIso_square (p j) (f i j hij) (e i) (e j) (he i j hij)
        (p i) (hpcomp i j hij) q (hq j) (hq i) G)
  obtain ⟨hrep, heq⟩ := fixed_spectral_sections S f hf hfid hfcomp E p hpcomp
    hlimit htop i Gi
  constructor
  · intro s
    obtain ⟨s', hs'⟩ := hEi.2 s
    obtain ⟨j, hij, a, ha⟩ := hrep s'
    refine ⟨j, hij, (Ej j hij).hom.hom.app (op ⊤) a, ?_⟩
    rw [square, ha, hs']
  · intro j hij a b hab
    obtain ⟨a', ha'⟩ := (hEj j hij).2 a
    obtain ⟨b', hb'⟩ := (hEj j hij).2 b
    have hab0 : (compMap (p j) (e j) q (hq j) G).hom.app (op ⊤)
        ((Ej j hij).hom.hom.app (op ⊤) a') =
        (compMap (p j) (e j) q (hq j) G).hom.app (op ⊤)
          ((Ej j hij).hom.hom.app (op ⊤) b') := by
      rw [ha', hb']
      exact hab
    have hab' := hEi.1 ((square j hij a').symm.trans
      (hab0.trans (square j hij b')))
    obtain ⟨k, hjk, hk⟩ := heq j hij a' b' hab'
    refine ⟨k, hjk, ?_⟩
    have sq := compIso_square (f j k hjk) (f i j hij) (e i)
      (e j) (he i j hij) (f i k (hij.trans hjk)) (hfcomp i j k hij hjk)
      (e k) (he j k hjk) (he i k (hij.trans hjk)) G
    have hka := congrArg (fun m ↦ m.hom.app (op ⊤) a') sq
    have hkb := congrArg (fun m ↦ m.hom.app (op ⊤) b') sq
    change (compMap (f j k hjk) (e j) (e k) (he j k hjk) G).hom.app (op ⊤)
        ((Ej j hij).hom.hom.app (op ⊤) a') = _ at hka
    change (compMap (f j k hjk) (e j) (e k) (he j k hjk) G).hom.app (op ⊤)
        ((Ej j hij).hom.hom.app (op ⊤) b') = _ at hkb
    rw [ha'] at hka
    rw [hb'] at hkb
    exact hka.trans ((congrArg ((Ej k (hij.trans hjk)).hom.hom.app (op ⊤)) hk).trans
      hkb.symm)

@[irreducible] private noncomputable def globalMap {A B : TopCat.{u}} (f : A ⟶ B)
    {F : B.Sheaf (Type u)} {H : A.Sheaf (Type u)}
    (m : F ⟶ (pushforward (Type u) f).obj H) :
    F.obj.obj (op ⊤) ⟶ H.obj.obj (op ⊤) :=
  m.hom.app (op ⊤)

@[irreducible] private noncomputable def unitToTop {A Z : TopCat.{u}} (f : A ⟶ Z)
    (G : Z.Sheaf (Type u)) (V : TopologicalSpace.Opens Z) (h : ∀ x : A, f x ∈ V) :
    G.obj.obj (op V) ⟶ ((pullback (Type u) f).obj G).obj.obj (op ⊤) :=
  ((pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app (op V) ≫
    ((pullback (Type u) f).obj G).obj.map (homOfLE (fun x _ ↦ h x)).op

private theorem compMap_unitToTop {A B Z : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ Z) (k : A ⟶ Z) (h : f ≫ g = k)
    (G : Z.Sheaf (Type u)) (V : TopologicalSpace.Opens Z)
    (hB : ∀ x : B, g x ∈ V) (hA : ∀ x : A, k x ∈ V) :
    unitToTop g G V hB ≫ globalMap f (compMap f g k h G) = unitToTop k G V hA := by
  subst k
  let m := compMap f g (f ≫ g) rfl G
  have hu : (pullbackPushforwardAdjunction (Type u) g).unit.app G ≫
      (pushforward (Type u) g).map m =
      (pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G := by
    unfold m compMap
    simp only [eqToHom_refl]
    exact TopCat.Sheaf.compUnit_unit f g G
  have huV := congrArg (fun a ↦ a.hom.app (op V)) hu
  change ((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app (op V) ≫
    m.hom.app (op ((Opens.map g).obj V)) = _ at huV
  have hn := m.hom.naturality
    (homOfLE (show (⊤ : TopologicalSpace.Opens B) ≤ (Opens.map g).obj V
      from fun x _ ↦ hB x)).op
  unfold unitToTop globalMap
  rw [Category.assoc]
  erw [hn, ← Category.assoc, huV]
  rfl

private theorem unitToTop_naturality {A Z : TopCat.{u}} (f : A ⟶ Z)
    (G : Z.Sheaf (Type u)) (V W : TopologicalSpace.Opens Z) (hWV : W ≤ V)
    (hW : ∀ x : A, f x ∈ W) :
    G.obj.map (homOfLE hWV).op ≫ unitToTop f G W hW =
      unitToTop f G V (fun x ↦ hWV (hW x)) := by
  let η := ((pullbackPushforwardAdjunction (Type u) f).unit.app G).hom
  have hn := η.naturality (homOfLE hWV).op
  dsimp [η] at hn
  unfold unitToTop
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  congr 1

end IntersectionProof

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_sets_sections
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hqc : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j)
    (G : X.toTopCat.Sheaf (Type u)) (i₀ : I) :
    (∀ s : ((TopCat.Sheaf.pullback (Type u) (intersectionInclusion X U)).obj G).obj.obj
        (op ⊤), ∃ (i : I) (a : G.obj.obj (op (U i))),
      TopCat.Sheaf.subspaceSectionMap (Type u) {x : X | ∀ j : I, x ∈ U j}
        G (U i) (fun _ hx ↦ hx i) a = s) ∧
    (∀ a b : G.obj.obj (op (U i₀)),
      TopCat.Sheaf.subspaceSectionMap (Type u) {x : X | ∀ j : I, x ∈ U j}
        G (U i₀) (fun _ hx ↦ hx i₀) a =
      TopCat.Sheaf.subspaceSectionMap (Type u) {x : X | ∀ j : I, x ∈ U j}
        G (U i₀) (fun _ hx ↦ hx i₀) b →
      ∃ (k : I) (hki : U k ≤ U i₀),
        G.obj.map (homOfLE hki).op a = G.obj.map (homOfLE hki).op b) := by
  classical
  obtain ⟨hsmall, hne, hd, hleast, hcof, hinter, hspec, hmaps, hlim, hpoints, htop⟩ :=
    qcOpenIntersection_spectral_presentation X U hqc hdir i₀
  let K := qcOpenIntersectionIndex U i₀
  let : PartialOrder K := inferInstanceAs (PartialOrder (qcOpenIntersectionIndex U i₀))
  let r : K ≃o qcOpenIntersectionIndex U i₀ := OrderIso.refl _
  have : Nonempty K := hne
  have : IsDirected K (· ≤ ·) := hd
  let S (j : K) : TopCat.{u} := TopCat.of (r j).val
  let f (j k : K) (h : j ≤ k) : S k ⟶ S j :=
    (Opens.toTopCat X.toTopCat).map (homOfLE (r.monotone h))
  let p (j : K) : TopCat.of {x : X // ∀ i : I, x ∈ U i} ⟶ S j :=
    (qcOpenIntersectionCone U i₀).π.app (op (r j))
  let e (j : K) : S j ⟶ X.toTopCat := (r j).val.inclusion'
  have : ∀ j : K, SpectralSpace (S j) := fun j ↦ (hspec (r j)).2
  have hf (j k : K) (h : j ≤ k) : IsSpectralMap (f j k h) :=
    hmaps (op (r k)) (op (r j)) (homOfLE (r.monotone h)).op
  have hfid (j : K) : f j j le_rfl = 𝟙 (S j) := rfl
  have hfcomp (j k l : K) (hjk : j ≤ k) (hkl : k ≤ l) :
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl) := rfl
  have hpcomp (j k : K) (h : j ≤ k) : p k ≫ f j k h = p j := rfl
  have hpoints' : ∀ a : ∀ j : K, S j,
      (∀ (j k : K) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : TopCat.of {x : X // ∀ i : I, x ∈ U i}, ∀ j : K, p j x = a j := by
    intro a ha
    obtain ⟨x, hx, hu⟩ := hpoints (fun j ↦ a j.unop)
      (fun j k g ↦ ha k.unop j.unop (leOfHom g.unop))
    refine ⟨x, fun j ↦ hx (op j), ?_⟩
    intro y hy
    exact hu y (fun j ↦ hy j.unop)
  have htop' : (TopCat.of {x : X // ∀ i : I, x ∈ U i}).str =
      ⨅ j : K, TopologicalSpace.induced (p j) (S j).str := by
    change (inferInstance : TopologicalSpace (qcOpenIntersectionCone U i₀).pt) = _
    rw [htop]
    apply le_antisymm
    · exact le_iInf fun j ↦ iInf_le _ (op j)
    · exact le_iInf fun j ↦ iInf_le _ j.unop
  let j₀ : K := r.symm ⟨U i₀, ⟨⟨i₀, rfl⟩, le_rfl⟩⟩
  have he (j k : K) (h : j ≤ k) : f j k h ≫ e j = e k := rfl
  have hq (j : K) : p j ≫ e j = intersectionInclusion X U := rfl
  obtain ⟨hrep, heq⟩ := IntersectionProof.ambient_spectral_sections S f hf hfid hfcomp _ p
    hpcomp hpoints' htop' X.toTopCat e (intersectionInclusion X U) he hq j₀ G
  let lift (j : K) := TopCat.Sheaf.subspaceSectionMap (Type u) ((r j).val : Set X) G
    (r j).val (fun _ hx ↦ hx)
  have hlift (j : K) : Function.Bijective (lift j) := sets_open_unit_bijective G _
  have square (j : K) :
      lift j ≫ IntersectionProof.globalMap (p j)
          (TopCat.Sheaf.compMap (p j) (e j) (intersectionInclusion X U) (hq j) G) =
        TopCat.Sheaf.subspaceSectionMap (Type u) {x : X | ∀ i : I, x ∈ U i}
          G (r j).val (fun _ hx ↦ (r j).property.1.elim (fun i hi ↦ hi ▸ hx i)) := by
    have hs := IntersectionProof.compMap_unitToTop (p j) (e j)
      (intersectionInclusion X U) (hq j) G (r j).val (fun x ↦ x.property)
      (fun x ↦ (r j).property.1.elim (fun i hi ↦ hi ▸ x.property i))
    unfold IntersectionProof.unitToTop at hs
    unfold lift TopCat.Sheaf.subspaceSectionMap
    convert hs using 1 <;> rfl
  have trans_square (j k : K) (h : j ≤ k) :
      lift j ≫ IntersectionProof.globalMap (f j k h)
          (TopCat.Sheaf.compMap (f j k h) (e j) (e k) (he j k h) G) =
        G.obj.map (homOfLE (r.monotone h)).op ≫ lift k := by
    have hsq := IntersectionProof.compMap_unitToTop
      (f j k h) (e j) (e k) (he j k h) G (r j).val
      (fun x ↦ x.property) (fun x ↦ r.monotone h x.property)
    have hn := (IntersectionProof.unitToTop_naturality (e k) G (r j).val (r k).val
      (r.monotone h) (fun x ↦ x.property)).symm
    have hs := hsq.trans hn
    unfold IntersectionProof.unitToTop at hs
    unfold lift TopCat.Sheaf.subspaceSectionMap
    convert hs using 1 <;> rfl
  constructor
  · intro s
    obtain ⟨j, hij, a, ha⟩ := hrep s
    rcases j with ⟨W, ⟨⟨i, rfl⟩, hW⟩⟩
    let j : K := ⟨U i, ⟨⟨i, rfl⟩, hW⟩⟩
    obtain ⟨b, hb⟩ := (hlift j).2 a
    have hsq := ConcreteCategory.congr_hom (square j) b
    have hsa : (lift j ≫ IntersectionProof.globalMap (p j)
        (TopCat.Sheaf.compMap (p j) (e j) (intersectionInclusion X U) (hq j) G)) b =
        s := by
      unfold IntersectionProof.globalMap
      change (TopCat.Sheaf.compMap (p j) (e j) (intersectionInclusion X U)
        (hq j) G).hom.app (op ⊤) (lift j b) = s
      rw [hb, ha]
    have hres := hsq.symm.trans hsa
    exact ⟨i, b, hres⟩
  · intro a b hab
    let a' : G.obj.obj (op (r j₀).val) := a
    let b' : G.obj.obj (op (r j₀).val) := b
    have hab' :
        (TopCat.Sheaf.compMap (p j₀) (e j₀) (intersectionInclusion X U)
            (hq j₀) G).hom.app (op ⊤) (lift j₀ a') =
        (TopCat.Sheaf.compMap (p j₀) (e j₀) (intersectionInclusion X U)
            (hq j₀) G).hom.app (op ⊤) (lift j₀ b') := by
      have ha := ConcreteCategory.congr_hom (square j₀) a'
      have hb := ConcreteCategory.congr_hom (square j₀) b'
      simp only [ConcreteCategory.comp_apply, IntersectionProof.globalMap] at ha hb
      change (TopCat.Sheaf.compMap (p j₀) (e j₀) (intersectionInclusion X U)
        (hq j₀) G).hom.app (op ⊤) (lift j₀ a') = _ at ha
      change (TopCat.Sheaf.compMap (p j₀) (e j₀) (intersectionInclusion X U)
        (hq j₀) G).hom.app (op ⊤) (lift j₀ b') = _ at hb
      exact ha.trans (hab.trans hb.symm)
    obtain ⟨k, hjk, hk⟩ := heq j₀ le_rfl (lift j₀ a') (lift j₀ b') hab'
    rcases k with ⟨W, ⟨⟨l, rfl⟩, hW⟩⟩
    have ha := ConcreteCategory.congr_hom (trans_square j₀ ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩ hjk) a'
    have hb := ConcreteCategory.congr_hom (trans_square j₀ ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩ hjk) b'
    simp only [ConcreteCategory.comp_apply, IntersectionProof.globalMap] at ha hb
    change (TopCat.Sheaf.compMap (f j₀ ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩ hjk) (e j₀)
      (e ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩)
        (he j₀ ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩ hjk) G).hom.app
      (op ⊤) (lift j₀ a') = _ at ha
    change (TopCat.Sheaf.compMap (f j₀ ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩ hjk) (e j₀)
      (e ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩)
        (he j₀ ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩ hjk) G).hom.app
      (op ⊤) (lift j₀ b') = _ at hb
    have habk := (hlift ⟨U l, ⟨⟨l, rfl⟩, hW⟩⟩).1 (ha.symm.trans (hk.trans hb))
    exact ⟨l, hW, habk⟩


private theorem ringSetPullbackIso_restriction
    (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (W : X.Opens) (hW : ∀ x : X, (∀ i : I, x ∈ U i) → x ∈ W)
    (a : X.presheaf.obj (op W)) :
    ((ringSetPullbackIso (intersectionInclusion X U)).hom.app X.sheaf).hom.app (op ⊤)
      (TopCat.Sheaf.subspaceSectionMap (Type u) {x : X | ∀ i : I, x ∈ U i}
        ((sheafCompose (Opens.grothendieckTopology X.toTopCat)
          (CategoryTheory.forget CommRingCat)).obj X.sheaf) W (fun x hx ↦ hW x hx) a) =
      intersectionRestriction X U W hW a := by
  let α := ((ringSetPullbackIso (intersectionInclusion X U)).hom.app X.sheaf).hom
  have hn := ConcreteCategory.congr_hom (α.naturality
    (homOfLE (show (⊤ : TopologicalSpace.Opens {x : X // ∀ i : I, x ∈ U i}) ≤
      (Opens.map (intersectionInclusion X U)).obj W from fun x _ ↦ hW x.val x.property)).op)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
      (intersectionInclusion X U)).unit.app
        ((sheafCompose (Opens.grothendieckTopology X.toTopCat)
          (CategoryTheory.forget CommRingCat)).obj X.sheaf)).hom.app (op W) a)
  change _ = _ at hn
  unfold TopCat.Sheaf.subspaceSectionMap intersectionRestriction
  change α.app (op ⊤) _ = _
  erw [hn]
  simp only [ConcreteCategory.comp_apply]
  dsimp only [α]
  erw [ringSetPullbackIso_unit]
  rfl

private theorem intersection_ring_sections
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hqc : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) :
    (∀ s : intersectionSections X U, ∃ (i : I) (a : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun _ hx ↦ hx i) a = s) ∧
    (∀ (i : I) (a b : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun _ hx ↦ hx i) a =
        intersectionRestriction X U (U i) (fun _ hx ↦ hx i) b →
      ∃ (k : I) (hki : U k ≤ U i),
        X.presheaf.map (homOfLE hki).op a = X.presheaf.map (homOfLE hki).op b) := by
  let G := (sheafCompose (Opens.grothendieckTopology X.toTopCat)
    (CategoryTheory.forget CommRingCat)).obj X.sheaf
  let α := ((ringSetPullbackIso (intersectionInclusion X U)).hom.app X.sheaf).hom.app
    (op ⊤)
  have hα := (CategoryTheory.isIso_iff_bijective α).mp inferInstance
  constructor
  · intro s
    obtain ⟨s', hs'⟩ := hα.2 s
    obtain ⟨i, a, ha⟩ := (intersection_sets_sections X U hqc hdir G
      (Classical.choice inferInstance)).1 s'
    refine ⟨i, a, ?_⟩
    rw [← ringSetPullbackIso_restriction]
    exact (congrArg α ha).trans hs'
  · intro i a b hab
    apply (intersection_sets_sections X U hqc hdir G i).2 a b
    apply hα.1
    change ((ringSetPullbackIso (intersectionInclusion X U)).hom.app X.sheaf).hom.app
      (op ⊤) _ = _
    rw [ringSetPullbackIso_restriction, ringSetPullbackIso_restriction]
    exact hab

private theorem intersectionRestriction_naturality
    (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (W V : X.Opens) (hWV : W ≤ V)
    (hW : ∀ x : X, (∀ i : I, x ∈ U i) → x ∈ W) :
    X.presheaf.map (homOfLE hWV).op ≫ intersectionRestriction X U W hW =
      intersectionRestriction X U V (fun x hx ↦ hWV (hW x hx)) := by
  let η := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion X U)).unit.app X.sheaf).hom
  have hn := η.naturality (homOfLE hWV).op
  unfold intersectionRestriction
  dsimp [η] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  congr 1

/- The transport is the adjoint of the scheme sheaf map followed by the source unit. -/
private theorem intersection_transport
    {X Y : Scheme.{u}} (g : X ⟶ Y) {I : Type v}
    (U : I → X.Opens) (V : I → Y.Opens)
    (hUV : ∀ i : I, U i = g ⁻¹ᵁ V i) :
    ∃! t : intersectionStructureSheaf Y V ⟶
        (TopCat.Sheaf.pushforward CommRingCat
          (intersectionMap g U V (fun i ↦ (hUV i).le))).obj
            (intersectionStructureSheaf X U),
      (∀ W : Y.Opens,
        HEq
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
              (intersectionInclusion Y V)).unit.app Y.sheaf).hom.app (op W) ≫
            t.hom.app (op ((Opens.map (intersectionInclusion Y V)).obj W)))
          (g.app W ≫
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
              (intersectionInclusion X U)).unit.app X.sheaf).hom.app
                (op (g ⁻¹ᵁ W)))) ∧
      (∀ i : I,
        intersectionRestriction Y V (V i) (fun _ hy ↦ hy i) ≫
            t.hom.app (op ⊤) ≫
              (intersectionStructureSheaf X U).obj.map
                (homOfLE (fun _ _ ↦ trivial)).op =
          g.appLE (V i) (U i) (hUV i).le ≫
            intersectionRestriction X U (U i) (fun _ hx ↦ hx i)) := by
  let ηX := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion X U)).unit.app X.sheaf
  let e := intersectionInclusion Y V
  let f := intersectionMap g U V (fun i ↦ (hUV i).le)
  let H := (TopCat.Sheaf.pushforward CommRingCat f).obj (intersectionStructureSheaf X U)
  let m : Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat e).obj H :=
    ⟨g.c ≫ ((TopCat.Presheaf.pushforward CommRingCat g.base).map ηX.hom)⟩
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat e
  let t := (adj.homEquiv Y.sheaf H).symm m
  have ht : adj.unit.app Y.sheaf ≫ (TopCat.Sheaf.pushforward CommRingCat e).map t = m :=
    (adj.homEquiv _ _).apply_symm_apply m
  have hunit (W : Y.Opens) :
      ((adj.unit.app Y.sheaf).hom.app (op W)) ≫
        t.hom.app (op ((Opens.map e).obj W)) =
      g.app W ≫ ηX.hom.app (op (g ⁻¹ᵁ W)) :=
    congrArg (fun a ↦ a.hom.app (op W)) ht
  refine ⟨t, ⟨fun W ↦ heq_of_eq (hunit W), ?_⟩, ?_⟩
  · intro i
    have hright : g.appLE (V i) (U i) (hUV i).le ≫
        intersectionRestriction X U (U i) (fun _ hx ↦ hx i) =
        g.app (V i) ≫ intersectionRestriction X U (g ⁻¹ᵁ V i)
          (fun x hx ↦ (hUV i).le (hx i)) := by
      unfold Hom.appLE
      rw [Category.assoc, intersectionRestriction_naturality]
    rw [hright]
    unfold intersectionRestriction
    have hn := t.hom.naturality
      (homOfLE (show (⊤ : TopologicalSpace.Opens (TopCat.of {y : Y // ∀ j, y ∈ V j})) ≤
        (Opens.map e).obj (V i) from fun y _ ↦ y.property i)).op
    simp only [Category.assoc]
    erw [← Category.assoc _ (t.hom.app (op ⊤)), hn]
    erw [← Category.assoc, ← Category.assoc, hunit]
    change g.app (V i) ≫ ηX.hom.app (op (g ⁻¹ᵁ V i)) ≫
      (intersectionStructureSheaf X U).obj.map _ ≫
        (intersectionStructureSheaf X U).obj.map _ = _
    rw [← Functor.map_comp]
    rfl
  · intro t' ht'
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ht]
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    exact eq_of_heq (ht'.1 W.unop)

set_option linter.unusedVariables false in
/-- Structure-sheaf sections on a directed intersection are the filtered colimit, in sets,
abelian groups and commutative rings, naturally under scheme isomorphisms. The final clause
specifies the canonical sheaf transport by its adjunction-unit equation on every open,
then states its square with the section restrictions. Thus no unspecified comparison map
is assumed. Distinct opens index the colimit; the elementwise clauses retain the original
indexing, including repetitions.

Source: Stacks, equation `equation-sections-of-intersection` preceding Tag 0APJ
(blueprint: lem-a1-sections-intersection-structure-colimit).

Proof:
1. Fix a member of the family and use the spectral presentation by the distinct
   indicated opens contained in it. Apply fixed-sheaf spectral continuity at the full
   compact open of the fixed member.
2. The unit-compatible composition isomorphisms transfer this statement to pullbacks
   of the ambient sheaf. The open-embedding unit is bijective on global sections;
   its naturality identifies the transition maps with ordinary restrictions. The
   ring-to-set inverse-image comparison preserves these units, yielding representatives
   and eventual equality for the structure sheaf.
3. Index all distinct opens by reverse inclusion. Apply directed-ring cocone recognition
   to these two elementwise properties, then transport its three colimits through the
   equivalence between the order-dual and opposite categories.
4. Construct the sheaf transport directly by the inverse-image adjunction. Its unit
   equation characterizes it uniquely; naturality gives its restriction squares.
All constructions allow an empty intersection and repeated members. -/
theorem sections_intersection_structure_colimit
    (X : Scheme.{u}) [QuasiSeparatedSpace X] {I : Type v} [Nonempty I]
    (U : I → X.Opens) (hqc : ∀ i : I, IsCompact (U i : Set X))
    (hdir : ∀ i j : I, ∃ k : I, U k ≤ U i ⊓ U j) :
    (∀ s : intersectionSections X U, ∃ (i : I) (a : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a = s) ∧
    (∀ (i : I) (a a' : X.presheaf.obj (op (U i))),
      intersectionRestriction X U (U i) (fun x hx ↦ hx i) a =
        intersectionRestriction X U (U i) (fun x hx ↦ hx i) a' →
      ∃ (k : I) (hki : U k ≤ U i),
        X.presheaf.map (homOfLE hki).op a = X.presheaf.map (homOfLE hki).op a') ∧
    (∃ ι : intersectionOpenDiagram X U ⟶
        (Functor.const _).obj (intersectionSections X U),
      (∀ V, ι.app V = intersectionRestriction X U V.unop.val
        (fun x hx ↦ V.unop.property.elim (fun i hi ↦ hi ▸ hx i))) ∧
      Nonempty (IsColimit (Cocone.mk (intersectionSections X U) ι)) ∧
      Nonempty (IsColimit ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι))) ∧
      Nonempty (IsColimit ((CategoryTheory.forget CommRingCat).mapCocone
        (Cocone.mk (intersectionSections X U) ι)))) ∧
    (∀ (Y : Scheme.{u}) (g : X ≅ Y) (V : I → Y.Opens)
        (hUV : ∀ i : I, U i = g.hom ⁻¹ᵁ V i),
      ∃! t : intersectionStructureSheaf Y V ⟶
          (TopCat.Sheaf.pushforward CommRingCat
            (intersectionMap g.hom U V (fun i ↦ (hUV i).le))).obj
              (intersectionStructureSheaf X U),
        (∀ W : Y.Opens,
          HEq
            (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion Y V)).unit.app Y.sheaf).hom.app (op W) ≫
              t.hom.app (op ((Opens.map (intersectionInclusion Y V)).obj W)))
            (g.hom.app W ≫
              ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
                (intersectionInclusion X U)).unit.app X.sheaf).hom.app
                  (op (g.hom ⁻¹ᵁ W)))) ∧
        (∀ i : I,
          intersectionRestriction Y V (V i) (fun y hy ↦ hy i) ≫
              t.hom.app (op ⊤) ≫
                (intersectionStructureSheaf X U).obj.map
                  (homOfLE (fun _ _ ↦ trivial)).op =
            g.hom.appLE (V i) (U i) (hUV i).le ≫
              intersectionRestriction X U (U i) (fun x hx ↦ hx i))) := by
  classical
  obtain ⟨hrep, heq⟩ := intersection_ring_sections X U hqc hdir
  refine ⟨hrep, heq, ?_, fun Y g V hUV ↦ intersection_transport g.hom U V hUV⟩
  let ι : intersectionOpenDiagram X U ⟶
      (Functor.const _).obj (intersectionSections X U) :=
    { app := fun V ↦ intersectionRestriction X U V.unop.val
        (fun _ hx ↦ V.unop.property.elim (fun i hi ↦ hi ▸ hx i))
      naturality := by
        intro V W f
        exact intersectionRestriction_naturality X U W.unop.val V.unop.val
          (leOfHom f.unop) _ }
  refine ⟨ι, fun _ ↦ rfl, ?_⟩
  let J := OrderDual {V : X.Opens // V ∈ Set.range U}
  let eqv := orderDualEquivalence {V : X.Opens // V ∈ Set.range U}
  have : Nonempty J := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨⟨U i, ⟨i, rfl⟩⟩⟩
  have : IsDirected J (· ≤ ·) := ⟨fun V W ↦ by
    obtain ⟨i, hi⟩ := V.property
    obtain ⟨j, hj⟩ := W.property
    obtain ⟨k, hk⟩ := hdir i j
    refine ⟨⟨U k, ⟨k, rfl⟩⟩, ?_, ?_⟩
    · change U k ≤ V.val
      rw [← hi]
      exact hk.trans inf_le_left
    · change U k ≤ W.val
      rw [← hj]
      exact hk.trans inf_le_right⟩
  let c : Cocone (intersectionOpenDiagram X U) := Cocone.mk _ ι
  let F := eqv.functor ⋙ intersectionOpenDiagram X U
  let d := c.whisker eqv.functor
  have hrep' : ∀ s : d.pt, ∃ (j : J) (a : F.obj j), d.ι.app j a = s := by
    intro s
    obtain ⟨i, a, ha⟩ := hrep s
    exact ⟨⟨U i, ⟨i, rfl⟩⟩, a, ha⟩
  have heq' : ∀ (j : J) (a b : F.obj j),
      d.ι.app j a = d.ι.app j b →
      ∃ (k : J) (hjk : j ≤ k), F.map (homOfLE hjk) a = F.map (homOfLE hjk) b := by
    intro j a b hab
    obtain ⟨i, hi⟩ := j.property
    have hj : j = (⟨U i, ⟨i, rfl⟩⟩ : J) := Subtype.ext hi.symm
    subst j
    obtain ⟨k, hk, he⟩ := heq i a b hab
    exact ⟨⟨U k, ⟨k, rfl⟩⟩, hk, he⟩
  obtain ⟨hR, hA, hS, _⟩ := CommRingCat.directed_cocone_recognition F d hrep' heq'
  refine ⟨⟨IsColimit.ofWhiskerEquivalence eqv hR⟩, ?_, ?_⟩
  · exact ⟨IsColimit.ofWhiskerEquivalence eqv hA⟩
  · exact ⟨IsColimit.ofWhiskerEquivalence eqv hS⟩

end AlgebraicGeometry.Scheme
