/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineLogEtaleDescentDatum
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.AlgebraicGeometry.Sites.Gm
import WeilConjectures.AlgebraicGeometry.FineLogEtaleDescentExistence

/-!
# Étale descent of fine log structures and arbitrary prelog morphisms

Source: ILO, Exposé VI 1.1 and Exposé VIII 3.3.8, pp. 69, 107--108;
Stacks, Tags 04TR and 04TQ (blueprint: lem-trf-fine-log-structure-etale-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Joint surjectivity makes the étale objects cover the terminal object. -/
private theorem etale_coversTop
    {T : Scheme.{u}} {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x) :
    T.smallEtaleTopology.CoversTop U := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal T.smallEtaleTopology
    (Scheme.Etale.mk (𝟙 T)) (MorphismProperty.Over.mkIdTerminal (@Etale) T)]
  let f (a : ι) : U a ⟶ Scheme.Etale.mk (𝟙 T) :=
    MorphismProperty.Over.homMk (U a).hom (Category.comp_id _)
  rw [← Sieve.ofArrows_eq_ofObjects
    (MorphismProperty.Over.mkIdTerminal (@Etale) T) U f]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).2
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨a, y, hy⟩ := hcover x
  exact Set.mem_iUnion.mpr ⟨a, y, hy⟩

/-- A natural transformation into a sheaf is determined by its slice restrictions. -/
private theorem natTrans_ext_cover
    {T : Scheme.{u}} {ι : Type v} (U : ι → T.Etale)
    (hc : T.smallEtaleTopology.CoversTop U)
    (A B : T.Etaleᵒᵖ ⥤ CommMonCat.{u})
    (hB : Presheaf.IsSheaf T.smallEtaleTopology B) (f g : A ⟶ B)
    (heq : ∀ (a : ι) (V : T.Etale) (_k : V ⟶ U a),
      f.app (op V) = g.app (op V)) : f = g := by
  apply (presheafHomSectionsEquiv A B).symm.injective
  apply hc.sections_ext ⟨presheafHom A B, hB.hom A⟩
  intro a
  apply NatTrans.ext
  funext V
  exact heq a V.unop.left V.unop.hom

/-- Glue arbitrary prelog morphisms using the sheaf of natural transformations. -/
private theorem prelogHom_glue
    {T : Scheme.{u}} {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    (A B : EtalePrelogStructure T) (localHom : ∀ a : ι, A.LocalHom B (U a))
    (hover : ∀ (a b : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b),
      (localHom a).hom.app (op (Over.mk f)) =
        (localHom b).hom.app (op (Over.mk g))) :
    ∃! h : A.Hom B, ∀ (a : ι) (V : T.Etale) (f : V ⟶ U a),
      h.hom.app (op V) = (localHom a).hom.app (op (Over.mk f)) := by
  let hc := etale_coversTop U hcover
  let x : Presheaf.FamilyOfElementsOnObjects
      (presheafHom A.monoidSheaf.obj B.monoidSheaf.obj) U :=
    fun a ↦ (localHom a).hom
  have hx : x.IsCompatible := by
    intro W a b f g
    apply NatTrans.ext
    funext V
    exact hover a b V.unop.left (V.unop.hom ≫ f) (V.unop.hom ≫ g)
  obtain ⟨s, hs, _⟩ := hx.existsUnique_section hc
    (B.monoidSheaf.property.hom A.monoidSheaf.obj)
  let h := presheafHomSectionsEquiv A.monoidSheaf.obj B.monoidSheaf.obj s
  have hres (a : ι) :
      Functor.whiskerLeft (Over.forget (U a)).op h = (localHom a).hom := by
    change ((presheafHomSectionsEquiv _ _).symm h).val (op (U a)) = _
    rw [Equiv.symm_apply_apply]
    exact hs a
  have hh (a : ι) (V : T.Etale) (f : V ⟶ U a) :
      h.app (op V) = (localHom a).hom.app (op (Over.mk f)) :=
    congrArg (fun k ↦ k.app (op (Over.mk f))) (hres a)
  have hR : Presheaf.IsSheaf T.smallEtaleTopology
      (T.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ T.isSheaf_etaleStructurePresheaf
  have halpha : h ≫ B.alpha = A.alpha := by
    apply natTrans_ext_cover U hc _ _ hR
    intro a V f
    apply ConcreteCategory.hom_ext
    intro z
    change B.alpha.app (op V) (h.app (op V) z) = A.alpha.app (op V) z
    rw [hh a V f]
    exact (localHom a).alpha (Over.mk f) z
  refine ⟨⟨h, halpha⟩, hh, ?_⟩
  intro k hk
  have heq : k.hom = h := by
    apply natTrans_ext_cover U hc _ _ B.monoidSheaf.property
    intro a V f
    exact (hk a V f).trans (hh a V f).symm
  rcases k with ⟨k, ka⟩
  dsimp only at heq
  subst k
  rfl

/-- The local comparison is obtained by composing the two labelled identifications. -/
private def gluingComparison
    {T : Scheme.{u}} {ι : Type v} {U : ι → T.Etale}
    {D : FineLogEtaleDescentDatum U} {M N : EtaleLogStructure T}
    (e : D.Gluing M) (f : D.Gluing N) (a : ι) :
    M.toEtalePrelogStructure.LocalHom N.toEtalePrelogStructure (U a) where
  hom :=
    { app := fun V ↦ CommMonCat.ofHom
        (((e.component a V.unop.left V.unop.hom).trans
          (f.component a V.unop.left V.unop.hom).symm).toMonoidHom)
      naturality := by
        intro V W k
        apply ConcreteCategory.hom_ext
        intro z
        apply (f.component a W.unop.left W.unop.hom).injective
        change f.component a W.unop.left W.unop.hom
            ((f.component a W.unop.left W.unop.hom).symm
              (e.component a W.unop.left W.unop.hom
                (M.monoidSheaf.obj.map k.unop.left.op z))) =
          f.component a W.unop.left W.unop.hom
            (N.monoidSheaf.obj.map k.unop.left.op
              ((f.component a V.unop.left V.unop.hom).symm
                (e.component a V.unop.left V.unop.hom z)))
        rw [MulEquiv.apply_symm_apply]
        have he := e.naturality a V.unop.left W.unop.left V.unop.hom k.unop.left z
        have hf := f.naturality a V.unop.left W.unop.left V.unop.hom k.unop.left
          ((f.component a V.unop.left V.unop.hom).symm
            (e.component a V.unop.left V.unop.hom z))
        rw [← Over.w k.unop, he, hf, MulEquiv.apply_symm_apply] }
  alpha := by
    intro V z
    change N.alpha.app (op V.left)
        ((f.component a V.left V.hom).symm (e.component a V.left V.hom z)) =
      M.alpha.app (op V.left) z
    rw [← f.alpha a V.left V.hom, MulEquiv.apply_symm_apply, e.alpha]

/-- The cocycle equations force local comparison maps to agree on every overlap. -/
private theorem gluingComparison_overlap
    {T : Scheme.{u}} {ι : Type v} {U : ι → T.Etale}
    {D : FineLogEtaleDescentDatum U} {M N : EtaleLogStructure T}
    (e : D.Gluing M) (f : D.Gluing N)
    (a b : ι) (V : T.Etale) (k : V ⟶ U a) (l : V ⟶ U b) :
    (gluingComparison e f a).hom.app (op (Over.mk k)) =
      (gluingComparison e f b).hom.app (op (Over.mk l)) := by
  apply ConcreteCategory.hom_ext
  intro z
  apply (f.component b V l).injective
  change f.component b V l ((f.component a V k).symm (e.component a V k z)) =
    f.component b V l ((f.component b V l).symm (e.component b V l z))
  rw [← f.transition a b V k l, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, e.transition]

/-- Morphism gluing yields the unique isomorphism respecting two sets of labels. -/
private theorem gluing_unique
    {T : Scheme.{u}} {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x)
    {D : FineLogEtaleDescentDatum U} {M N : EtaleLogStructure T}
    (e : D.Gluing M) (f : D.Gluing N) :
    ∃! h : EtalePrelogStructure.Iso M.toEtalePrelogStructure N.toEtalePrelogStructure,
      ∀ (a : ι) (V : T.Etale) (g : V ⟶ U a) (s : M.monoidSheaf.obj.obj (op V)),
        f.component a V g (h.iso.hom.app (op V) s) = e.component a V g s := by
  obtain ⟨h, hh, _⟩ := prelogHom_glue U hcover _ _ (gluingComparison e f)
    (gluingComparison_overlap e f)
  obtain ⟨i, hi, _⟩ := prelogHom_glue U hcover _ _ (gluingComparison f e)
    (gluingComparison_overlap f e)
  have hhi : h.hom ≫ i.hom = 𝟙 _ := by
    apply natTrans_ext_cover U (etale_coversTop U hcover) _ _ M.monoidSheaf.property
    intro a V g
    apply ConcreteCategory.hom_ext
    intro z
    change i.hom.app (op V) (h.hom.app (op V) z) = z
    rw [hh a V g, hi a V g]
    change (e.component a V g).symm
      (f.component a V g ((f.component a V g).symm (e.component a V g z))) = z
    simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hih : i.hom ≫ h.hom = 𝟙 _ := by
    apply natTrans_ext_cover U (etale_coversTop U hcover) _ _ N.monoidSheaf.property
    intro a V g
    apply ConcreteCategory.hom_ext
    intro z
    change h.hom.app (op V) (i.hom.app (op V) z) = z
    rw [hh a V g, hi a V g]
    change (f.component a V g).symm
      (e.component a V g ((e.component a V g).symm (f.component a V g z))) = z
    simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  let E : EtalePrelogStructure.Iso M.toEtalePrelogStructure N.toEtalePrelogStructure :=
    ⟨⟨h.hom, i.hom, hhi, hih⟩, h.alpha⟩
  refine ⟨E, ?_, ?_⟩
  · intro a V g z
    change f.component a V g (h.hom.app (op V) z) = e.component a V g z
    rw [hh a V g]
    exact (f.component a V g).apply_symm_apply _
  · intro E' hE'
    have heq : E'.iso.hom = E.iso.hom := by
      apply natTrans_ext_cover U (etale_coversTop U hcover) _ _ N.monoidSheaf.property
      intro a V g
      apply ConcreteCategory.hom_ext
      intro z
      apply (f.component a V g).injective
      rw [hE']
      change e.component a V g z = f.component a V g (h.hom.app (op V) z)
      rw [hh a V g]
      exact ((f.component a V g).apply_symm_apply _).symm
    have he : E'.iso = E.iso := Iso.ext heq
    rcases E' with ⟨E', ha⟩
    rcases E with ⟨E, hb⟩
    dsimp only at he
    subst E'
    rfl

/-- Fine log structures descend effectively, uniquely with their labelled identifications,
and fs charts descend as well. Maps of arbitrary monoid sheaves over the structure sheaf
also glue uniquely; no log condition on their source or target is needed.

Source: ILO VI 1.1, VIII 3.3.8; Stacks, Tags 04TR and 04TQ
(blueprint: lem-trf-fine-log-structure-etale-descent).

Proof:
1. Apply `fineLogEtaleDescent_exists` for existence, labelled local identifications,
   fineness and the conditional fs assertion. This is the construction and chart-locality
   part of descent, split off as lem-trf-fine-log-etale-descent-existence.
2. Prove arbitrary prelog morphism gluing with Mathlib's sheaf of natural transformations:
   joint surjectivity gives `CoversTop`, and the local maps form compatible sections of
   `presheafHom`. Glue the sections and use `presheafHomSectionsEquiv` to obtain the map.
   The structural-map equation holds locally, hence globally by Hom-sheaf separatedness
   for the multiplicative structure sheaf. The log axiom is never used in this argument.
3. For two labelled gluings e and f, the local maps f⁻¹e preserve the structural maps
   and agree on overlaps by the transition equations. Glue them and their inverses by
   step 2. Both composites are identities by local verification and separatedness of
   the Hom sheaf. Any other isomorphism respecting the labels has the same local maps,
   hence the same global hom map and is therefore equal. -/
theorem fineLogStructure_etale_descent
    {T : Scheme.{u}} [IsLocallyNoetherian T] {ι : Type v} (U : ι → T.Etale)
    (hcover : ∀ x : T, ∃ (a : ι) (y : (U a).left), (U a).hom y = x) :
    (∀ D : FineLogEtaleDescentDatum U,
      ∃ (M : EtaleLogStructure T) (_hM : M.IsFine) (e : D.Gluing M),
        ((∀ a : ι, (D.localLog a).IsFineSaturated) → M.IsFineSaturated) ∧
        ∀ (N : EtaleLogStructure T) (_hN : N.IsFine) (f : D.Gluing N),
          ∃! h : EtalePrelogStructure.Iso M.toEtalePrelogStructure N.toEtalePrelogStructure,
            ∀ (a : ι) (V : T.Etale) (g : V ⟶ U a) (s : M.monoidSheaf.obj.obj (op V)),
              f.component a V g (h.iso.hom.app (op V) s) = e.component a V g s) ∧
    (∀ (A B : EtalePrelogStructure T) (localHom : ∀ a : ι, A.LocalHom B (U a)),
      (∀ (a b : ι) (V : T.Etale) (f : V ⟶ U a) (g : V ⟶ U b),
        (localHom a).hom.app (op (Over.mk f)) = (localHom b).hom.app (op (Over.mk g))) →
      ∃! h : A.Hom B, ∀ (a : ι) (V : T.Etale) (f : V ⟶ U a),
        h.hom.app (op V) = (localHom a).hom.app (op (Over.mk f))) := by
  constructor
  · intro D
    obtain ⟨M, hM, e, hfs⟩ := fineLogEtaleDescent_exists U hcover D
    refine ⟨M, hM, e, hfs, ?_⟩
    intro N _hN f
    exact gluing_unique U hcover e f
  · exact prelogHom_glue U hcover

end AlgebraicGeometry
