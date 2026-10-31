/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.ProfiniteActionCoherentPresentation
import WeilConjectures.CategoryTheory.CondensedGroupAlgebraExactForgetful
import Mathlib.CategoryTheory.Abelian.Transfer
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Exact inflation and normalized invariants of profinite condensed-group actions

Source: blueprint direct-image stability, paragraph (3), categorical input below the
partial Kummer boundary-unit calculation
(blueprint: lem-sfb-condensed-product-action-inflation).

The action categories use internal modules over the given arbitrary condensed ring.
The invariant inclusions and adjunction transposes are specified on every profinite test
object. Thus the comparison identifies the same fixed-section subsheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

private def sectionLinear {M N : Modules R} (f : M ⟶ N) (S : Profinite.{u}) :
    sectionModule R M S →ₗ[(InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) R.X).obj (op S)] sectionModule R N S :=
  ((InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X).map f).val.app (op S) |>.hom

private theorem sectionLinear_apply {M N : Modules R} (f : M ⟶ N)
    (S : Profinite.{u}) (x : sectionModule R M S) :
    sectionLinear R f S x = (f.hom.hom.app (op S)).hom x := rfl

private theorem action_grothendieck
    (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] :
    ∃ a : Abelian (ActionModule R P),
      a.toPreadditive = actionPreadditive ∧
      @IsGrothendieckAbelian.{u + 1} (ActionModule R P) _ a := by
  obtain ⟨Q, _, hQ⟩ := CoherentPresentation.profiniteAction_coherentPresentation P
  obtain ⟨D⟩ := hQ R
  let E := D.data.equivalence
  have : E.functor.Additive := D.properties.additive
  have : HasFiniteProducts (ActionModule R P) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  let a : Abelian (ActionModule R P) := abelianOfEquivalence E.functor
  have : IsGrothendieckAbelian.{u + 1} (ringedSiteModules.{u + 1}
      ((sheafCompose (CoherentPresentation.coverage P).toGrothendieck
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj D.data.ring)) :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator _ D.data.ring).1
  exact ⟨a, rfl, IsGrothendieckAbelian.of_equivalence E.symm⟩

private theorem invariants_exist
    (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] :
    Nonempty (Invariants R P) := by
  obtain ⟨Q, _, hQ⟩ := CoherentPresentation.profiniteAction_coherentPresentation P
  obtain ⟨D⟩ := hQ R
  exact ⟨D.data.invariants⟩

@[instance_reducible]
private def nativeAbelian
    (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] :
    Abelian (ActionModule R P) where
  toPreadditive := actionPreadditive
  toIsNormalMonoCategory := by
    obtain ⟨a, ha, _⟩ := action_grothendieck R P
    exact ha ▸ a.toIsNormalMonoCategory
  toIsNormalEpiCategory := by
    obtain ⟨a, ha, _⟩ := action_grothendieck R P
    exact ha ▸ a.toIsNormalEpiCategory
  has_finite_products := by
    obtain ⟨a, _, _⟩ := action_grothendieck R P
    exact a.has_finite_products
  has_kernels := by
    obtain ⟨a, ha, _⟩ := action_grothendieck R P
    exact ha ▸ a.has_kernels
  has_cokernels := by
    obtain ⟨a, ha, _⟩ := action_grothendieck R P
    exact ha ▸ a.has_cokernels

private theorem modules_grothendieck : IsGrothendieckAbelian.{u + 1} (Modules R) := by
  let P := PUnit.{u + 1}
  obtain ⟨a, ha, hg⟩ := action_grothendieck R P
  let := a
  have : IsGrothendieckAbelian.{u + 1} (ActionModule R P) := hg
  let F := forgetAction (R := R) (P := P)
  have : F.Faithful := ⟨fun h ↦ Subtype.ext h⟩
  have : F.Full :=
    ⟨fun f ↦ ⟨⟨f, by
      intro S g x
      have he : g = 1 := Subsingleton.elim _ _
      rw [he, map_one, map_one]
      rfl⟩, rfl⟩⟩
  have : F.EssSurj := ⟨fun M ↦ ⟨(trivial (P := P)).obj M, ⟨Iso.refl M⟩⟩⟩
  have : F.IsEquivalence := {}
  exact IsGrothendieckAbelian.of_equivalence F.asEquivalence

private theorem forget_exact
    (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] :
    PreservesFiniteLimits (forgetAction (R := R) (P := P)) ∧
      PreservesFiniteColimits (forgetAction (R := R) (P := P)) := by
  let := nativeAbelian R P
  let U := forgetAction (R := R) (P := P)
  have : U.Additive := GroupAlgebra.forget_additive R P
  have {M N : ActionModule R P} (f : M ⟶ N) :
      PreservesLimit (parallelPair f 0) U := by
    have := (GroupAlgebra.creates_kernels_cokernels R P M N f).1.some
    infer_instance
  have {M N : ActionModule R P} (f : M ⟶ N) :
      PreservesColimit (parallelPair f 0) U := by
    have := (GroupAlgebra.creates_kernels_cokernels R P M N f).2.some
    infer_instance
  exact ⟨U.preservesFiniteLimits_of_preservesKernels,
    U.preservesFiniteColimits_of_preservesCokernels⟩

private theorem forget_reflects (P : Type u) [TopologicalSpace P] [Group P]
    [IsTopologicalGroup P] :
    (forgetAction (R := R) (P := P)).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have : IsIso f.val := hf
    let i := inv f.val
    have hi : Equivariant N M i := by
      intro S g x
      have hf (y : sectionModule R N.module S) :
          (f.val.hom.hom.app (op S)).hom ((i.hom.hom.app (op S)).hom y) = y := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun k ↦ k.hom.hom) (IsIso.inv_hom_id f.val)) (op S)) y
      have hg (y : sectionModule R M.module S) :
          (i.hom.hom.app (op S)).hom ((f.val.hom.hom.app (op S)).hom y) = y := by
        exact ConcreteCategory.congr_hom (congr_app
          (congrArg (fun k ↦ k.hom.hom) (IsIso.hom_inv_id f.val)) (op S)) y
      have h := congrArg (fun y ↦ (i.hom.hom.app (op S)).hom y)
        (f.property S g ((i.hom.hom.app (op S)).hom x))
      rw [hg, hf] at h
      exact h.symm
    exact ⟨⟨⟨i, hi⟩, Subtype.ext (IsIso.hom_inv_id f.val),
      Subtype.ext (IsIso.inv_hom_id f.val)⟩⟩

section

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

private abbrev second (M : ActionModule R (G × H)) : ActionModule R H :=
  (inflate (ContinuousMonoidHom.inr G H)).obj M

private abbrev firstSection (S : Profinite.{u}) (g : C(S, G)) : C(S, G × H) :=
  (ContinuousMonoidHom.inl G H).toContinuousMap.comp g

private abbrev secondSection (S : Profinite.{u}) (h : C(S, H)) : C(S, G × H) :=
  (ContinuousMonoidHom.inr G H).toContinuousMap.comp h

private theorem section_commute (M : ActionModule R (G × H)) (S : Profinite.{u})
    (g : C(S, G)) (h : C(S, H)) (x : sectionModule R M.module S) :
    M.act S (secondSection G H S h) (M.act S (firstSection G H S g) x) =
      M.act S (firstSection G H S g) (M.act S (secondSection G H S h) x) := by
  have hp : secondSection G H S h * firstSection G H S g =
      firstSection G H S g * secondSection G H S h := by
    ext t <;> simp [firstSection, secondSection]
  have he := congrArg (fun p ↦ M.act S p x) hp
  simpa only [map_mul, Module.End.mul_apply] using he

private theorem first_fixed (d : Invariants R H) (M : ActionModule R (G × H))
    (S : Profinite.{u}) (g : C(S, G))
    (x : sectionModule R (d.functor.obj (second R G H M)) S) :
    ∃ y : sectionModule R (d.functor.obj (second R G H M)) S,
      ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom y =
        M.act S (firstSection G H S g)
          (((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x) := by
  apply (d.image (second R G H M) S _).mpr
  have hx := (d.image (second R G H M) S _).mp ⟨x, rfl⟩
  intro T f h
  change M.act T (secondSection G H T h)
      ((M.module.X.obj.map f.op).hom (M.act S (firstSection G H S g) _)) =
    (M.module.X.obj.map f.op).hom (M.act S (firstSection G H S g) _)
  let z := ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x
  have hn := M.naturality S T f (firstSection G H S g) z
  have hc := section_commute R G H M T (g.comp f.hom.hom) h
    ((M.module.X.obj.map f.op).hom z)
  exact (congrArg (M.act T (secondSection G H T h)) hn).trans
    (hc.trans ((congrArg (M.act T (firstSection G H T (g.comp f.hom.hom)))
      (hx T f h)).trans hn.symm))

-- The inclusion is injective, so the image equation determines this section uniquely.
private def residualValue (d : Invariants R H) (M : ActionModule R (G × H))
    (S : Profinite.{u}) (g : C(S, G))
    (x : sectionModule R (d.functor.obj (second R G H M)) S) :=
  Classical.choose (first_fixed R G H d M S g x)

private theorem residualValue_eq (d : Invariants R H) (M : ActionModule R (G × H))
    (S : Profinite.{u}) (g : C(S, G))
    (x : sectionModule R (d.functor.obj (second R G H M)) S) :
    ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
      (residualValue R G H d M S g x) =
        M.act S (firstSection G H S g)
          (((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x) :=
  Classical.choose_spec (first_fixed R G H d M S g x)

private def residualAction (d : Invariants R H) (M : ActionModule R (G × H))
    (S : Profinite.{u}) : C(S, G) →*
      Module.End ((InternalAbelianSheafModule.sectionRings
        (coherentTopology Profinite.{u}) R.X).obj (op S))
          (sectionModule R (d.functor.obj (second R G H M)) S) :=
  { toFun := fun g ↦
      { toFun := residualValue R G H d M S g
        map_add' := by
          intro x y
          apply d.injective (second R G H M) S
          simp only [map_add, residualValue_eq]
        map_smul' := by
          intro r x
          apply d.injective (second R G H M) S
          change sectionLinear R (d.inclusion.app (second R G H M)) S
            (residualValue R G H d M S g (r • x)) =
              sectionLinear R (d.inclusion.app (second R G H M)) S
                (r • residualValue R G H d M S g x)
          let i := sectionLinear R (d.inclusion.app (second R G H M)) S
          let a := M.act S (firstSection G H S g)
          have h (y : sectionModule R (d.functor.obj (second R G H M)) S) :
              i (residualValue R G H d M S g y) = a (i y) :=
            residualValue_eq R G H d M S g y
          exact (h (r • x)).trans ((congrArg a (i.map_smul r x)).trans
            ((a.map_smul r (i x)).trans
              ((congrArg (fun z ↦ r • z) (h x).symm).trans
                (i.map_smul r (residualValue R G H d M S g x)).symm))) }
    map_one' := by
      apply LinearMap.ext
      intro x
      apply d.injective (second R G H M) S
      change ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
        (residualValue R G H d M S 1 x) =
          ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x
      rw [residualValue_eq]
      change M.act S 1 _ = _
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro x
      apply d.injective (second R G H M) S
      change ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
        (residualValue R G H d M S (g * h) x) =
          ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
            (residualValue R G H d M S g (residualValue R G H d M S h x))
      rw [residualValue_eq, residualValue_eq, residualValue_eq]
      have hp : firstSection G H S (g * h) =
          firstSection G H S g * firstSection G H S h := by
        ext t <;> simp [firstSection]
      exact (congrArg (fun p ↦ M.act S p
        (((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x)) hp).trans
          (congrArg (fun a ↦ a
            (((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x))
              ((M.act S).map_mul (firstSection G H S g) (firstSection G H S h))) }

private theorem residual_naturality (d : Invariants R H) (M : ActionModule R (G × H))
    (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, G))
    (x : sectionModule R (d.functor.obj (second R G H M)) S) :
    ((d.functor.obj (second R G H M)).X.obj.map f.op).hom
      (residualAction R G H d M S g x) =
        residualAction R G H d M T (g.comp f.hom.hom)
          (((d.functor.obj (second R G H M)).X.obj.map f.op).hom x) := by
  apply d.injective (second R G H M) T
  have hn := (d.inclusion.app (second R G H M)).hom.hom.naturality f.op
  have hn' (y : sectionModule R (d.functor.obj (second R G H M)) S) :
      ((d.inclusion.app (second R G H M)).hom.hom.app (op T)).hom
        (((d.functor.obj (second R G H M)).X.obj.map f.op).hom y) =
      (M.module.X.obj.map f.op).hom
        (((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom y) :=
    ConcreteCategory.congr_hom hn y
  exact (hn' (residualValue R G H d M S g x)).trans
    ((congrArg (M.module.X.obj.map f.op).hom (residualValue_eq R G H d M S g x)).trans
      ((M.naturality S T f (firstSection G H S g) _).trans
        ((congrArg (M.act T (firstSection G H T (g.comp f.hom.hom))) (hn' x).symm).trans
          (residualValue_eq R G H d M T (g.comp f.hom.hom) _).symm)))

private def residualObject (d : Invariants R H) (M : ActionModule R (G × H)) :
    ActionModule R G where
  module := d.functor.obj (second R G H M)
  act := residualAction R G H d M
  naturality := residual_naturality R G H d M

private theorem residual_map (d : Invariants R H) {M N : ActionModule R (G × H)}
    (f : M ⟶ N) :
    Equivariant (residualObject R G H d M) (residualObject R G H d N)
      (d.functor.map ((inflate (ContinuousMonoidHom.inr G H)).map f)) := by
  intro S g x
  apply d.injective (second R G H N) S
  have hn := congr_app (congrArg (fun k ↦ k.hom.hom) (d.inclusion.naturality
    ((inflate (ContinuousMonoidHom.inr G H)).map f))) (op S)
  have he (y : sectionModule R (d.functor.obj (second R G H M)) S) :
      ((d.inclusion.app (second R G H N)).hom.hom.app (op S)).hom
        (((d.functor.map ((inflate (ContinuousMonoidHom.inr G H)).map f)).hom.hom.app
          (op S)).hom y) =
        (f.val.hom.hom.app (op S)).hom
          (((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom y) :=
    ConcreteCategory.congr_hom hn y
  change ((d.inclusion.app (second R G H N)).hom.hom.app (op S)).hom
    (((d.functor.map ((inflate (ContinuousMonoidHom.inr G H)).map f)).hom.hom.app
      (op S)).hom (residualValue R G H d M S g x)) =
        ((d.inclusion.app (second R G H N)).hom.hom.app (op S)).hom
          (residualValue R G H d N S g _)
  exact (he (residualValue R G H d M S g x)).trans
    ((congrArg (f.val.hom.hom.app (op S)).hom (residualValue_eq R G H d M S g x)).trans
      ((f.property S (firstSection G H S g) _).trans
        ((congrArg (N.act S (firstSection G H S g)) (he x).symm).trans
          (residualValue_eq R G H d N S g _).symm)))

private def residualFunctor (d : Invariants R H) :
    ActionModule R (G × H) ⥤ ActionModule R G where
  obj M := residualObject R G H d M
  map f := ⟨d.functor.map ((inflate (ContinuousMonoidHom.inr G H)).map f),
    residual_map R G H d f⟩
  map_id M := Subtype.ext (d.functor.map_id _)
  map_comp f g := by
    apply Subtype.ext
    exact ((inflate (ContinuousMonoidHom.inr G H)) ⋙ d.functor).map_comp f g

private def residualInclusion (d : Invariants R H) :
    residualFunctor R G H d ⋙ forgetAction ⟶ forgetAction where
  app M := d.inclusion.app (second R G H M)
  naturality {_M _N} f :=
    d.inclusion.naturality ((inflate (ContinuousMonoidHom.inr G H)).map f)

private theorem restrict_trivial_equivariant
    (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M) :
    Equivariant (trivial.obj N.module) (second R G H M) f.val := by
  intro S h x
  have hf := f.property S (secondSection G H S h) x
  change (f.val.hom.hom.app (op S)).hom (N.act S 1 x) = _ at hf
  change (f.val.hom.hom.app (op S)).hom x =
    M.act S (secondSection G H S h) ((f.val.hom.hom.app (op S)).hom x)
  simpa only [map_one, Module.End.one_apply] using hf

private def residualTranspose (d : Invariants R H)
    (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M) :
    N.module ⟶ d.functor.obj (second R G H M) :=
  d.adjunction.homEquiv N.module (second R G H M)
    ⟨f.val, restrict_trivial_equivariant R G H N M f⟩

private theorem residualTranspose_inclusion (d : Invariants R H)
    (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M) :
    residualTranspose R G H d N M f ≫ d.inclusion.app (second R G H M) = f.val :=
  d.transpose N.module (second R G H M) _

private theorem residual_transpose_equivariant (d : Invariants R H)
    (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M) :
    Equivariant N (residualObject R G H d M) (residualTranspose R G H d N M f) := by
  intro S g x
  apply d.injective (second R G H M) S
  have ht := residualTranspose_inclusion R G H d N M f
  have ht' (y : sectionModule R N.module S) :
      ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
        (((residualTranspose R G H d N M f).hom.hom.app (op S)).hom y) =
      (f.val.hom.hom.app (op S)).hom y :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun k ↦ k.hom.hom) ht) (op S)) y
  exact (ht' (N.act S g x)).trans
    ((f.property S (firstSection G H S g) x).trans
      ((congrArg (M.act S (firstSection G H S g)) (ht' x).symm).trans
        (residualValue_eq R G H d M S g _).symm))

private def residualUntranspose (d : Invariants R H)
    (N : ActionModule R G) (M : ActionModule R (G × H))
    (f : N ⟶ (residualFunctor R G H d).obj M) :
    (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M :=
   ⟨f.val ≫ d.inclusion.app (second R G H M), by
    intro S p x
    change ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
      ((f.val.hom.hom.app (op S)).hom
        (N.act S ((ContinuousMonoidHom.fst G H).toContinuousMap.comp p) x)) = _
    rw [f.property]
    change ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
      (residualValue R G H d M S _ _) = _
    rw [residualValue_eq]
    let y := ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom
      ((f.val.hom.hom.app (op S)).hom x)
    have hy := (d.image (second R G H M) S y).mp ⟨_, rfl⟩
    have hh := hy S (𝟙 S) ((ContinuousMonoidHom.snd G H).toContinuousMap.comp p)
    have hh' : M.act S (secondSection G H S
        ((ContinuousMonoidHom.snd G H).toContinuousMap.comp p)) y = y := by
      change M.act S (secondSection G H S _)
        ((M.module.X.obj.map (𝟙 S).op).hom y) =
          (M.module.X.obj.map (𝟙 S).op).hom y at hh
      have hid : (M.module.X.obj.map (𝟙 S).op).hom y = y := by
        change (M.module.X.obj.map (𝟙 (op S))).hom y = y
        rw [M.module.X.obj.map_id]
        rfl
      exact (congrArg (M.act S (secondSection G H S _)) hid).symm.trans (hh.trans hid)
    have hp : firstSection G H S ((ContinuousMonoidHom.fst G H).toContinuousMap.comp p) *
        secondSection G H S ((ContinuousMonoidHom.snd G H).toContinuousMap.comp p) = p := by
      ext t <;> simp [firstSection, secondSection]
    change M.act S (firstSection G H S _) y = M.act S p y
    exact (congrArg (M.act S (firstSection G H S _)) hh'.symm).trans
      ((congrArg (fun a ↦ a y) ((M.act S).map_mul _ _)).symm.trans
        (congrArg (fun q ↦ M.act S q y) hp))⟩

private def residualHomEquiv (d : Invariants R H)
    (N : ActionModule R G) (M : ActionModule R (G × H)) :
    ((inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M) ≃
      (N ⟶ (residualFunctor R G H d).obj M) where
  toFun f := ⟨residualTranspose R G H d N M f,
    residual_transpose_equivariant R G H d N M f⟩
  invFun := residualUntranspose R G H d N M
  left_inv f := by
    apply Subtype.ext
    exact residualTranspose_inclusion R G H d N M f
  right_inv f := by
    apply Subtype.ext
    apply (d.adjunction.homEquiv N.module (second R G H M)).symm.injective
    exact ((d.adjunction.homEquiv N.module (second R G H M)).symm_apply_apply _).trans
      (Subtype.ext (d.untranspose N.module (second R G H M) f.val).symm)

private theorem residualHomEquiv_naturality_left (d : Invariants R H)
    {N N' : ActionModule R G} {M : ActionModule R (G × H)}
    (f : N' ⟶ N) (g : N ⟶ (residualFunctor R G H d).obj M) :
    (residualHomEquiv R G H d N' M).symm (f ≫ g) =
      (inflate (ContinuousMonoidHom.fst G H)).map f ≫
        (residualHomEquiv R G H d N M).symm g := by
  apply Subtype.ext
  exact Category.assoc _ _ _

private theorem residualHomEquiv_naturality_right (d : Invariants R H)
    {N : ActionModule R G} {M M' : ActionModule R (G × H)}
    (f : (inflate (ContinuousMonoidHom.fst G H)).obj N ⟶ M) (g : M ⟶ M') :
    residualHomEquiv R G H d N M' (f ≫ g) =
      residualHomEquiv R G H d N M f ≫ (residualFunctor R G H d).map g := by
  apply Subtype.ext
  exact d.adjunction.homEquiv_naturality_right
    (show trivial.obj N.module ⟶ second R G H M from
      ⟨f.val, restrict_trivial_equivariant R G H N M f⟩)
    ((inflate (ContinuousMonoidHom.inr G H)).map g)

private def residualCore (d : Invariants R H) :
    Adjunction.CoreHomEquiv (inflate (ContinuousMonoidHom.fst G H))
      (residualFunctor R G H d) where
  homEquiv := residualHomEquiv R G H d
  homEquiv_naturality_left_symm := residualHomEquiv_naturality_left R G H d
  homEquiv_naturality_right := residualHomEquiv_naturality_right R G H d

private def residualAdjunction (d : Invariants R H) :
    ProductInvariants R G H where
  functor := residualFunctor R G H d
  additive := by
    have := d.additive
    refine ⟨?_⟩
    intro M N f g
    apply Subtype.ext
    change d.functor.map (((inflate (ContinuousMonoidHom.inr G H)).map f) +
      ((inflate (ContinuousMonoidHom.inr G H)).map g)) = _
    exact d.functor.map_add
  inclusion := residualInclusion R G H d
  adjunction := Adjunction.mkOfHomEquiv (residualCore R G H d)
  injective M S := d.injective (second R G H M) S
  image M S m := by
    change (∃ x : sectionModule R (d.functor.obj (second R G H M)) S,
      ((d.inclusion.app (second R G H M)).hom.hom.app (op S)).hom x = m) ↔ _
    rw [d.image]
    constructor
    · intro hm T f p hp
      have he : p = secondSection G H T
          ((ContinuousMonoidHom.snd G H).toContinuousMap.comp p) := by
        apply ContinuousMap.ext
        intro t
        exact Prod.ext (hp t) rfl
      rw [he]
      exact hm T f _
    · intro hm T f h
      exact hm T f (secondSection G H T h) (fun _ ↦ rfl)
  residual M S g x := residualValue_eq R G H d M S g x
  transpose N M f := by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    exact d.transpose N.module (second R G H M) _
  untranspose N M f := by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl

private theorem trivial_product :
    trivial (R := R) (P := G × H) =
      trivial (R := R) (P := G) ⋙ inflate (ContinuousMonoidHom.fst G H) := by
  rfl

private theorem trivial_exact (P : Type u) [TopologicalSpace P] [Group P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] :
    (trivial (R := R) (P := P)).Additive ∧
      PreservesFiniteLimits (trivial (R := R) (P := P)) ∧
      PreservesFiniteColimits (trivial (R := R) (P := P)) := by
  let := nativeAbelian R P
  let U := forgetAction (R := R) (P := P)
  have := forget_reflects R P
  have := (forget_exact R P).1
  have := (forget_exact R P).2
  have : ReflectsFiniteLimits U :=
    ⟨fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  have : ReflectsFiniteColimits U :=
    { reflects := fun _ _ _ ↦
        reflectsColimitsOfShape_of_reflectsIsomorphisms }
  let F := trivial (R := R) (P := P)
  have : PreservesFiniteLimits (F ⋙ U) :=
    show PreservesFiniteLimits (𝟭 (Modules R)) from inferInstance
  have : PreservesFiniteColimits (F ⋙ U) :=
    show PreservesFiniteColimits (𝟭 (Modules R)) from inferInstance
  exact ⟨⟨by intros; rfl⟩, preservesFiniteLimits_of_reflects_of_preserves F U,
    preservesFiniteColimits_of_reflects_of_preserves F U⟩

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

private theorem projection_exact :
    (inflate (R := R) (ContinuousMonoidHom.fst G H)).Additive ∧
      PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) ∧
      PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) := by
  let := nativeAbelian R G
  let := nativeAbelian R (G × H)
  let U := forgetAction (R := R) (P := G × H)
  have := forget_reflects R (G × H)
  have := (forget_exact R (G × H)).1
  have := (forget_exact R (G × H)).2
  have : ReflectsFiniteLimits U :=
    ⟨fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  have : ReflectsFiniteColimits U :=
    { reflects := fun _ _ _ ↦
        reflectsColimitsOfShape_of_reflectsIsomorphisms }
  let F := inflate (R := R) (ContinuousMonoidHom.fst G H)
  have : PreservesFiniteLimits (F ⋙ U) := (forget_exact R G).1
  have : PreservesFiniteColimits (F ⋙ U) := (forget_exact R G).2
  exact ⟨⟨by intros; rfl⟩, preservesFiniteLimits_of_reflects_of_preserves F U,
    preservesFiniteColimits_of_reflects_of_preserves F U⟩

end

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

-- The unchanged specification retains the separate H-invariants witness.
set_option linter.unusedVariables false in
/-- Grothendieck abelianness, exact additive inflation and normalized invariants for both
factors and their product, including the identity normalization of the conjugate comparison.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-product-action-inflation).

Proof:
1. Use `sk-def-sfb-sheaf-tensor` and
   `def-weil-pbc-internal-abelian-sheaf-module-equivalence` to pass from internal modules
   to sectionwise modules without changing the underlying sheaves, sections or maps.
2. The action-site presentation `lem-sfb-internal-action-site-presentation` identifies each
   action category additively with module sheaves on a small ringed site. It creates
   kernels and cokernels, and detects zero. Apply
   `lem-pur-ringed-site-grothendieck-abelian` and transport the generator, colimits and
   exact filtered colimits across this equivalence, including the trivial-group case.
3. Inflation precomposes each action with the projection and leaves the module and map
   unchanged. It is additive and preserves the preceding kernel and cokernel formulas,
   hence is exact.
4. Define fixed sections by requiring fixedness after every profinite base change. Linearity
   makes these submodules; the quantified condition gives restriction stability. Glue them
   in the original sheaf and test fixedness on the pulled-back cover to prove the sheaf
   condition. The first-factor action preserves second-factor invariants because the two
   factors commute. Restrict equivariant maps; this is an additive functor.
5. An equivariant map from an inflated object has fixed image, so restrict its codomain.
   Conversely compose a map to invariants with the inclusion. These operations are inverse
   and natural. In the product case use `(g,h)=(g,1)(1,h)` for equivariance and `(g,1)` for
   the residual action. These are exactly the transpose formulas in the specifications.
6. Direct and successive trivial inflation have the same module, action and maps. Being
   fixed by all pairs is equivalent, on every base change, to being fixed by both factors.
   Both successive and direct transposes retain the same section maps, so their conjugate
   right-adjoint comparison is the identity under the invariant inclusions. The unit law
   handles either trivial factor, and the zero ring forces every section module to be zero.
-/
theorem product_action_inflation :
    ∃ (aG : Abelian (ActionModule R G)) (aH : Abelian (ActionModule R H))
      (aGH : Abelian (ActionModule R (G × H))),
    aG.toPreadditive = actionPreadditive ∧
    aH.toPreadditive = actionPreadditive ∧
    aGH.toPreadditive = actionPreadditive ∧
    IsGrothendieckAbelian.{u + 1} (Modules R) ∧
    @IsGrothendieckAbelian.{u + 1} (ActionModule R G) _ aG ∧
    @IsGrothendieckAbelian.{u + 1} (ActionModule R H) _ aH ∧
    @IsGrothendieckAbelian.{u + 1} (ActionModule R (G × H)) _ aGH ∧
    (trivial (R := R) (P := G)).Additive ∧
    PreservesFiniteLimits (trivial (R := R) (P := G)) ∧
    PreservesFiniteColimits (trivial (R := R) (P := G)) ∧
    (trivial (R := R) (P := H)).Additive ∧
    PreservesFiniteLimits (trivial (R := R) (P := H)) ∧
    PreservesFiniteColimits (trivial (R := R) (P := H)) ∧
    (inflate (R := R) (ContinuousMonoidHom.fst G H)).Additive ∧
    PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) ∧
    PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G H)) ∧
    ∃ (dG : Invariants R G) (dH : Invariants R H) (dGH : Invariants R (G × H))
      (dHG : ProductInvariants R G H)
      (h : trivial (R := R) (P := G × H) =
        trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H)),
      ∀ (M : ActionModule R (G × H)) (S : Profinite.{u})
        (x : sectionModule R (dGH.functor.obj M) S),
        (((dG.inclusion.app (dHG.functor.obj M)) ≫ dHG.inclusion.app M).hom.hom.app
          (op S)).hom
          (((((conjugateIsoEquiv dGH.adjunction
            (dG.adjunction.comp dHG.adjunction)) (eqToIso h.symm)).hom.app M).hom.hom.app
              (op S)).hom x) =
          ((dGH.inclusion.app M).hom.hom.app (op S)).hom x := by
  obtain ⟨aG, hG, gG⟩ := action_grothendieck R G
  obtain ⟨aH, hH, gH⟩ := action_grothendieck R H
  obtain ⟨aGH, hGH, gGH⟩ := action_grothendieck R (G × H)
  have gm := modules_grothendieck R
  obtain ⟨dG⟩ := invariants_exist R G
  obtain ⟨dH⟩ := invariants_exist R H
  obtain ⟨dGH⟩ := invariants_exist R (G × H)
  let dHG := residualAdjunction R G H dH
  let h := trivial_product R G H
  refine ⟨aG, aH, aGH, hG, hH, hGH, gm, gG, gH, gGH,
    (trivial_exact R G).1, (trivial_exact R G).2.1, (trivial_exact R G).2.2,
    (trivial_exact R H).1, (trivial_exact R H).2.1, (trivial_exact R H).2.2,
    (projection_exact R G H).1, (projection_exact R G H).2.1,
    (projection_exact R G H).2.2, dG, dH, dGH, dHG, h, ?_⟩
  intro M S x
  have he := conjugateEquiv_counit dGH.adjunction (dG.adjunction.comp dHG.adjunction)
    (eqToIso h.symm).hom M
  have hc (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
      (d : Invariants R P) (N : ActionModule R P) :
      (d.adjunction.counit.app N).val = d.inclusion.app N := by
    rw [← d.adjunction.homEquiv_symm_id, d.untranspose, Category.id_comp]
  have hp (N : ActionModule R (G × H)) :
      (dHG.adjunction.counit.app N).val = dHG.inclusion.app N := by
    rw [← dHG.adjunction.homEquiv_symm_id, dHG.untranspose]
    change 𝟙 _ ≫ dHG.inclusion.app N = dHG.inclusion.app N
    exact Category.id_comp _
  rw [Adjunction.comp_counit_app] at he
  have hm :
      (((conjugateIsoEquiv dGH.adjunction (dG.adjunction.comp dHG.adjunction))
        (eqToIso h.symm)).hom.app M) ≫
          (dG.adjunction.counit.app (dHG.functor.obj M)).val ≫
          (dHG.adjunction.counit.app M).val = (dGH.adjunction.counit.app M).val := by
    have ht := congrArg Subtype.val he
    change ((((conjugateIsoEquiv dGH.adjunction (dG.adjunction.comp dHG.adjunction))
      (eqToIso h.symm)).hom.app M) ≫
        (dG.adjunction.counit.app (dHG.functor.obj M)).val) ≫
      (dHG.adjunction.counit.app M).val =
        𝟙 _ ≫ (dGH.adjunction.counit.app M).val at ht
    simpa only [Category.assoc, Category.id_comp] using ht
  rw [hc, hp, hc] at hm
  exact congrArg (fun f ↦ (f.hom.hom.app (op S)).hom x) hm

end Profinite.CondensedAction
