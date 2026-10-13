/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3, SHEAF group N2
-/
module

public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Exact internal Hom from a projective module on the one-object site

Source: Stacks Project, more-algebra.tex, Tag 0A6A, bounded projective computation;
algebra.tex, projective modules and exactness of Hom.
(blueprint: lem-pc-ring-projective-internal-hom-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private lemma point_unique (X : (Discrete PUnit.{u + 1})ᵒᵖ) : X = point :=
  Subsingleton.elim _ _

/-- On the bottom topology every presheaf is already a sheaf. -/
private noncomputable def bottomEquivalence
    {C : Type u} [SmallCategory C] (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}) :
    SheafOfModules.{u} R ≌ PresheafOfModules.{u} R.obj where
  functor := forget R
  inverse :=
    { obj := fun N => ⟨N, Presheaf.isSheaf_bot _⟩
      map := fun f => ⟨f⟩ }
  unitIso := NatIso.ofComponents (fun _ =>
    { hom := ⟨𝟙 _⟩
      inv := ⟨𝟙 _⟩ })
  counitIso := Iso.refl _

/-- Extend a linear map at the sole object to a morphism of presheaves. -/
private noncomputable def pointPreimage
    {A : Type u} [CommRing A]
    {M N : PresheafOfModules.{u}
      (((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)).obj)}
    (f : M.obj point ⟶ N.obj point) : M ⟶ N where
  app X := by
    obtain rfl := point_unique X
    exact f
  naturality {X Y} g := by
    obtain rfl := point_unique X
    obtain rfl := point_unique Y
    have hg : g = 𝟙 point := Subsingleton.elim _ _
    subst g
    ext x
    simp

/-- The singleton discrete category has a singleton slice as well. -/
private lemma slice_unique (U : Discrete PUnit.{u + 1})
    (W : Over U) : W = Over.mk (𝟙 U) := by
  cases U with
  | mk U =>
    cases U
    cases W
    aesop

private lemma point_hom_ext
    {A : Type u} [CommRing A]
    {M N : PresheafOfModules.{u}
      (((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)).obj)}
    {f g : M ⟶ N} (h : f.app point = g.app point) : f = g := by
  apply PresheafOfModules.hom_ext
  intro X
  obtain rfl := point_unique X
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Internal Hom acts on its point value by postcomposition on the slice. -/
private lemma homPointMap_apply
    {A : Type u} [CommRing A]
    (M N N' : SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))
    (g : N ⟶ N') (φ : (homObj (R := CochainComplex.onePointRingSheaf A) M N).val.obj
      point) :
    ((homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) g).val.app point).hom
      φ = φ ≫ (PresheafOfModules.restrictOver
        (CochainComplex.onePointRingSheaf A).obj point.unop).map g.val := by
  change (PresheafOfModules.restrictOver _ _).map (𝟙 M.val) ≫ φ ≫
    (PresheafOfModules.restrictOver _ _).map g.val = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Internal Hom from a projective module on the one-object bottom-topology site
preserves short exact sequences. No finite-generation assumption is needed.
Source: Stacks Project, more-algebra.tex, Tag 0A6A, projective Hom computation;
algebra.tex, projective modules and exactness of Hom.
(blueprint: lem-pc-ring-projective-internal-hom-exact).

Proof: evaluation at the unique object identifies sheaves of modules on this site
with modules over A: there are only identity restriction maps, and the bottom topology
imposes no additional condition. The slice over the unique object is again this site,
so evaluation of the shared internal Hom is Hom_A(M(*),N(*)), with homObjMap acting
by pre- and postcomposition. A short exact sequence evaluates to a short exact
sequence of A-modules. Hom_A(M(*),-) preserves kernels, giving injectivity and
exactness at the middle term. Projectivity of M(*) lifts every map M(*) to the last
term through the surjection from the middle term, giving surjectivity. The composite
is zero since the original composite is zero. Evaluation reflects these three
properties, so the internal-Hom sequence is short exact. This also covers the zero
ring, the zero source, and projectives of infinite rank. -/
theorem ringProjectiveInternalHomExact {A : Type u} [CommRing A]
    (M : SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (CochainComplex.onePointRingSheaf A)))
    (hM : Module.Projective A (M.val.obj (op ⟨PUnit.unit⟩)))
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))) (hS : S.ShortExact) :
    ∃ hz : homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f ≫
        homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g = 0,
      (ShortComplex.mk
        (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f)
        (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g) hz).ShortExact := by
  let R := (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A)
  have : (forget R).IsEquivalence := (bottomEquivalence R).isEquivalence_functor
  let E := evaluation R point
  have : E.Faithful := ⟨fun h => hom_ext (point_hom_ext h)⟩
  have : PreservesFiniteColimits (forget R) := inferInstance
  have : PreservesFiniteColimits E :=
    inferInstanceAs (PreservesFiniteColimits
      (forget R ⋙ PresheafOfModules.evaluation R.obj point))
  have hs := hS.map_of_exact E
  have : Mono (S.map E).f := hs.mono_f
  have : Epi (S.map E).g := hs.epi_g
  have : Mono (E.map S.f) := hs.mono_f
  have : Epi (E.map S.g) := hs.epi_g
  have : Module.Projective A (M.val.obj point) := hM
  have : Projective (M.val.obj point) :=
    ModuleCat.projective_of_categoryTheory_projective (R := A) (M.val.obj point)
  have hz : homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f ≫
      homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g = 0 := by
    rw [homObjMap_comp_homObjMap (R := CochainComplex.onePointRingSheaf A),
      Category.id_comp, S.zero]
    apply hom_ext
    ext X φ : 3
    rfl
  let T := ShortComplex.mk
    (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.f)
    (homObjMap (R := CochainComplex.onePointRingSheaf A) (𝟙 M) S.g) hz
  have ht : (T.map E).ShortExact := by
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro φ hφ
      let p : M.val.obj point ⟶ S.X₂.val.obj point :=
        φ.app (op (Over.mk (𝟙 point.unop)))
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.g).val.app point).hom φ = 0 at hφ
      rw [homPointMap_apply] at hφ
      have hp : p ≫ E.map S.g = 0 := by
        exact congrArg (fun ψ => ψ.app (op (Over.mk (𝟙 point.unop)))) hφ
      let q := hs.exact.lift p hp
      refine ⟨(PresheafOfModules.restrictOver
        (CochainComplex.onePointRingSheaf A).obj point.unop).map (pointPreimage q), ?_⟩
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.f).val.app point).hom _ = φ
      rw [homPointMap_apply]
      apply PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      obtain rfl := slice_unique point.unop W
      change q ≫ S.f.val.app point = p
      exact hs.exact.lift_f p hp
    · rw [ModuleCat.mono_iff_injective]
      intro φ ψ h
      apply PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      obtain rfl := slice_unique point.unop W
      apply (cancel_mono (E.map S.f)).1
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.f).val.app point).hom φ =
        ((homObjMap (R := CochainComplex.onePointRingSheaf A)
          (𝟙 M) S.f).val.app point).hom ψ at h
      rw [homPointMap_apply, homPointMap_apply] at h
      exact congrArg (fun χ => χ.app (op (Over.mk (𝟙 point.unop)))) h
    · rw [ModuleCat.epi_iff_surjective]
      intro φ
      let p : M.val.obj point ⟶ S.X₃.val.obj point :=
        φ.app (op (Over.mk (𝟙 point.unop)))
      let q := Projective.factorThru p (E.map S.g)
      refine ⟨(PresheafOfModules.restrictOver
        (CochainComplex.onePointRingSheaf A).obj point.unop).map (pointPreimage q), ?_⟩
      change ((homObjMap (R := CochainComplex.onePointRingSheaf A)
        (𝟙 M) S.g).val.app point).hom _ = φ
      rw [homPointMap_apply]
      apply PresheafOfModules.hom_ext
      intro W
      obtain ⟨W⟩ := W
      obtain rfl := slice_unique point.unop W
      change q ≫ S.g.val.app point = p
      exact Projective.factorThru_comp p (E.map S.g)
  refine ⟨hz, ?_⟩
  change T.ShortExact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (T.exact_map_iff_of_faithful E).1 ht.exact
  · have : Mono (E.map T.f) := ht.mono_f
    exact E.mono_of_mono_map inferInstance
  · have : Epi (E.map T.g) := ht.epi_g
    exact E.epi_of_epi_map inferInstance

end SheafOfModules
