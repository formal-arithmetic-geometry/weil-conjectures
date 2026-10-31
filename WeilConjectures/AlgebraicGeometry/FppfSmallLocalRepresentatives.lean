/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.Small

/-! Small sections of locally generated fppf sheaves. -/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private abbrev affineLft (T : Scheme.{u}) :=
  MorphismProperty.CostructuredArrow @LocallyOfFiniteType ⊤ Scheme.Spec T

private theorem affineLft_small (T : Scheme.{u}) : EssentiallySmall.{u} (affineLft T) :=
  essentiallySmall_costructuredArrow_Spec _ le_rfl

private noncomputable abbrev affineLftOver (T : Scheme.{u}) : affineLft T ⥤ Over T :=
  MorphismProperty.CostructuredArrow.toOver _ Scheme.Spec T ⋙
    MorphismProperty.Over.forget _ ⊤ T

-- A locally generated sheaf has small sections: record all representatives on a
-- small model of the affine schemes locally of finite type over the test scheme.
/-- Small local representatives give small sections of an fppf sheaf.
Source: Mathlib's essentially-small category of affine schemes locally of finite type
and the sheaf local-representative argument (Stacks, Sites, Tags 00WB and 00WK).
Encode a section by its representatives on a small model of that category. Affine
refinement of a covering with representatives, followed by separatedness, makes the
encoding injective into a small power set.
(blueprint: lem-trf-fppf-small-local-representatives). -/
theorem fppf_small_of_local_representatives {S : Scheme.{u}}
    (P : (Over S)ᵒᵖ ⥤ Type u) (Q : Sheaf (fppfTopology.over S) (Type (u + 1)))
    (η : P ⋙ uliftFunctor.{u + 1} ⟶ Q.obj)
    [Presheaf.IsLocallySurjective (fppfTopology.over S) η] (T : Over S) :
    Small.{u} (Q.obj.obj (op T)) := by
  classical
  let : MorphismProperty.IsMultiplicative @LocallyOfFinitePresentation :=
    { id_mem := fun _ ↦ inferInstance }
  let := affineLft_small T.left
  let E := equivSmallModel.{u} (affineLft T.left)
  let K : SmallModel.{u} (affineLft T.left) ⥤ Over T.left := E.inverse ⋙ affineLftOver T.left
  let L := K ⋙ Over.map T.hom
  let code (x : Q.obj.obj (op T)) : Set (Σ j, P.obj (op (L.obj j))) :=
    { a | η.app _ ⟨a.2⟩ = Q.obj.map (Over.homMk (K.obj a.1).hom).op x }
  apply small_of_injective (f := code)
  intro x y hxy
  obtain ⟨C, hC, hle⟩ :=
    (mem_overGrothendieckTopology (P := @Flat ⊓ @LocallyOfFinitePresentation) T
      (Presheaf.imageSieve η x)).mp
      (by
        change Presheaf.imageSieve η x ∈ (fppfTopology.over S) T
        exact Presheaf.imageSieve_mem (fppfTopology.over S) η x)
  let D := C.bind fun i ↦
    (C.X i).affineCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ ↦ ⟨inferInstance, inferInstance⟩)
  let : C.Over S := hC
  let hQ := (isSheaf_iff_isSheaf_of_type _ _).mp Q.property
  have hDC : Sieve.ofArrows D.X D.f ∈ fppfTopology T.left := Cover.mem_grothendieckTopology D
  have hDC' := (fppfTopology.overEquiv_symm_mem_over T _ hDC)
  have hi (i : D.I₀) :
      Q.obj.map (Over.homMk (V := T) (U := Over.mk (D.f i ≫ T.hom)) (D.f i) rfl).op x =
        Q.obj.map (Over.homMk (V := T) (U := Over.mk (D.f i ≫ T.hom)) (D.f i) rfl).op y := by
    have hflat : Flat (C.f i.1) := (C.map_prop _).1
    have hfp : LocallyOfFinitePresentation (C.f i.1) := (C.map_prop _).2
    let V' : Over S := Over.mk (D.f i ≫ T.hom)
    let f' : V' ⟶ T := Over.homMk (D.f i)
    obtain ⟨p, hp⟩ := hle _ _ ⟨i.1⟩
    let g : V' ⟶ (C.X i.1).asOver S := Over.homMk ((C.X i.1).affineCover.f i.2) (by
      change _ ≫ _ = (_ ≫ C.f i.1) ≫ T.hom
      rw [Category.assoc]
      exact congrArg (fun k ↦ (C.X i.1).affineCover.f i.2 ≫ k)
        ((C.f i.1).asOver S).w.symm)
    have hg : g ≫ (C.f i.1).asOver S = f' := by ext; rfl
    let p' : P.obj (op V') := P.map g.op p.down
    have hp' : η.app _ ⟨p'⟩ = Q.obj.map f'.op x := by
      have hn := NatTrans.naturality_apply η g.op p
      change η.app _ ((P ⋙ uliftFunctor.{u + 1}).map g.op p) = _
      rw [hn, hp, ← Functor.map_comp_apply, ← op_comp, hg]
    have hft : LocallyOfFiniteType (D.f i) := by
      change LocallyOfFiniteType ((C.X i.1).affineCover.f i.2 ≫ C.f i.1)
      infer_instance
    have : IsAffine (D.X i) := by
      change IsAffine ((C.X i.1).affineCover.X i.2)
      infer_instance
    let A : affineLft T.left :=
      MorphismProperty.CostructuredArrow.mk ⊤
        ((D.X i).isoSpec.inv ≫ D.f i) (by infer_instance)
    let e : Over.mk (D.f i) ≅ K.obj (E.functor.obj A) :=
      Over.isoMk (g := (affineLftOver T.left).obj A) (D.X i).isoSpec
        (by simp [A, affineLftOver]) ≪≫
        (affineLftOver T.left).mapIso (E.unitIso.app A)
    let e' : V' ≅ L.obj (E.functor.obj A) := (Over.map T.hom).mapIso e
    let z : P.obj (op (L.obj (E.functor.obj A))) := P.map e'.inv.op p'
    have he : e'.inv ≫ f' = Over.homMk (K.obj (E.functor.obj A)).hom := by
      ext
      exact e.inv.w
    have hz : (⟨E.functor.obj A, z⟩ : Σ j, P.obj (op (L.obj j))) ∈ code x := by
      change η.app _ ⟨z⟩ = _
      have hn := NatTrans.naturality_apply η e'.inv.op
        (show (P ⋙ uliftFunctor.{u + 1}).obj (op V') from ULift.up p')
      change η.app _ ((P ⋙ uliftFunctor.{u + 1}).map e'.inv.op
        (ULift.up p')) = _
      rw [hn, hp', ← Functor.map_comp_apply, ← op_comp, he]
    rw [hxy] at hz
    have hz' : η.app _ ⟨z⟩ = Q.obj.map (Over.homMk (K.obj (E.functor.obj A)).hom).op y := hz
    have hxz : η.app _ ⟨z⟩ = Q.obj.map (Over.homMk (K.obj (E.functor.obj A)).hom).op x := by
      rw [← hxy] at hz
      exact hz
    apply (mono_iff_injective (Q.obj.map e'.inv.op)).mp inferInstance
    change Q.obj.map e'.inv.op (Q.obj.map f'.op x) =
      Q.obj.map e'.inv.op (Q.obj.map f'.op y)
    simpa only [← Functor.map_comp_apply, ← op_comp, he] using hxz.symm.trans hz'
  apply (hQ _ hDC').isSeparatedFor.ext
  intro V f hf
  obtain ⟨W, a, b, ⟨i⟩, hab⟩ := hf
  let V' : Over S := Over.mk (D.f i ≫ T.hom)
  let f' : V' ⟶ T := Over.homMk (D.f i)
  let a' : V ⟶ V' := Over.homMk a (by
    change a ≫ (D.f i ≫ T.hom) = V.hom
    rw [← Category.assoc, hab]
    exact f.w)
  have hh : f = a' ≫ f' := by ext; exact hab.symm
  rw [hh, op_comp, Q.obj.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, hi i]

end AlgebraicGeometry.Scheme
