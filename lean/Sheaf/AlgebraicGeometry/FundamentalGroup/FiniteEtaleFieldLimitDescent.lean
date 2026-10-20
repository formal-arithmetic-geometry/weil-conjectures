/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit

/-!
# Finite étale descent to finite intermediate fields

Source: Stacks Project, Fundamental Groups, Tag 0BTV (lemma-limit), specialized to
constant-field base changes (blueprint: lem-wf-finite-etale-field-limit-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The specified base change `X₀ ×_K Spec A`, using the chosen fibre product.
Source: Stacks Tag 0BTV, field-system specialization
(blueprint: lem-wf-finite-etale-field-limit-descent). -/
abbrev fieldExtensionBase {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) (A : Type u) [Field A] [Algebra K A] : Scheme.{u} :=
  Limits.pullback X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The canonical map between the specified constant-field base changes induced by a
`K`-algebra map. It preserves the projection to `X₀` and induces `Spec φ` on scalars.
Source: Stacks Tag 0BTV and the fibre-product universal property
(blueprint: lem-wf-finite-etale-field-limit-descent). -/
def fieldExtensionBaseMap {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) {A B : Type u} [Field A] [Field B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) :
    fieldExtensionBase X₀ B ⟶ fieldExtensionBase X₀ A :=
  Limits.pullback.map X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K B)))
    X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (𝟙 X₀.left) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (by simp)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext x
      exact (φ.commutes x).symm)

private lemma fieldMap_fst {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) {A B : Type u} [Field A] [Field B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) :
    fieldExtensionBaseMap X₀ φ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ := by
  simp [fieldExtensionBaseMap]

private lemma fieldMap_snd {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) {A B : Type u} [Field A] [Field B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) :
    fieldExtensionBaseMap X₀ φ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  simp [fieldExtensionBaseMap]

private abbrev fieldDiagram {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) : (FiniteIntermediateField K L)ᵒᵖ ⥤ Scheme.{u} where
  obj E := fieldExtensionBase X₀ E.unop.1
  map f := fieldExtensionBaseMap X₀ (IntermediateField.inclusion (leOfHom f.unop))
  map_id E := by
    apply Limits.pullback.hom_ext
    · simp [fieldExtensionBaseMap]
    · simp [fieldExtensionBaseMap, Spec.map_id]
  map_comp f g := by
    apply Limits.pullback.hom_ext
    · simp [fieldExtensionBaseMap]
    · simp [fieldExtensionBaseMap, ← Spec.map_comp]
      rfl

private abbrev fieldCone {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) : Cone (fieldDiagram (L := L) X₀) where
  pt := fieldExtensionBase X₀ L
  π :=
    { app E := fieldExtensionBaseMap X₀ E.unop.1.val
      naturality E F f := by
        change fieldExtensionBaseMap X₀ F.unop.1.val =
          fieldExtensionBaseMap X₀ E.unop.1.val ≫
            fieldExtensionBaseMap X₀ (IntermediateField.inclusion (leOfHom f.unop))
        apply Limits.pullback.hom_ext
        · simp [fieldExtensionBaseMap]
        · simp [fieldExtensionBaseMap, ← Spec.map_comp]
          rfl }

set_option backward.isDefEq.respectTransparency false in
private def fieldConeIsLimit {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (X₀ : Over (Spec (.of K))) :
    IsLimit (fieldCone (L := L) X₀) := by
  letI : IsConnected (FiniteIntermediateField K L)ᵒᵖ := IsCofiltered.isConnected _
  let D := FiniteIntermediateField.specDiagram K L
  let c := FiniteIntermediateField.specCone K L
  let ρ : fieldDiagram (L := L) X₀ ⟶ D :=
    { app E := Limits.pullback.snd _ _
      naturality E F f := by
        exact fieldMap_snd X₀ (IntermediateField.inclusion (leOfHom f.unop)) }
  let v : (Cone.postcompose ρ).obj (fieldCone (L := L) X₀) ⟶ c :=
    { hom := Limits.pullback.snd _ _
      w := by
        intro E
        exact (fieldMap_snd X₀ E.unop.1.val).symm }
  apply isLimitOfIsPullbackOfIsConnected ρ _ c v _
    (FiniteIntermediateField.isLimitSpecCone K L)
  intro E
  exact isPullback_pullback_map X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (Spec.map (CommRingCat.ofHom (algebraMap K E.unop.1)))
    (Spec.map (CommRingCat.ofHom E.unop.1.val.toRingHom)) (by
      rw [← Spec.map_comp]
      congr 1)

private lemma fieldMap_isAffine {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) {A B : Type u} [Field A] [Field B]
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) :
    IsAffineHom (fieldExtensionBaseMap X₀ φ) := by
  apply MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_pullback_map X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K B)))
      (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
        rw [← Spec.map_comp]
        congr 1
        ext x
        exact φ.commutes x)).flip
  infer_instance

private def coverIso {X : Scheme.{u}} {P Q : X.FiniteEtale}
    (e : P.obj.left ≅ Q.obj.left) (he : e.hom ≫ Q.obj.hom = P.obj.hom) : P ≅ Q :=
  ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk e he)

private def pullbackAssocCover {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (P : Z.FiniteEtale) : (pullback f).obj ((pullback g).obj P) ≅ (pullback h).obj P := by
  let sq := (IsPullback.of_hasPullback (Limits.pullback.snd P.obj.hom g) f).paste_horiz
    (IsPullback.of_hasPullback P.obj.hom g)
  have sq' : IsPullback
      (Limits.pullback.fst (Limits.pullback.snd P.obj.hom g) f ≫
        Limits.pullback.fst P.obj.hom g)
      (Limits.pullback.snd (Limits.pullback.snd P.obj.hom g) f) P.obj.hom h := by
    simpa only [hfg] using sq
  exact coverIso sq'.isoPullback (by simp)

private lemma pullbackAssocCover_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (P : Z.FiniteEtale) :
    (pullbackAssocCover f g h hfg P).hom.hom.left ≫ Limits.pullback.fst P.obj.hom h =
      Limits.pullback.fst _ f ≫ Limits.pullback.fst P.obj.hom g := by
  simp [pullbackAssocCover, coverIso]

private lemma fieldMap_comp {K : Type u} [Field K]
    (X₀ : Over (Spec (.of K))) {A B C : Type u} [Field A] [Field B] [Field C]
    [Algebra K A] [Algebra K B] [Algebra K C] (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    fieldExtensionBaseMap X₀ ψ ≫ fieldExtensionBaseMap X₀ φ =
      fieldExtensionBaseMap X₀ (ψ.comp φ) := by
  apply Limits.pullback.hom_ext
  · simp [fieldExtensionBaseMap]
  · simp [fieldExtensionBaseMap, ← Spec.map_comp]
    rfl

private instance fieldBase_compact {K A : Type u} [Field K] [Field A] [Algebra K A]
    (X₀ : Over (Spec (.of K))) [QuasiCompact X₀.hom] :
    CompactSpace (fieldExtensionBase X₀ A) :=
  QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.snd X₀.hom _)

private instance fieldBase_qs {K A : Type u} [Field K] [Field A] [Algebra K A]
    (X₀ : Over (Spec (.of K))) [IsSeparated X₀.hom] :
    QuasiSeparatedSpace (fieldExtensionBase X₀ A) :=
  quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.snd X₀.hom _)

private instance fieldDiagram_affine {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) {i j : (FiniteIntermediateField K L)ᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((fieldDiagram (L := L) X₀).map f) := fieldMap_isAffine X₀ _

private lemma overPullbackStructure {S T R : Scheme.{u}} (p : R ⟶ S) (q : T ⟶ S) :
    (((Over.pullback q).map (Over.homMk p : Over.mk p ⟶ Over.mk (𝟙 S))).left) ≫
      Limits.pullback.snd (𝟙 S) q = Limits.pullback.snd p q := by
  simp

private lemma finite_pullbackStructure_iff {S T R : Scheme.{u}} (p : R ⟶ S)
    (q : T ⟶ S) :
    IsFinite (((Over.pullback q).map
      (Over.homMk p : Over.mk p ⟶ Over.mk (𝟙 S))).left) ↔
      IsFinite (Limits.pullback.snd p q) := by
  rw [← overPullbackStructure p q]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite) _ _).symm

private lemma etale_pullbackStructure_iff {S T R : Scheme.{u}} (p : R ⟶ S)
    (q : T ⟶ S) :
    Etale (((Over.pullback q).map
      (Over.homMk p : Over.mk p ⟶ Over.mk (𝟙 S))).left) ↔
      Etale (Limits.pullback.snd p q) := by
  rw [← overPullbackStructure p q]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).symm

attribute [local irreducible] coverIso pullbackAssocCover

private lemma pullbackAssocCover_map {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (P : Z.FiniteEtale) :
    (pullbackAssocCover f g h hfg P).hom.hom.left ≫
        Limits.pullback.map P.obj.hom h P.obj.hom g (𝟙 _) f (𝟙 _)
          (by simp) (by simp [hfg]) =
      Limits.pullback.fst (Limits.pullback.snd P.obj.hom g) f := by
  apply Limits.pullback.hom_ext
  · simp only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_fst,
      Category.comp_id]
    exact pullbackAssocCover_fst f g h hfg P
  · simp only [Limits.pullback.map, Category.assoc, Limits.pullback.lift_snd]
    rw [← Category.assoc]
    have hw := hom_left_comp (pullbackAssocCover f g h hfg P).hom
    change (pullbackAssocCover f g h hfg P).hom.hom.left ≫
      Limits.pullback.snd P.obj.hom h = _ at hw
    rw [hw]
    exact (Limits.pullback.condition (f := Limits.pullback.snd P.obj.hom g) (g := f)).symm

private lemma pullbackAssocCover_naturality {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    {P Q : Z.FiniteEtale}
    (t : (pullback h).obj P ⟶ (pullback h).obj Q)
    (t' : (pullback g).obj P ⟶ (pullback g).obj Q)
    (ht : Limits.pullback.map P.obj.hom h P.obj.hom g (𝟙 _) f (𝟙 _)
        (by simp) (by simp [hfg]) ≫ t'.hom.left ≫ Limits.pullback.fst Q.obj.hom g =
      t.hom.left ≫ Limits.pullback.fst Q.obj.hom h) :
    (pullbackAssocCover f g h hfg P).inv ≫ (pullback f).map t' ≫
        (pullbackAssocCover f g h hfg Q).hom = t := by
  apply (cancel_epi (pullbackAssocCover f g h hfg P).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply hom_ext
  change ((pullback f).map t').hom.left ≫
      (pullbackAssocCover f g h hfg Q).hom.hom.left =
    (pullbackAssocCover f g h hfg P).hom.hom.left ≫ t.hom.left
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pullbackAssocCover_fst]
    rw [pullback_map_hom_left]
    simp only [Limits.pullback.map, Limits.pullback.lift_fst_assoc]
    rw [← ht, ← Category.assoc, ← Category.assoc, pullbackAssocCover_map]
    rfl
  · exact (hom_left_comp (((pullback f).map t') ≫
        (pullbackAssocCover f g h hfg Q).hom)).trans
      (hom_left_comp ((pullbackAssocCover f g h hfg P).hom ≫ t)).symm

private lemma pullback_map_fst {X Y : Scheme.{u}} (q : X ⟶ Y)
    {P Q : Y.FiniteEtale} (f : P ⟶ Q) :
    ((pullback q).map f).hom.left ≫ Limits.pullback.fst Q.obj.hom q =
      Limits.pullback.fst P.obj.hom q ≫ f.hom.left := by
  simp [pullback_map_hom_left, Limits.pullback.map]

private lemma pullback_map_eq_iff {X Y : Scheme.{u}} (q : X ⟶ Y)
    {P Q : Y.FiniteEtale} (f g : P ⟶ Q) :
    (pullback q).map f = (pullback q).map g ↔
      Limits.pullback.fst P.obj.hom q ≫ f.hom.left =
        Limits.pullback.fst P.obj.hom q ≫ g.hom.left := by
  constructor
  · intro h
    have hh := congrArg (fun a ↦ a.hom.left ≫ Limits.pullback.fst Q.obj.hom q) h
    simpa only [pullback_map_fst] using hh
  · intro h
    apply hom_ext
    apply Limits.pullback.hom_ext
    · simpa only [pullback_map_fst] using h
    · exact (hom_left_comp ((pullback q).map f)).trans
        (hom_left_comp ((pullback q).map g)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Finite étale covers, all their morphisms, and equality of morphisms descend to finite
intermediate fields of a separable algebraic extension.

Source: Stacks Tag 0BTV (lemma-limit), specialized to the finite intermediate fields
(blueprint: lem-wf-finite-etale-field-limit-descent).

Proof:
1. The proved FiniteIntermediateField.isLimitSpecCone supplies the small directed
   system of finite intermediate fields, with least stage K and union L.
2. Every field base change is separated of finite type, hence qcqs, by
   lem-pod-separated-finite-type-base-change and lem-weil-pbc-qcqs-over-affine.
   The transition maps are affine by lem-weil-pbc-affine-morphism-permanence.
3. Spec L is the limit of the field spectra by lem-weil-pbc-spec-small-colimit-limit.
   The fibre-product universal property (def-pc-fibre-product) exhibits X_L as the
   limit of the specified X_E, with exactly these projections.
4. Mathlib instances make finite étale covers locally finitely presented,
   quasi-compact and quasi-separated, as required for finite-presentation descent.
5. Object descent in thm-pd-spreading-out gives a finitely presented model. Its source
   is qcqs by lem-weil-pbc-qcqs-morphism-permanence.
6. Apply lem-weil-pbc-descend-finite and lem-weil-pbc-descend-etale independently
   to the model, and choose a common upper bound of their stages.
7. Finiteness and etaleness persist there by base change. Pullback pasting identifies
   the limit of this finite étale model with the original cover, giving (1).
8. The morphism clause of thm-pd-spreading-out gives (2). The two comparison isomorphisms
   preserve the projections to the original covers, so they are the canonical pullback
   associativity identifications, not arbitrary changes of coordinates.
9. The equality clause of thm-pd-spreading-out gives (3) for the two finitely presented
   covers. Every larger index is a finite intermediate field containing the initial one.
-/
theorem finiteEtale_fieldLimit_descent {K L : Type u} [Field K] [Field L]
    [Algebra K L] [Algebra.IsSeparable K L] (X₀ : Over (Spec (.of K)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (∀ P : (fieldExtensionBase X₀ L).FiniteEtale,
      ∃ (E : IntermediateField K L), FiniteDimensional K E ∧
        ∃ P_E : (fieldExtensionBase X₀ E).FiniteEtale,
          Nonempty ((pullback (fieldExtensionBaseMap X₀ E.val)).obj P_E ≅ P)) ∧
    (∀ (E : IntermediateField K L), FiniteDimensional K E →
      ∀ (P Q : (fieldExtensionBase X₀ E).FiniteEtale)
        (f : (pullback (fieldExtensionBaseMap X₀ E.val)).obj P ⟶
          (pullback (fieldExtensionBaseMap X₀ E.val)).obj Q),
      ∃ (E' : IntermediateField K L) (_ : FiniteDimensional K E') (h : E ≤ E')
        (f' : (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj P ⟶
          (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj Q)
        (eP : (pullback (fieldExtensionBaseMap X₀ E'.val)).obj
            ((pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj P) ≅
          (pullback (fieldExtensionBaseMap X₀ E.val)).obj P)
        (eQ : (pullback (fieldExtensionBaseMap X₀ E'.val)).obj
            ((pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h))).obj Q) ≅
          (pullback (fieldExtensionBaseMap X₀ E.val)).obj Q),
        eP.hom.hom.left ≫ Limits.pullback.fst P.obj.hom
            (fieldExtensionBaseMap X₀ E.val) =
          Limits.pullback.fst _ (fieldExtensionBaseMap X₀ E'.val) ≫
            Limits.pullback.fst P.obj.hom
              (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)) ∧
        eQ.hom.hom.left ≫ Limits.pullback.fst Q.obj.hom
            (fieldExtensionBaseMap X₀ E.val) =
          Limits.pullback.fst _ (fieldExtensionBaseMap X₀ E'.val) ≫
            Limits.pullback.fst Q.obj.hom
              (fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)) ∧
        eP.inv ≫ (pullback (fieldExtensionBaseMap X₀ E'.val)).map f' ≫ eQ.hom = f) ∧
    (∀ (E : IntermediateField K L), FiniteDimensional K E →
      ∀ (P Q : (fieldExtensionBase X₀ E).FiniteEtale) (f h : P ⟶ Q),
        (pullback (fieldExtensionBaseMap X₀ E.val)).map f =
          (pullback (fieldExtensionBaseMap X₀ E.val)).map h →
        ∃ (E' : IntermediateField K L) (_ : FiniteDimensional K E') (hE : E ≤ E'),
          (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion hE))).map f =
            (pullback (fieldExtensionBaseMap X₀ (IntermediateField.inclusion hE))).map h) :=
by
  classical
  let D := fieldDiagram (L := L) X₀
  let c := fieldCone (L := L) X₀
  let hc := fieldConeIsLimit (L := L) X₀
  have : ∀ i, CompactSpace (D.obj i) := fun i ↦ fieldBase_compact X₀
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i ↦ fieldBase_qs X₀
  refine ⟨?_, ?_, ?_⟩
  · intro P
    have : IsFinite P.obj.hom := P.property
    have : Etale P.obj.hom := P.obj.prop
    obtain ⟨i, Y, p, hp, hqc, hqs, a, hsq⟩ :=
      Scheme.exists_isPullback_of_finitePresentation hc P.obj.hom
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
    have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
    have : CompactSpace (Over.mk p).left := ‹CompactSpace Y›
    have : QuasiSeparatedSpace (Over.mk p).left := ‹QuasiSeparatedSpace Y›
    have : CompactSpace (Over.mk (𝟙 (D.obj i))).left :=
      (inferInstance : CompactSpace (D.obj i))
    have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
      (inferInstance : QuasiSeparatedSpace (D.obj i))
    have hfin : IsFinite (Limits.pullback.snd p (c.π.app i)) := by
      rw [← hsq.isoPullback_inv_snd]
      infer_instance
    have het : Etale (Limits.pullback.snd p (c.π.app i)) := by
      rw [← hsq.isoPullback_inv_snd]
      infer_instance
    let pOver : Over.mk p ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk p (by simp)
    have : LocallyOfFiniteType pOver.left := (inferInstance : LocallyOfFiniteType p)
    have : LocallyOfFinitePresentation pOver.left := hp
    obtain ⟨j₁, h₁, hf₁⟩ := exists_isFinite_baseChange_stage D c hc i.unop
      (Over.mk p) (Over.mk (𝟙 _)) pOver
      ((finite_pullbackStructure_iff p _).mpr hfin)
    obtain ⟨j₂, h₂, he₂⟩ := Etale.exists_stage_of_inverseLimit D c hc i.unop
      (Over.mk p) (Over.mk (𝟙 _)) pOver
      ((etale_pullbackStructure_iff p _).mpr het)
    obtain ⟨j, hj₁, hj₂⟩ := exists_ge_ge j₁ j₂
    let hij : i.unop ≤ j := h₁.trans hj₁
    let q := D.map (homOfLE hij).op
    have hfinj : IsFinite (Limits.pullback.snd p q) := by
      apply MorphismProperty.of_isPullback (P := @IsFinite)
        (isPullback_pullback_map p q (D.map (homOfLE h₁).op)
          (D.map (homOfLE hj₁).op) (by
            rw [← D.map_comp]))
      exact (finite_pullbackStructure_iff p _).mp hf₁
    have hetj : Etale (Limits.pullback.snd p q) := by
      apply MorphismProperty.of_isPullback (P := @Etale)
        (isPullback_pullback_map p q (D.map (homOfLE h₂).op)
          (D.map (homOfLE hj₂).op) (by
            rw [← D.map_comp]))
      exact (etale_pullbackStructure_iff p _).mp he₂
    let Pj : (fieldExtensionBase X₀ j.1).FiniteEtale :=
      ⟨MorphismProperty.Over.mk ⊤ (Limits.pullback.snd p q) hetj, hfinj⟩
    refine ⟨j.1, j.2, Pj, ⟨?_⟩⟩
    have sq := isPullback_pullback_map p (c.π.app i) q (c.π.app (.op j))
      (c.w (homOfLE hij).op)
    apply coverIso (sq.isoPullback.symm ≪≫ hsq.isoPullback.symm)
    change (sq.isoPullback.inv ≫ hsq.isoPullback.inv) ≫ P.obj.hom = _
    rw [Category.assoc, hsq.isoPullback_inv_snd]
    exact sq.isoPullback_inv_snd
  · intro E hE P Q f
    let i : FiniteIntermediateField K L := ⟨E, hE⟩
    have : IsFinite P.obj.hom := P.property
    have : IsFinite Q.obj.hom := Q.property
    have : Etale P.obj.hom := P.obj.prop
    have : Etale Q.obj.hom := Q.obj.prop
    let ψ := f.hom.left ≫ Limits.pullback.fst Q.obj.hom (c.π.app (.op i))
    have hψ : ψ ≫ Q.obj.hom =
        Limits.pullback.fst P.obj.hom (c.π.app (.op i)) ≫ P.obj.hom := by
      have hw : f.hom.left ≫ Limits.pullback.snd Q.obj.hom (c.π.app (.op i)) =
          Limits.pullback.snd P.obj.hom (c.π.app (.op i)) := hom_left_comp f
      dsimp [ψ]
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hw]
      exact (Limits.pullback.condition (f := _) (g := _)).symm
    obtain ⟨j, a, ψj, hj, hdesc⟩ :=
      Scheme.exists_pullback_hom_of_isLimit (D := D) (c := c) hc
        (i := .op i) P.obj.hom Q.obj.hom ψ hψ
    let h : E ≤ j.unop.1 := leOfHom a.unop
    let q := fieldExtensionBaseMap X₀ (IntermediateField.inclusion h)
    let f' : (pullback q).obj P ⟶ (pullback q).obj Q :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk
        (Limits.pullback.lift ψj (Limits.pullback.snd P.obj.hom q)
          (hj.trans (Limits.pullback.condition (f := _) (g := _)))) (by simp))
    have hcomp : fieldExtensionBaseMap X₀ j.unop.1.val ≫ q =
        fieldExtensionBaseMap X₀ E.val := by
      rw [fieldMap_comp]
      rfl
    let eP : (pullback (fieldExtensionBaseMap X₀ j.unop.1.val)).obj
        ((pullback q).obj P) ≅ (pullback (fieldExtensionBaseMap X₀ E.val)).obj P :=
      pullbackAssocCover (fieldExtensionBaseMap X₀ j.unop.1.val) q
        (fieldExtensionBaseMap X₀ E.val) hcomp P
    let eQ : (pullback (fieldExtensionBaseMap X₀ j.unop.1.val)).obj
        ((pullback q).obj Q) ≅ (pullback (fieldExtensionBaseMap X₀ E.val)).obj Q :=
      pullbackAssocCover (fieldExtensionBaseMap X₀ j.unop.1.val) q
        (fieldExtensionBaseMap X₀ E.val) hcomp Q
    refine ⟨j.unop.1, j.unop.2, h, f', eP, eQ, ?_, ?_, ?_⟩
    · exact pullbackAssocCover_fst _ _ _ _ P
    · exact pullbackAssocCover_fst _ _ _ _ Q
    · apply pullbackAssocCover_naturality _ _ _ hcomp f f'
      change _ ≫ Limits.pullback.lift ψj (Limits.pullback.snd P.obj.hom q) _ ≫
        Limits.pullback.fst Q.obj.hom q = _
      rw [Limits.pullback.lift_fst]
      exact hdesc
  · intro E hE P Q f g hfg
    let i : FiniteIntermediateField K L := ⟨E, hE⟩
    have : IsFinite P.obj.hom := P.property
    have : IsFinite Q.obj.hom := Q.property
    have : Etale P.obj.hom := P.obj.prop
    have : Etale Q.obj.hom := Q.obj.prop
    have heq : Limits.pullback.fst P.obj.hom (c.π.app (.op i)) ≫ f.hom.left =
        Limits.pullback.fst P.obj.hom (c.π.app (.op i)) ≫ g.hom.left :=
      (pullback_map_eq_iff _ f g).mp hfg
    obtain ⟨j, a, ha⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit (D := D) (c := c) hc
      (i := .op i) P.obj.hom Q.obj.hom f.hom.left g.hom.left (hom_left_comp f) (hom_left_comp g) heq
    refine ⟨j.unop.1, j.unop.2, leOfHom a.unop, ?_⟩
    exact (pullback_map_eq_iff _ f g).mpr ha

end AlgebraicGeometry.Scheme.FiniteEtale
