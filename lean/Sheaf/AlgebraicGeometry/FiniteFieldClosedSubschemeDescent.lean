/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of closed subschemes to finite constant fields

Source: Weil conjectures blueprint, main-20261015, `sec-deligne-laumon-general`,
`sk-i-dl-general-real/lem-zl-bertini-finite-cover-curve.proof.md`, final paragraph
(blueprint: lem-zl-bertini-finite-field-descent).

The isomorphism over `Spec k` and its equation after projection to `X₀` express equality
as closed subschemes of the geometric fibre. They retain the scheme structure, including
nilpotents. The resulting automorphism of `C` is a scheme automorphism; it is semilinear
on the coefficient field and need not be a morphism over `k`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

private abbrev Stage (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  {A : Subalgebra D.k₀ D.k // A.FG}

private local instance (D : WeilConjectures.FiniteFieldDatum.{u}) : Nonempty (Stage D) :=
  ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

private local instance (D : WeilConjectures.FiniteFieldDatum.{u}) : IsDirectedOrder (Stage D) :=
  ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩, show A.1 ≤ A.1 ⊔ B.1 from le_sup_left,
    show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def baseDiagram (D : WeilConjectures.FiniteFieldDatum.{u}) :
    (Stage D)ᵒᵖ ⥤ Scheme.{u} :=
  (CommRingCat.fgSubalgebraDiagramOf D.k₀ D.k).op ⋙ Scheme.Spec

set_option backward.isDefEq.respectTransparency false in
private noncomputable def baseCone (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Cone (baseDiagram D) :=
  Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf D.k₀ D.k).op

set_option backward.isDefEq.respectTransparency false in
private noncomputable def baseCone_isLimit (D : WeilConjectures.FiniteFieldDatum.{u}) :
    IsLimit (baseCone D) :=
  isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFGSubalgebraCocone D.k₀ D.k).op

set_option backward.isDefEq.respectTransparency false in
private noncomputable def stageBase (D : WeilConjectures.FiniteFieldDatum.{u})
    (A : (Stage D)ᵒᵖ) : (baseDiagram D).obj A ⟶ Spec (CommRingCat.of D.k₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A.unop.val))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ambientDiagram (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀))) : (Stage D)ᵒᵖ ⥤ Scheme.{u} where
  obj A := pullback X₀.hom (stageBase D A)
  map {A B} f := pullback.map _ _ _ _ (𝟙 _) ((baseDiagram D).map f) (𝟙 _)
    (by simp) (by
      symm
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1)
  map_id A := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ambientCone (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀))) : Cone (ambientDiagram D X₀) where
  pt := pullback X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  π.app A := pullback.map _ _ _ _ (𝟙 _) ((baseCone D).π.app A) (𝟙 _)
    (by simp) (by
      symm
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1)
  π.naturality {A B} f := by
    apply pullback.hom_ext <;> simp [ambientDiagram]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ambientCone_isLimit (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀))) : IsLimit (ambientCone D X₀) := by
  have : IsConnected (Stage D)ᵒᵖ := IsCofiltered.isConnected _
  let α : ambientDiagram D X₀ ⟶ baseDiagram D :=
    { app := fun A ↦ pullback.snd _ _
      naturality := fun f ↦ by simp [ambientDiagram] }
  apply isLimitOfIsPullbackOfIsConnected α (ambientCone D X₀) (baseCone D)
    { hom := pullback.snd _ _
      w := fun A ↦ by simp [ambientCone, α] } _ (baseCone_isLimit D)
  intro A
  exact isPullback_pullback_map _ _ _ _ (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1)

set_option backward.isDefEq.respectTransparency false in
private theorem stage_finiteDimensional (D : WeilConjectures.FiniteFieldDatum.{u})
    (A : Stage D) : Module.Finite D.k₀ A.val := by
  have : Algebra.FiniteType D.k₀ A.val := A.val.fg_iff_finiteType.mp A.property
  have : Algebra.IsIntegral D.k₀ A.val :=
    ⟨fun x ↦ (isIntegral_algHom_iff A.val.val Subtype.val_injective).mp
      (Algebra.IsIntegral.isIntegral (x : D.k))⟩
  exact Algebra.IsIntegral.finite

set_option backward.isDefEq.respectTransparency false in
private theorem stage_field (D : WeilConjectures.FiniteFieldDatum.{u}) (A : Stage D) :
    ∃ (m : ℕ) (hm : 1 ≤ m) (e : A.val ≃+* D.extensionSubfield m hm),
      (D.extensionSubfield m hm).subtype.comp e.toRingHom = A.val.val.toRingHom := by
  have : Module.Finite D.k₀ A.val := stage_finiteDimensional D A
  have : Algebra.IsIntegral D.k₀ A.val :=
    Algebra.IsIntegral.of_injective A.val.val Subtype.val_injective
  let K := Algebra.IsAlgebraic.toIntermediateField A.val
  let m := Module.finrank D.k₀ A.val
  have hm : 1 ≤ m := Module.finrank_pos
  have hcard : Nat.card K.toSubfield = D.q ^ m := by
    change Nat.card A.val = _
    rw [Module.natCard_eq_pow_finrank (K := D.k₀), D.card_base]
  have heq : K.toSubfield = D.extensionSubfield m hm :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.1 _ hcard
  let e : A.val ≃+* D.extensionSubfield m hm :=
    { toFun := fun x ↦ ⟨x.val, by rw [← heq]; exact x.property⟩
      invFun := fun x ↦ ⟨x.val, by
        have hx : x.val ∈ K.toSubfield := by rw [heq]; exact x.property
        exact hx⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact ⟨m, hm, e, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_closed_stage (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (C : Scheme.{u}) (i : C ⟶ (D.geometricFiber X₀).left) [IsClosedImmersion i] :
    ∃ (A : (Stage D)ᵒᵖ) (Y : Scheme.{u}) (p : Y ⟶ (ambientDiagram D X₀).obj A)
      (h : C ⟶ Y), IsClosedImmersion p ∧
        IsPullback h i p ((ambientCone D X₀).π.app A) := by
  have hD {A B : (Stage D)ᵒᵖ} (f : A ⟶ B) :
      IsAffineHom ((baseDiagram D).map f) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  have hDA {A B : (Stage D)ᵒᵖ} (f : A ⟶ B) :
      IsAffineHom ((ambientDiagram D X₀).map f) :=
    MorphismProperty.of_isPullback
      (isPullback_pullback_map X₀.hom (stageBase D A) (stageBase D B)
        ((baseDiagram D).map f) (by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        congr 1)).flip (hD f)
  have hAffine (A : (Stage D)ᵒᵖ) : IsAffine ((baseDiagram D).obj A) :=
    inferInstanceAs (IsAffine (Spec _))
  have hcompact (A : (Stage D)ᵒᵖ) : CompactSpace ((ambientDiagram D X₀).obj A) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd X₀.hom (stageBase D A))
  have hnoeth (A : (Stage D)ᵒᵖ) : IsLocallyNoetherian ((ambientDiagram D X₀).obj A) := by
    have : Algebra.FiniteType D.k₀ A.unop.val :=
      A.unop.val.fg_iff_finiteType.mp A.unop.property
    have : IsNoetherianRing A.unop.val := Algebra.FiniteType.isNoetherianRing D.k₀ A.unop.val
    have : IsLocallyNoetherian ((baseDiagram D).obj A) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A.unop.val)))
    exact LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd X₀.hom (stageBase D A))
  have hqs (A : (Stage D)ᵒᵖ) : QuasiSeparatedSpace ((ambientDiagram D X₀).obj A) :=
    inferInstance
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
  have : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
  have : LocallyOfFinitePresentation i := inferInstance
  obtain ⟨A, Y, p, hp, hqc, hsep, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (ambientCone_isLimit D X₀) i
  have := hp
  have := hqc
  have := hsep
  obtain ⟨B, f, hf⟩ :=
    Scheme.exists_isClosedImmersion_pullback_snd (ambientCone_isLimit D X₀) H
  refine ⟨B, pullback p ((ambientDiagram D X₀).map f), pullback.snd _ _,
    isPullbackLift _ _ f H, ?_, isPullback_isPullbackLift (D := ambientDiagram D X₀)
      (c := ambientCone D X₀) f H⟩
  have hfB := hf (𝟙 B)
  erw [Category.id_comp] at hfB
  exact hfB

set_option backward.isDefEq.respectTransparency false in
private theorem geometricFrobenius_pow_projections
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    let _ := Fintype.ofFinite D.k₀
    let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
    (D.geometricFrobenius X₀ ^ m).hom ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    (D.geometricFrobenius X₀ ^ m).hom ≫ (D.geometricFiber X₀).hom =
      (D.geometricFiber X₀).hom ≫ Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) := by
  let _ := Fintype.ofFinite D.k₀
  let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
  have h := D.galoisMap_projections X₀.hom σ
  induction m with
  | zero =>
      constructor
      · change (𝟙 _) ≫ _ = _
        exact Category.id_comp _
      · change (𝟙 _) ≫ _ = _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id D.k))
        change (𝟙 _) ≫ _ = _ ≫ Spec.map (𝟙 _)
        rw [Spec.map_id, Category.comp_id, Category.id_comp]
  | succ m ih =>
      constructor
      · rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc, ih.1]
        exact h.1
      · rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc, ih.2]
        change D.galoisMap X₀.hom σ ≫ (D.geometricFiber X₀).hom ≫
          Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) = _
        erw [reassoc_of% h.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        change (D.geometricFiber X₀).hom ≫
          Spec.map (CommRingCat.ofHom (σ * σ ^ m).toRingHom) = _
        rw [← pow_succ']

set_option backward.isDefEq.respectTransparency false in
/-- A closed subscheme of a finite-type geometric fibre descends to a finite constant-field
extension, and some positive power of geometric Frobenius restricts to an automorphism.
Source: blueprint main-20261015, `lem-zl-bertini-finite-cover-curve.proof.md`, final paragraph
(blueprint: lem-zl-bertini-finite-field-descent).

Proof:
1. Use the directed system of finitely generated k₀-subalgebras A of k. Its colimit
   is k, so Spec preserves the opposite limiting cone. Pulling back X₀ along this
   cone gives a limiting cone with vertex X₀ × Spec k, by the pullback universal property.
2. The stages X₀ × Spec A are quasi-compact and locally Noetherian: A is a finitely
   generated algebra over a field, and the structure maps are of finite type. Thus the
   stages are quasi-separated. The geometric fibre is locally Noetherian as well.
3. The closed immersion i is quasi-compact, quasi-separated, and locally of finite
   presentation over its Noetherian target. Apply the object clause of Stacks Tag 01ZM
   directly to i over the ambient limiting cone. This descends the source together
   with its actual map to an ambient stage. Stacks Tag 01ZP then makes the map a closed
   immersion after increasing the stage. The resulting square remains cartesian.
4. Every finitely generated subalgebra A is integral and finite-dimensional over k₀,
   since k/k₀ is algebraic. It is therefore a field, of cardinality q^m for the positive
   integer m = finrank k₀ A. Uniqueness of the subfield with q^m elements identifies
   A with extensionSubfield m hm, compatibly with both inclusions into k.
5. Transport the descended closed immersion along this field isomorphism. Pasting its
   cartesian square with the ambient base-change square gives the required isomorphism
   over Spec k. Its projection equations give the specified equality of embeddings.
6. The mth power of geometric field Frobenius fixes extensionSubfield m hm pointwise.
   The cartesian square lifts the identity of the descended source together with this
   coefficient automorphism to C. Lifting the inverse coefficient automorphism gives
   its inverse, by pullback uniqueness. Induction gives the projections of the mth
   power of ambient geometric Frobenius. Comparing both ambient projections then proves
   equivariance of the original embedding. -/
theorem exists_closed_subscheme_finiteField_descent (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (C : Scheme.{u}) (i : C ⟶ (D.geometricFiber X₀).left) [IsClosedImmersion i] :
    ∃ (m : ℕ) (hm : 1 ≤ m) (Cₘ : Over (Spec (CommRingCat.of (D.extensionSubfield m hm))))
      (iₘ : Cₘ ⟶ (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀),
      IsClosedImmersion iₘ.left ∧
      (∃ e : Over.mk (i ≫ (D.geometricFiber X₀).hom) ≅
          (Over.pullback (Spec.map
            (CommRingCat.ofHom (D.extensionSubfield m hm).subtype))).obj Cₘ,
        e.hom.left ≫
            pullback.fst Cₘ.hom
              (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
            iₘ.left ≫
            pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) =
          i ≫ pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
      ∃ φ : Aut C, φ.hom ≫ i = i ≫ (D.geometricFrobenius X₀ ^ m).hom := by
  classical
  obtain ⟨A, Y, p, h, hp, H⟩ := exists_closed_stage D X₀ C i
  have := hp
  obtain ⟨m, hm, e, he⟩ := stage_field D A.unop
  let E := D.extensionSubfield m hm
  let b := Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))
  let t := Spec.map (CommRingCat.ofHom E.subtype)
  let s := Scheme.Spec.mapIso e.toCommRingCatIso.op
  have hEmb : E.subtype.comp (D.extensionEmbedding m hm) = algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have hs : s.hom ≫ stageBase D A = b := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A.unop.val)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    change (E.subtype.comp e.toRingHom) (algebraMap D.k₀ A.unop.val x) =
      (E.subtype.comp (D.extensionEmbedding m hm)) x
    rw [he, hEmb]
    rfl
  have ht : t ≫ s.hom = (baseCone D).π.app A := by
    change Spec.map (CommRingCat.ofHom E.subtype) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom) =
        Spec.map (CommRingCat.ofHom A.unop.val.val.toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]
  have hb : t ≫ b = Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hEmb]
  let a : pullback X₀.hom b ⟶ (ambientDiagram D X₀).obj A :=
    pullback.map _ _ _ _ (𝟙 _) s.hom (𝟙 _) (by simp) (by simpa using hs.symm)
  have : IsIso a := inferInstanceAs (IsIso (pullback.map _ _ _ _ _ _ _ _ _))
  let pE : Y ⟶ pullback X₀.hom b := p ≫ inv a
  have hpE : IsClosedImmersion pE := inferInstanceAs (IsClosedImmersion (p ≫ inv a))
  let π : (D.geometricFiber X₀).left ⟶ pullback X₀.hom b :=
    pullback.map _ _ _ _ (𝟙 _) t (𝟙 _) (by simp) (by simpa using hb.symm)
  have hπ : π ≫ a = (ambientCone D X₀).π.app A := by
    apply pullback.hom_ext <;> simp [π, a, ambientCone, ht]
  have HE : IsPullback h i pE π := by
    apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso a).symm
    · simp
    · simp
    · simp [pE]
    · simp [← hπ]
  have HB : IsPullback π (D.geometricFiber X₀).hom (pullback.snd X₀.hom b) t :=
    isPullback_pullback_map X₀.hom _ b t hb
  have HC := HE.paste_vert HB
  let Cₘ : Over (Spec (CommRingCat.of E)) := Over.mk (pE ≫ pullback.snd X₀.hom b)
  let iₘ : Cₘ ⟶ (Over.pullback b).obj X₀ := Over.homMk pE
  refine ⟨m, hm, Cₘ, iₘ, hpE, ⟨?_, ?_⟩⟩
  · refine ⟨Over.isoMk HC.isoPullback (by exact HC.isoPullback_hom_snd), ?_⟩
    change HC.isoPullback.hom ≫ pullback.fst Cₘ.hom t ≫ pE ≫
      pullback.fst X₀.hom b = _
    erw [IsPullback.isoPullback_hom_fst_assoc, HE.w_assoc]
    simp [π]
  · let _ := Fintype.ofFinite D.k₀
    let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k
    let δ : Aut (Spec (CommRingCat.of D.k)) :=
      Scheme.Spec.mapIso (σ ^ m).toRingEquiv.toCommRingCatIso.op
    have hcard : Nat.card E = D.q ^ m :=
      (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
        D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
    have : Finite E :=
      (Nat.card_pos_iff.mp (by rw [hcard]; exact pow_pos (by
        rw [← D.card_base]; exact Nat.card_pos) m)).2
    have hδ : δ.hom ≫ t = t := by
      change Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫
        Spec.map (CommRingCat.ofHom E.subtype) = Spec.map (CommRingCat.ofHom E.subtype)
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
        D.k₀ D.k m (by rw [← Nat.card_eq_fintype_card, D.card_base]; exact hcard) E.subtype x
    have hδinv : δ.inv ≫ t = t := by
      rw [Iso.inv_comp_eq, hδ]
    let w := i ≫ (D.geometricFiber X₀).hom
    let f : C ⟶ C := HC.lift h (w ≫ δ.hom) (by
      rw [Category.assoc w δ.hom t, hδ]
      exact HC.w)
    let g : C ⟶ C := HC.lift h (w ≫ δ.inv) (by
      rw [Category.assoc w δ.inv t, hδinv]
      exact HC.w)
    have fh : f ≫ h = h := HC.lift_fst _ _ _
    have gh : g ≫ h = h := HC.lift_fst _ _ _
    have fw : f ≫ w = w ≫ δ.hom := HC.lift_snd _ _ _
    have gw : g ≫ w = w ≫ δ.inv := HC.lift_snd _ _ _
    let φ : Aut C :=
      { hom := f
        inv := g
        hom_inv_id := by
          apply HC.hom_ext
          · simp only [Category.assoc, gh, fh, Category.id_comp]
          · change (f ≫ g) ≫ w = (𝟙 C) ≫ w
            rw [Category.assoc, gw, ← Category.assoc, fw, Category.assoc,
              δ.hom_inv_id, Category.comp_id, Category.id_comp]
        inv_hom_id := by
          apply HC.hom_ext
          · simp only [Category.assoc, fh, gh, Category.id_comp]
          · change (g ≫ f) ≫ w = (𝟙 C) ≫ w
            rw [Category.assoc, fw, ← Category.assoc, gw, Category.assoc,
              δ.inv_hom_id, Category.comp_id, Category.id_comp] }
    refine ⟨φ, ?_⟩
    apply pullback.hom_ext
    · have hi : i ≫ pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          h ≫ pE ≫ pullback.fst X₀.hom b := by
        rw [HE.w_assoc]
        simp [π]
      change (f ≫ i) ≫ _ = (i ≫ (D.geometricFrobenius X₀ ^ m).hom) ≫ _
      simp only [Category.assoc]
      rw [hi, ← Category.assoc, ← Category.assoc, fh]
      simpa only [Category.assoc, (geometricFrobenius_pow_projections D X₀ m).1] using
        hi.symm
    · change φ.hom ≫ w = i ≫ (D.geometricFrobenius X₀ ^ m).hom ≫
        (D.geometricFiber X₀).hom
      rw [(geometricFrobenius_pow_projections D X₀ m).2]
      exact HC.lift_snd _ _ _

end WeilConjectures.FiniteFieldDatum
