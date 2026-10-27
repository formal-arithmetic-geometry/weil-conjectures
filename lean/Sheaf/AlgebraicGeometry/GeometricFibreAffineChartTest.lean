module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties

/-! # Affine charts of a fibre after arbitrary base change

Source: Stacks Project, Tag 0576, first proof sentence, and Tags 01JR, 01I4, 01J2
(blueprint: lem-trf-geometric-fibre-affine-chart-test).

The chosen affine charts are open immersions from spectra, jointly surjective on points.
The field extension is a ring homomorphism `h`; `hH` specifies its composite residue-field
algebra structure. No finiteness, flatness, or nonemptiness assumption is made.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Affine chart test after arbitrary base change and extension of the residue field.
Source: Stacks Project, Tag 0576, first proof sentence; Tags 01JR, 01I4, 01J2
(blueprint: lem-trf-geometric-fibre-affine-chart-test).

Proof:
1. Naturality of the residue-field point maps and `hH` identify the composite
   `Spec H → T`. The universal property in `def-pc-fibre-product` constructs `p`
   with its prescribed maps to `X` and `Spec κ(g t')`.
2. Paste the square defining the base change over `T'` with that defining `X ×_T T'`.
   Cancel the square defining the original fibre, using
   `lem-weil-pbc-cartesian-square-pasting`. The resulting cartesian square gives `e`
   and its projection identities directly, without an intermediate `κ(t')`-fibre.
3. Base change preserves the open immersions of the given charts
   (`lem-weil-pbc-open-fibre-product`). Pasting their pullback squares with the square
   for `p` and applying `lem-weil-pbc-fibre-product-affine-spectra` gives the tensor
   spectrum charts and both projection identities. The ring structure is the standard
   one of `lem-weil-pbc-algebra-tensor-pushout-universal-property`, clause (1).
4. The scheme pullback comparison is surjective on underlying points, so the pulled-back
   charts cover. Apply `lem-trf-reduced-scheme-open-cover`, transfer reducedness across
   each chart isomorphism (`def-pc-reduced-scheme`), and use
   `lem-weil-pbc-affine-scheme-reduced-iff`. These constructions also apply when the
   index type or individual charts are empty.
-/
theorem geometric_fibre_affine_chart_test
    {X T T' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T) (t' : T')
    (I : Type v) (A : I → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra (T.residueField (g t')) (A i)]
    (ι : ∀ i, Spec (.of (A i)) ⟶ f.fiber (g t'))
    [∀ i, IsOpenImmersion (ι i)]
    (hι : ∀ i, ι i ≫ f.fiberToSpecResidueField (g t') =
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField (g t')) (A i))))
    (hcover : ∀ y : f.fiber (g t'), ∃ (i : I) (x : Spec (.of (A i))), ι i x = y)
    (H : Type u) [Field H] (h : T'.residueField t' →+* H)
    [Algebra (T.residueField (g t')) H]
    (hH : algebraMap (T.residueField (g t')) H = h.comp (g.residueFieldMap t').hom) :
    ∃ (p : pullback (pullback.snd f g)
        (Spec.map (CommRingCat.ofHom h) ≫ T'.fromSpecResidueField t') ⟶ f.fiber (g t'))
      (e : pullback (pullback.snd f g)
        (Spec.map (CommRingCat.ofHom h) ≫ T'.fromSpecResidueField t') ≅
        pullback (f.fiberToSpecResidueField (g t'))
          (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField (g t')) H)))),
      e.hom ≫ pullback.fst _ _ = p ∧
      p ≫ f.fiberι (g t') = pullback.fst _ _ ≫ pullback.fst f g ∧
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      (∀ i, IsOpenImmersion (pullback.fst p (ι i))) ∧
      (∀ z, ∃ (i : I) (w : ↥(pullback (C := Scheme.{u}) p (ι i))),
        pullback.fst p (ι i) w = z) ∧
      (∀ i, ∃ c : pullback p (ι i) ≅ Spec (.of (A i ⊗[T.residueField (g t')] H)),
        c.inv ≫ pullback.snd p (ι i) =
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ∧
        c.inv ≫ pullback.fst p (ι i) ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := T.residueField (g t')) (A := A i) (B := H)).toRingHom)) ∧
      (IsReduced (pullback (pullback.snd f g)
        (Spec.map (CommRingCat.ofHom h) ≫ T'.fromSpecResidueField t')) ↔
        ∀ i, _root_.IsReduced (A i ⊗[T.residueField (g t')] H)) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField (g t')) H))
  let d := Spec.map (CommRingCat.ofHom h) ≫ T'.fromSpecResidueField t'
  let q := pullback.snd (pullback.snd f g) d
  let x := pullback.fst (pullback.snd f g) d ≫ pullback.fst f g
  have hd : d ≫ g = b ≫ T.fromSpecResidueField (g t') := by
    dsimp only [d, b]
    rw [hH, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp]
    simp only [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hx : x ≫ f = (q ≫ b) ≫ T.fromSpecResidueField (g t') := by
    dsimp only [x, q]
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
    simp only [Category.assoc, hd]
  let p : pullback (pullback.snd f g) d ⟶ f.fiber (g t') :=
    pullback.lift x (q ≫ b) hx
  have hp : p ≫ f.fiberι (g t') = x := pullback.lift_fst _ _ _
  have hq : p ≫ f.fiberToSpecResidueField (g t') = q ≫ b :=
    pullback.lift_snd _ _ _
  have houter : IsPullback x q f (b ≫ T.fromSpecResidueField (g t')) := by
    rw [← hd]
    exact (IsPullback.of_hasPullback (pullback.snd f g) d).paste_horiz
      (IsPullback.of_hasPullback f g)
  have hs : IsPullback p q (f.fiberToSpecResidueField (g t')) b := by
    apply IsPullback.of_right (h₁₂ := f.fiberι (g t'))
      (h₂₂ := T.fromSpecResidueField (g t'))
    · rw [hp]
      exact houter
    · exact hq
    · exact IsPullback.of_hasPullback f (T.fromSpecResidueField (g t'))
  have hopen (i : I) : IsOpenImmersion (pullback.fst p (ι i)) := inferInstance
  have hcov : ∀ z, ∃ (i : I) (w : ↥(pullback (C := Scheme.{u}) p (ι i))),
      pullback.fst p (ι i) w = z := by
    intro z
    obtain ⟨i, a, ha⟩ := hcover (p z)
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback z a ha.symm
    exact ⟨i, w, hw⟩
  have charts (i : I) :
      ∃ c : pullback p (ι i) ≅ Spec (.of (A i ⊗[T.residueField (g t')] H)),
        c.inv ≫ pullback.snd p (ι i) =
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ∧
        c.inv ≫ pullback.fst p (ι i) ≫ q =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := T.residueField (g t')) (A := A i) (B := H)).toRingHom) := by
    have hi := (IsPullback.of_hasPullback p (ι i)).flip.paste_vert hs
    rw [hι i] at hi
    refine ⟨hi.isoPullback ≪≫ pullbackSpecIso (T.residueField (g t')) (A i) H, ?_, ?_⟩
    · simp only [Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst]
      exact pullbackSpecIso_inv_fst (T.residueField (g t')) (A i) H
    · simp only [Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd]
      exact pullbackSpecIso_inv_snd (T.residueField (g t')) (A i) H
  refine ⟨p, hs.isoPullback, hs.isoPullback_hom_fst, hp,
    hs.isoPullback_hom_snd, hopen, hcov, charts, ?_⟩
  let C : (pullback (pullback.snd f g) d).OpenCover :=
    Scheme.Cover.mkOfCovers I (fun i ↦ pullback p (ι i))
      (fun i ↦ pullback.fst p (ι i)) hcov
  rw [IsReduced.iff_of_openCover _ C]
  apply forall_congr'
  intro i
  obtain ⟨c, _, _⟩ := charts i
  change IsReduced (pullback p (ι i)) ↔ _root_.IsReduced _
  rw [← affine_isReduced_iff (.of (A i ⊗[T.residueField (g t')] H))]
  exact ⟨fun _ ↦ isReduced_of_isOpenImmersion c.inv,
    fun _ ↦ isReduced_of_isOpenImmersion c.hom⟩

end AlgebraicGeometry
