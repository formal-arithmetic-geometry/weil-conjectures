/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Defs.Filter
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineImageSelection
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Finite affine refinements of specified algebraic-space atlases

Source: Stacks Project, Properties of Spaces, Tags 03E4 (lemma-quasi-compact-space)
and 03H6 (lemma-quasi-compact-affine-cover)
(blueprint: lem-trf-space-qc-finite-affine-atlas-refinement).

The coproduct is specified by its universal property in schemes. The maps from its
summands and its map to the given atlas are over the original base. Their commuting
triangles specify the induced atlas map, without choosing another unrelated covering.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

private theorem isEtale_yoneda_map {S : Scheme.{u}} {U V : Over S}
    (r : U ⟶ V) (hr : Etale r.left) : IsEtale (yoneda.map r) := by
  intro T a
  let b : T ⟶ V := yoneda.preimage a
  refine ⟨Limits.pullback r b, Limits.pullback.snd r b,
    yoneda.map (Limits.pullback.fst r b), ?_, ?_⟩
  · rw [← yoneda.map_preimage a]
    exact (IsPullback.of_hasPullback r b).map yoneda
  · exact MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback r b).map (Over.forget S)) hr

private theorem surjective_of_jointlySurjective {S : Scheme.{u}}
    (X : AlgebraicSpace S) {I : Type} {V : I → Over S} {U : Over S}
    (r : ∀ i, V i ⟶ U) (f : yoneda.obj U ⟶ X.obj.obj)
    (h : IsJointlySurjective (fun i ↦ yoneda.map (r i) ≫ f)) : IsSurjective f := by
  intro T t
  obtain ⟨P, p, q, hpq, _, hsur⟩ := exists_scheme_fibreProduct_point X T U t f
  refine ⟨P, p, yoneda.map q, hpq.flip, hsur ?_⟩
  intro x
  let a : Over.mk (T.left.fromSpecResidueField x ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField x) rfl
  obtain ⟨i, L, hL, e, y, hy⟩ := h (T.left.residueField x)
    (T.left.fromSpecResidueField x ≫ T.hom) (t.app _ a)
  let k : Over.mk (Spec.map (CommRingCat.ofHom e) ≫
      (T.left.fromSpecResidueField x ≫ T.hom)) ⟶
      Over.mk (T.left.fromSpecResidueField x ≫ T.hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
  let b : Over.mk (Spec.map (CommRingCat.ofHom e) ≫
      (T.left.fromSpecResidueField x ≫ T.hom)) ⟶ U := y ≫ r i
  let z : Spec (CommRingCat.of L) := IsLocalRing.closedPoint L
  refine ⟨b.left z, L, hL, _, k ≫ a, b, z, ?_, rfl, ?_⟩
  · simp only [Over.comp_left, Scheme.Hom.comp_apply, a]
    exact T.left.fromSpecResidueField_apply x _
  · exact (t.naturality_apply k.op a).trans hy.symm

/-- Every specified scheme atlas of a quasi-compact algebraic space has a finite affine
open refinement whose scheme coproduct is an affine surjective etale atlas. Its spectrum
formula holds for any affine presentations of the summands, including the empty product.
If the atlas is empty (equivalently its target is empty), the selected family is empty
and its coproduct is the spectrum of the zero ring `PUnit`.
Source: Stacks Project, Tags 03E4 and 03H6
(blueprint: lem-trf-space-qc-finite-affine-atlas-refinement).

Proof:
1. Take the quasi-compact scheme atlas Q supplied by the hypothesis. Its map on points
   is continuous and surjective by lem-a1-space-point-open-calculus, with the topology of
   def-a1-space-point-topology. The continuous-image compactness lemma
   lem-weil-pbc-continuous-image-quasi-compact shows that the target point space is compact.
2. Cover the specified atlas W by affine opens. Base change each open inclusion by a
   scheme test of W -> X; lem-weil-pbc-open-immersion-base-change and clauses (1)-(2) of
   lem-weil-pbc-etale-composition-cancellation make its composite representable etale.
   Its point image is open by lem-a1-space-point-open-calculus. These images cover X,
   so compactness selects a finite family, jointly surjective in the sense of
   def-trf-algebraic-space-jointly-surjective-family. No compactness of W is used.
3. Form their scheme coproduct U by lem-weil-pbc-scheme-coproduct-family and the induced
   map a : U -> W. For a scheme test T -> X, represent U times_X T by
   U times_W (W times_X T), using def-pc-fibre-product and pullback pasting. It is covered
   by the pullbacks of the selected summands. Their projections to T are etale by the
   open-immersion base-change and etale-composition lemmas; apply
   lem-weil-pbc-etale-local-on-source to conclude that the projection from U times_X T
   is etale. This proves representability and etaleness of the induced map to X.
4. The point image of U contains those of all selected summands, hence is all of X.
   The representable-map criterion in lem-a1-space-point-open-calculus gives surjectivity
   on every scheme test. The finite-affine-coproduct-spectrum lemma identifies U with
   the spectrum of the product of any coordinate rings of its summands, so U is affine.
5. For empty X its scheme atlas W is empty, and take n = 0. The empty coproduct is
   initial, hence is Spec of the zero ring, also given by the empty product formula.
   The same scheme tests apply. The construction uses neither separatedness nor
   quasi-compactness of the specified atlas. -/
theorem exists_finite_affine_atlas_refinement {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : ∃ (Q : Over S) (q : yoneda.obj Q ⟶ X.obj.obj),
      CompactSpace Q.left ∧ IsEtale q ∧ IsSurjective q)
    (W : Over S) (w : yoneda.obj W ⟶ X.obj.obj)
    (hw : IsEtale w) (hs : IsSurjective w) :
    ∃ (n : ℕ) (V : Fin n → W.left.Opens) (U : Over S)
      (j : ∀ i : Fin n, Over.mk ((V i).ι ≫ W.hom) ⟶ U) (a : U ⟶ W),
      (∀ i : Fin n, IsAffineOpen (V i)) ∧
      Nonempty (IsColimit (Cofan.mk U.left (fun i : Fin n ↦ (j i).left))) ∧
      (∀ i : Fin n, j i ≫ a = Over.homMk (V := W) (V i).ι rfl) ∧
      IsJointlySurjective (fun i : Fin n ↦ yoneda.map (j i ≫ a) ≫ w) ∧
      IsEtale (yoneda.map a ≫ w) ∧ IsSurjective (yoneda.map a ≫ w) ∧
      IsAffine U.left ∧
      (∀ (A : Fin n → CommRingCat.{u}),
        (∀ i : Fin n, Nonempty ((V i).toScheme ≅ Spec (A i))) →
          Nonempty (U.left ≅ Spec (.of (∀ i : Fin n, A i)))) ∧
      (IsEmpty W.left → n = 0) ∧
      (n = 0 → Nonempty (U.left ≅ Spec (.of PUnit.{u + 1}))) := by
  classical
  obtain ⟨n, V, hV, hcover, hempty⟩ :=
    exists_finite_affine_image_selection X hqc W w hw hs
  let F : Fin n → Scheme.{u} := fun i ↦ (V i).toScheme
  let d : (∐ F) ⟶ W.left := Sigma.desc (fun i ↦ (V i).ι)
  let U : Over S := Over.mk (d ≫ W.hom)
  let a : U ⟶ W := Over.homMk d rfl
  let j : ∀ i : Fin n, Over.mk ((V i).ι ≫ W.hom) ⟶ U :=
    fun i ↦ Over.homMk (Sigma.ι F i) (by simp [U, d])
  have hj : ∀ i : Fin n, j i ≫ a = Over.homMk (V := W) (V i).ι rfl := by
    intro i
    apply Over.OverMorphism.ext
    exact Sigma.ι_desc _ i
  have hc : IsJointlySurjective (fun i : Fin n ↦ yoneda.map (j i ≫ a) ≫ w) := by
    simpa only [hj] using hcover
  have hd : Etale d := IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
    (fun i ↦ inferInstance)
  have he : IsEtale (yoneda.map a ≫ w) :=
    isEtale_comp _ _ (isEtale_yoneda_map a hd) hw
  have hsur : IsSurjective (yoneda.map a ≫ w) :=
    surjective_of_jointlySurjective X j _ (by
      simpa only [Functor.map_comp, Category.assoc] using hc)
  have hF (i : Fin n) : IsAffine (F i) := hV i
  let := hF
  refine ⟨n, V, U, j, a, hV, ?_, hj, hc, he, hsur, ?_, ?_, hempty, ?_⟩
  · exact ⟨coproductIsCoproduct F⟩
  · change IsAffine (∐ F)
    infer_instance
  · intro A hA
    let e : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
    let R : ULift.{u} (Fin n) → CommRingCat.{u} := fun i ↦ A i.down
    let eR := (RingEquiv.piCongrLeft (fun i ↦ A i) e).toCommRingCatIso
    exact ⟨Sigma.mapIso (fun i ↦ (hA i).some) ≪≫
      (Sigma.reindex e (fun i ↦ Spec (A i))).symm ≪≫
      asIso (sigmaSpec R) ≪≫ Scheme.Spec.mapIso eR.symm.op⟩
  · intro hn
    subst n
    let c := Cofan.mk (∐ F) (Sigma.ι F)
    have hc : IsColimit c := coproductIsCoproduct F
    exact ⟨((isColimitEquivIsInitialOfIsEmpty Scheme.{u} c) hc).uniqueUpToIso
      specPUnitIsInitial⟩

/-- In particular a quasi-compact algebraic space admits one affine scheme atlas.
Source: Stacks Project, Tag 03H6 (lemma-quasi-compact-affine-cover)
(blueprint: lem-trf-space-qc-finite-affine-atlas-refinement).

Proof: choose the quasi-compact scheme atlas in the hypothesis and apply the specified
atlas refinement above (steps 1-5 of the node). The resulting finite coproduct is affine
and its induced map is representable, etale and surjective. The empty case gives Spec 0.
No separatedness assumption is needed. -/
theorem exists_affine_atlas_of_quasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqc : ∃ (Q : Over S) (q : yoneda.obj Q ⟶ X.obj.obj),
      CompactSpace Q.left ∧ IsEtale q ∧ IsSurjective q) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj),
      IsAffine U.left ∧ IsEtale p ∧ IsSurjective p := by
  have hqc' := hqc
  obtain ⟨Q, q, _, hq, hs⟩ := hqc'
  obtain ⟨n, V, U, j, a, _, _, _, _, he, hsur, haff, _⟩ :=
    exists_finite_affine_atlas_refinement X hqc Q q hq hs
  exact ⟨U, yoneda.map a ≫ q, haff, he, hsur⟩

end AlgebraicGeometry.AlgebraicSpace
