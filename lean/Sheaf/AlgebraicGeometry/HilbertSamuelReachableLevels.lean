/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelLocalPresentations
public import Mathlib.Logic.Relation

import Sheaf.AlgebraicGeometry.JetLevelTopologyReachableDcc

/-! # Descending chains of reachable Hilbert--Samuel levels

Source: ILO VIII 2.3.11--2.3.13, pp. 93--94; BMT arXiv:0905.3580, section 6.1;
BM 1997, Corollary 3.20 and Lemma 9.3
(blueprint: lem-trf-hilbert-samuel-local-presentations).

The public import retains every previously recorded numerical and presentation declaration.
The additional theorem states the descending-chain condition for all levels reached after
finite admissible histories, including subsequences separated by stages with unchanged value.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

private abbrev rawPair (S : Embedded (ULift.{u} ℚ)) : JetLevelPair.{u} :=
  ⟨S.X, S.Z, S.p, S.i⟩

private theorem rawPair_transition {S T : Embedded (ULift.{u} ℚ)}
    (h : BlowupTransition S T) : JetLevelBlowup (rawPair S) (rawPair T) := by
  obtain ⟨C, ⟨hsmooth, c, hc, hconstant⟩, e, q, hp, hi⟩ := h
  let := S.closed
  have : IsClosedImmersion (c ≫ S.i) := hc.symm ▸ inferInstance
  have : IsClosedImmersion c := IsClosedImmersion.of_comp_isClosedImmersion c S.i
  exact ⟨C, c, inferInstance, hc, hsmooth, hconstant, e, q, hp, hi⟩

private theorem rational_ringHom_ext {A : Type u} [CommRing A]
    (f g : ULift.{u} ℚ →+* A) : f = g := by
  have h : f.comp ULift.ringEquiv.symm.toRingHom =
      g.comp ULift.ringEquiv.symm.toRingHom := Subsingleton.elim _ _
  ext x
  exact DFunLike.congr_fun h x.down

private theorem rational_morphism_ext {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of (ULift.{u} ℚ))) : f = g := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact rational_ringHom_ext _ _

private theorem ambient_chart (S : Embedded (ULift.{u} ℚ)) (x : S.Z) :
    ∃ (V : S.Z.Opens) (n : ℕ)
      (c : V.toScheme ⟶ Spec (.of (MvPolynomial (Fin n) (ULift.{u} ℚ)))),
      IsAffineOpen V ∧ x ∈ V ∧ Etale c ∧ c ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℚ)
          (MvPolynomial (Fin n) (ULift.{u} ℚ)))) = V.ι ≫ S.p := by
  let := S.smooth
  obtain ⟨U, hU, V, hV, hx, hVU, H⟩ := Smooth.exists_isStandardSmooth S.p x
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (S.p x) z ▸ hVU hx
  obtain ⟨n, φ, _, hφ⟩ := H.exists_etale_mvPolynomial
  let e : MvPolynomial (Fin n) (ULift.{u} ℚ) ≃+*
      MvPolynomial (Fin n) Γ(Spec (.of (ULift.{u} ℚ)), ⊤) :=
    MvPolynomial.mapEquiv _ (Scheme.ΓSpecIso (.of (ULift.{u} ℚ))).symm.commRingCatIsoToRingEquiv
  let ψ := φ.comp e.toRingHom
  have hψ : ψ.Etale := RingHom.Etale.respectsIso.2 _ _ hφ
  let : IsAffine V.toScheme := hV
  let c := V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have : Etale (Spec.map (CommRingCat.ofHom ψ)) := HasRingHomProperty.Spec_iff.mpr hψ
  have : IsIso V.toSpecΓ := by
    unfold Scheme.Opens.toSpecΓ
    infer_instance
  exact ⟨V, n, c, hV, hx, inferInstance, rational_morphism_ext _ _⟩

/-- No infinite strict chain among levels reached from one fixed initial embedded scheme.
The reflexive transitive closure includes zero blowups, arbitrary finite histories, and
subsequences of one infinite history. It does not require a drop at every intervening blowup.
Source: BMT 6.1; BM 1997, Corollary 3.20 and Lemma 9.3; node proof steps 3 and 9
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: Cover the initial finite-type scheme by finitely many smooth ambient charts. The
jet-diagram control theorem `lem-trf-jet-diagram-hilbert-control` gives the descending-chain
condition on diagram values in a fixed number of ambient variables. Smooth-center blowups
preserve the dimension of the ambient charts, so the same finite bound applies after any
finite admissible history, not only to the initial finite image. The smooth blowup geometry
of `lem-trf-smooth-center-blowup-geometry` keeps the ambient smooth and the strict transform
reduced at every stage. Thus every reached level lies in that same descending-chain family.
If different initial charts occur, an infinite subsequence belongs to one of the finitely
many charts. An infinite strict chain of reached levels contradicts its diagram bound. -/
theorem function_no_infinite_reachable_drops (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (values : ℕ → ℕ → ℕ)
    (hvalues : ∀ n : ℕ, ∃ T : Embedded (ULift.{u} ℚ),
      Relation.ReflTransGen BlowupTransition S T ∧
        ∃ x : T.X, function (T.i ≫ T.p) x = values n) :
    ¬ ∀ n : ℕ, lt (values (n + 1)) (values n) := by
  classical
  let := S.smooth
  let := S.closed
  let : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace (S.i ≫ S.p)
  choose V e c haff hmem het hbase using fun x : S.X ↦ ambient_chart S (S.i x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : S.X ↦ S.i ⁻¹' (V x : Set S.Z))
    (fun x ↦ (V x).isOpen.preimage S.i.continuous)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  let idx : Fin t.card → S.X := fun j ↦ (t.equivFin.symm j).val
  have hcover : ∀ x : S.X, ∃ j : Fin t.card, S.i x ∈ V (idx j) := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [idx] using hxy⟩
  have hbound : ∀ j : Fin t.card, e (idx j) ≤ t.sup e := by
    intro j
    exact Finset.le_sup (t.equivFin.symm j).property
  have hraw : ∀ n : ℕ, ∃ T : JetLevelPair.{u}, JetLevelReachable (rawPair S) T ∧
      ∃ x : T.X, function (T.i ≫ T.p) x = values n := by
    intro n
    obtain ⟨T, hT, x, hx⟩ := hvalues n
    refine ⟨rawPair T, ?_, x, hx⟩
    exact Relation.ReflTransGen.lift rawPair (fun _ _ h ↦ rawPair_transition h) _ _ hT
  exact (jet_level_reachable_diagrams_dcc (rawPair S) (t.sup e) t.card
    (fun j ↦ V (idx j)) (fun j ↦ e (idx j)) (fun j ↦ c (idx j))
    (fun j ↦ haff (idx j)) (fun j ↦ het (idx j)) (fun j ↦ hbase (idx j))
    hcover hbound).2 values hraw

end AlgebraicGeometry.HilbertSamuel
