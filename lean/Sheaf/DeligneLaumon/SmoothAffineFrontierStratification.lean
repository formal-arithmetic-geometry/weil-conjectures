/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.DeligneLaumon.SmoothAffineFiltrationFiniteFieldDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Topology.Connected.Clopen
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Smooth affine frontier stratification over a finite subfield

Source: Stacks Project, Tags 0B8X, 06LH and 01ZM; `thm-zl-real-mixed-by-curves`
(blueprint: lem-zl-smooth-affine-frontier-stratification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduced_factors_immersion {X Y Z : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) (i : Z ⟶ X) [IsImmersion i]
    (h : Set.range f ⊆ Set.range i) : ∃ g : Y ⟶ Z, g ≫ i = f := by
  let f' : Y ⟶ i.coborderRange.toScheme :=
    IsOpenImmersion.lift i.coborderRange.ι f (h.trans (by simpa using! subset_coborder))
  have hf' : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  have h' : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := h (Set.mem_range_self y)
    refine ⟨z, ?_⟩
    apply i.coborderRange.ι.isOpenEmbedding.injective
    change (i.liftCoborder ≫ i.coborderRange.ι) z = (f' ≫ i.coborderRange.ι) y
    rw [i.liftCoborder_ι, hf']
    exact hz
  obtain ⟨g, hg, -⟩ :=
    IsClosedImmersion.existsUnique_fac_of_range_subset_range i.liftCoborder f' h'
  refine ⟨g, ?_⟩
  rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closed_intoAmbient {S : Scheme.{u}} {Y : Over S} {n : ℕ}
    (H : SmoothAffineFiltration Y n) (a : Fin (n + 1)) :
    IsClosedImmersion (H.intoAmbient a).left := by
  induction a using Fin.induction with
  | zero => rw [H.intoAmbient_zero]; infer_instance
  | succ a ih =>
    rw [H.intoAmbient_succ, Over.comp_left]
    have := H.closed_inclusion a
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_point_of_geometricallyConnected
    {k : Type u} [Field k] (V : Over (Spec (.of k)))
    [IsSeparated V.hom] [Etale V.hom] [GeometricallyConnected V.hom] :
    Nonempty (V ≅ Over.mk (𝟙 _)) := by
  have : ConnectedSpace V.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton V.hom
  have : ConnectedSpace ↥(pullback V.hom V.hom) := inferInstance
  have hr : Set.range (pullback.diagonal V.hom) = Set.univ :=
    IsClopen.eq_univ
      ⟨(pullback.diagonal V.hom).isClosedEmbedding.isClosed_range,
        (pullback.diagonal V.hom).isOpenEmbedding.isOpen_range⟩
      (Set.range_nonempty _)
  have : Surjective (pullback.diagonal V.hom) := ⟨Set.range_eq_univ.mp hr⟩
  have : IsIso (pullback.diagonal V.hom) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : Mono V.hom := (pullback.isIso_diagonal_iff _).mp this
  have : IsOpenImmersion V.hom := IsOpenImmersion.of_flat_of_mono _
  have : IsIso V.hom := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, inferInstance⟩
  exact ⟨Over.isoMk (asIso V.hom) (by rfl)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- A finite frontier refinement by smooth affine geometrically connected pieces, together
with one finite-field model for all objects and maps.

Source: Stacks Project, Tags 0B8X, 06LH and 01ZM; `thm-zl-real-mixed-by-curves`,
proof paragraphs 6--7 (blueprint: lem-zl-smooth-affine-frontier-stratification).

Proof: If the geometric fibre is empty, use the length-zero chain. Otherwise apply the
Noetherian frontier refinement and choose, on each irreducible component, a nonempty affine
open in the smooth locus. Noetherian induction gives the closed chain and its finite
disjoint open-and-closed pieces. The pieces have constant smooth relative dimension and
are geometrically connected. Finite presentation spreads the whole finite diagram,
including the maps and the containment in the prescribed strata, to one finite subfield;
enlarging that field makes every descended affine piece geometrically connected. The
zero-dimensional case is a finite smooth geometrically connected scheme over the finite
field and hence is `Spec` of that field. The empty case and all inclusions are included.
-/
theorem smooth_affine_frontier_stratification
    (D : FiniteFieldDatum.{u})
    (X₀ : Scheme.{u})
    (a₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀))
    [IsSeparated a₀] [LocallyOfFiniteType (Over.mk a₀).hom] [QuasiCompact (Over.mk a₀).hom]
    (T : Scheme.FiniteLocallyClosedStratification
      (D.geometricFiber (Over.mk a₀)).left.nilradical.subscheme)
    (hTred : ∀ i : Fin T.n, IsReduced (T.domain i)) :
    ∃ (m : ℕ) (hm : 1 ≤ m),
      let km := D.extensionSubfield m hm
      let Sm := Spec (CommRingCat.of km)
      let Xm := (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)
      let X := D.geometricFiber (Over.mk a₀)
      let Sbase := Spec (CommRingCat.of D.k)
      let BC : Over Sm ⥤ Over Sbase := Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))
      ∃ (χ : BC.obj Xm ≅ X),
        ∃ (t : ℕ) (Z : Fin (t + 1) → Over Sm),
          (∀ a : Fin (t + 1), IsReduced (Z a).left) ∧
          ∃ (hZ0 : Z 0 = Over.mk (Xm.left.nilradical.subschemeι ≫ Xm.hom))
            (hZt : Z (Fin.last t) = Over.mk (Scheme.emptyTo Sm))
            (ι : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc)
            (z : ∀ a : Fin (t + 1), Z a ⟶ Xm),
            (∀ a : Fin t, IsClosedImmersion (ι a).left) ∧
            (z 0 = eqToHom hZ0 ≫ Over.homMk Xm.left.nilradical.subschemeι (by simp)) ∧
            (∀ a : Fin t, z a.succ = ι a ≫ z a.castSucc) ∧
            ∃ (U : Fin t → Over Sm) (u : ∀ a : Fin t, U a ⟶ Z a.castSucc),
              (∀ a : Fin t, IsOpenImmersion (u a).left) ∧
              (∀ a : Fin t, Set.range (u a).left = (Set.range (ι a).left)ᶜ) ∧
              ∃ (r : Fin t → ℕ) (V : ∀ a : Fin t, Fin (r a) → Over Sm)
                (d : ∀ a : Fin t, Fin (r a) → ℕ)
                (v : ∀ (a : Fin t) (b : Fin (r a)), V a b ⟶ U a),
                (∀ (a : Fin t) (b : Fin (r a)), Nonempty (V a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), IsReduced (V a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), IsAffine (V a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), GeometricallyConnected (V a b).hom) ∧
                (∀ (a : Fin t) (b : Fin (r a)), SmoothOfRelativeDimension (d a b) (V a b).hom) ∧
                (∀ (a : Fin t) (b : Fin (r a)),
                  IsOpenImmersion (v a b).left ∧ IsClosedImmersion (v a b).left) ∧
                (∀ (a : Fin t) (b : Fin (r a)), d a b = 0 → Nonempty (V a b ≅ Over.mk (𝟙 Sm))) ∧
                (∀ (a : Fin t), ⋃ b : Fin (r a), Set.range (v a b).left =
                  Set.univ) ∧
                (∀ (a : Fin t) (b₁ b₂ : Fin (r a)), b₁ ≠ b₂ →
                  Disjoint (Set.range (v a b₁).left) (Set.range (v a b₂).left)) ∧
                (∀ (a : Fin t) (b : Fin (r a)),
                  ∃ (ν : Fin T.n) (j : (BC.obj (V a b)).left ⟶ T.domain ν),
                  IsImmersion j ∧
                  j ≫ T.immersion ν ≫
                      (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι =
                    (BC.map (v a b ≫ u a ≫ z a.castSucc) ≫ χ.hom).left)
      := by
  classical
  have : LocallyOfFiniteType a₀ := inferInstanceAs
    (LocallyOfFiniteType (Over.mk a₀).hom)
  have : QuasiCompact a₀ := inferInstanceAs (QuasiCompact (Over.mk a₀).hom)
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let X := D.geometricFiber (Over.mk a₀)
  let Y : Over (Spec (.of D.k)) := Over.mk (X.left.nilradical.subschemeι ≫ X.hom)
  have : LocallyOfFiniteType X.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd a₀
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact X.hom := inferInstanceAs
    (QuasiCompact (pullback.snd a₀
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (X.left.nilradical.subschemeι ≫ X.hom))
  have : QuasiCompact Y.hom := inferInstanceAs
    (QuasiCompact (X.left.nilradical.subschemeι ≫ X.hom))
  have : IsReduced Y.left := inferInstanceAs (IsReduced X.left.nilradical.subscheme)
  obtain ⟨n, H, hH⟩ := exists_smooth_affine_geometric_filtration Y T.stratum
    T.isLocallyClosed_stratum T.iUnion_stratum_eq_univ
  obtain ⟨m, hm, χ, M, hfinal, hM⟩ :=
    exists_smooth_affine_filtration_finite_field_model D X₀ a₀ n H
  let km := D.extensionSubfield m hm
  let Sm := Spec (.of km)
  let Xm := (Over.pullback
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)
  let BC := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))
  by_cases hn : n = 0
  · subst n
    let R : Over Sm := Over.mk (Xm.left.nilradical.subschemeι ≫ Xm.hom)
    let E : Over Sm := Over.mk (Scheme.emptyTo Sm)
    have hR : IsEmpty R.left := by
      have h : IsEmpty (M.closed 0).left := M.finish
      have hs : M.closed 0 = R := M.start
      exact hs ▸ h
    have : IsEmpty R.left := hR
    have : IsEmpty E.left := inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
    have : IsReduced R.left := inferInstanceAs (IsReduced Xm.left.nilradical.subscheme)
    have : IsReduced E.left := by
      have (x : E.left) : _root_.IsReduced (E.left.presheaf.stalk x) := isEmptyElim x
      exact isReduced_of_isReduced_stalk _
    let i : E ⟶ R := Over.homMk (Scheme.emptyTo R.left) (by
      change (Scheme.emptyTo R.left) ≫ R.hom = Scheme.emptyTo Sm
      exact Subsingleton.elim _ _)
    let j : R ⟶ Xm := Over.homMk Xm.left.nilradical.subschemeι (by rfl)
    let z : ∀ a : Fin 2, (Fin.cons R (fun _ : Fin 1 ↦ E)) a ⟶ Xm :=
      Fin.cases j (fun _ ↦ i ≫ j)
    refine ⟨m, hm, χ, 1, Fin.cons R (fun _ : Fin 1 ↦ E),
      (Fin.cases (inferInstance : IsReduced R.left)
        (fun _ ↦ inferInstanceAs (IsReduced E.left))) , rfl, rfl,
      (fun a ↦ by have ha : a = 0 := Subsingleton.elim _ _; subst a; exact i),
      z, ?_, ?_, ?_, (fun _ ↦ E),
      (fun a ↦ by have ha : a = 0 := Subsingleton.elim _ _; subst a; exact i), ?_, ?_,
      (fun _ ↦ 0), (fun _ ↦ Fin.elim0), (fun _ ↦ Fin.elim0),
      (fun _ b ↦ b.elim0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      fin_cases a
      change IsClosedImmersion (Scheme.emptyTo R.left)
      infer_instance
    · rfl
    · intro a
      fin_cases a
      rfl
    · intro a
      fin_cases a
      change IsOpenImmersion (Scheme.emptyTo R.left)
      infer_instance
    · intro a
      fin_cases a
      apply Set.ext
      intro x
      change R.left at x
      exact isEmptyElim x
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
    · intro a
      apply Set.ext
      intro x
      exact isEmptyElim x
    · intro a b; exact b.elim0
    · intro a b; exact b.elim0
  · refine ⟨m, hm, χ, n, M.closed, M.reduced, M.start, hfinal hn,
      M.inclusion, (fun a ↦ M.intoAmbient a ≫
        Over.homMk Xm.left.nilradical.subschemeι (by rfl)), M.closed_inclusion,
      ?_, ?_, M.piece, M.pieceInclusion, M.open_piece, M.range_piece,
      (fun _ ↦ 1), (fun a _ ↦ M.piece a), (fun a _ ↦ M.dimension a),
      (fun a _ ↦ 𝟙 (M.piece a)), (fun a _ ↦ M.nonempty_piece a), (fun a _ ↦ M.reduced_piece a),
      (fun a _ ↦ M.affine_piece a), (fun a _ ↦ M.connected_piece a),
      (fun a _ ↦ M.smooth_piece a), ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      rw [M.intoAmbient_zero]
    · intro a
      dsimp only
      rw [M.intoAmbient_succ, Category.assoc]
    · intro a b
      constructor
      · exact inferInstanceAs (IsOpenImmersion (𝟙 (M.piece a).left))
      · exact inferInstanceAs (IsClosedImmersion (𝟙 (M.piece a).left))
    · intro a b hd
      have := M.affine_piece a
      have : IsSeparated (M.piece a).hom := inferInstance
      have := M.connected_piece a
      have : Etale (M.piece a).hom :=
        (Etale.iff_smoothOfRelativeDimension_zero _).mpr (hd ▸ M.smooth_piece a)
      exact etale_point_of_geometricallyConnected (M.piece a)
    · intro a
      ext x
      constructor
      · intro _; trivial
      · intro _
        exact Set.mem_iUnion.mpr ⟨0, ⟨x, rfl⟩⟩
    · intro a b₁ b₂ hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro a b
      obtain ⟨ν, hν⟩ := hH a
      obtain ⟨hdim, e, he⟩ := hM a
      have := H.reduced_piece a
      have := H.open_piece a
      have := closed_intoAmbient H a.castSucc
      have := T.isImmersion ν
      obtain ⟨j, hj⟩ := reduced_factors_immersion
        (H.pieceInclusion a ≫ H.intoAmbient a.castSucc).left (T.immersion ν)
        (by
          change Set.range (H.pieceInclusion a ≫ H.intoAmbient a.castSucc).left ⊆
            Set.range (T.immersion ν)
          exact hν.trans (T.range_immersion ν).ge)
      have : IsImmersion (j ≫ T.immersion ν) := by
        rw [hj, Over.comp_left]
        infer_instance
      have : IsImmersion j := IsImmersion.of_comp j (T.immersion ν)
      refine ⟨ν, e.hom.left ≫ j, inferInstance, ?_⟩
      simp only [Category.assoc, ← Category.assoc j (T.immersion ν), hj]
      simpa only [Category.id_comp, Category.assoc] using he.symm

end WeilConjectures
