/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.DeligneLaumon.SmoothAffineFiltrationFiniteFieldDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Topology.Connected.Clopen
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Smooth affine frontier stratifications over a common finite subfield

Source: Stacks Project, Tags 0B8X, 06LH, 01ZM; blueprint
`thm-zl-real-mixed-by-curves`, proof paragraphs 6--7
(blueprint: lem-zl-smooth-affine-frontier-stratification).

All chain maps and component maps are morphisms over the same finite subfield.
The two projection equations in the last clause express containment under the canonical
iterated base-change identification, without choosing an ambient automorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

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

private theorem closed_intoAmbient {S : Scheme.{u}} {Y : Over S} {n : ℕ}
    (H : SmoothAffineFiltration Y n) (a : Fin (n + 1)) :
    IsClosedImmersion (H.intoAmbient a).left := by
  induction a using Fin.induction with
  | zero => rw [H.intoAmbient_zero]; infer_instance
  | succ a ih =>
    rw [H.intoAmbient_succ, Over.comp_left]
    have := H.closed_inclusion a
    infer_instance

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

/-- A finite reduced closed filtration refining any finite locally closed reduced
partition after one common finite constant extension. The terminal scheme is empty;
when the original scheme is empty the filtration has length zero.
Source: Stacks Project, varieties.tex, Tags 0B8X and 06LH; limits.tex, Tag 01ZM;
blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7
(blueprint: lem-zl-smooth-affine-frontier-stratification).

Proof:
1. Apply `lem-zl-smooth-affine-geometric-filtration` to the reduction of the geometric
   fibre and the given partition. Choose smooth affine opens inside its strata and
   remove their reduced closed complements by Noetherian induction.
2. Apply `lem-zl-smooth-affine-filtration-finite-field-descent` to descend the finite
   diagram, its dimensions and its geometric comparison maps to one finite subfield.
3. Choose exactly one component in each layer, its inclusion the identity; the cover
   and pairwise disjointness assertions are then immediate. In the empty case
   retain the empty reduction itself as the sole member of the zero-length chain;
   emptiness does not require equality with a separately chosen empty scheme.
4. For a zero-dimensional piece `V`, etaleness and separatedness make the diagonal
   clopen in `V ×_{k_m} V`. This product is connected by geometric connectedness and
   the diagonal is nonempty, so the diagonal is an isomorphism and `V → Spec k_m` is a
   monomorphism. It is flat, so the flat-monomorphism criterion makes it an open
   immersion; geometric connectedness makes it surjective, hence an isomorphism.
5. The geometric comparisons give image containment in a stratum. A map from a
   reduced scheme into the image of an immersion factors through it: lift first
   through its open coborder and then through its closed part by reducedness.
   The factor is an immersion because its composite is. Composing its ambient
   equality with the two fibre-product projections gives the displayed equations.
-/
theorem smooth_affine_frontier_stratification
    (D : FiniteFieldDatum.{u}) (X₀ : Scheme.{u})
    (a₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀))
    [IsSeparated a₀] [LocallyOfFiniteType (Over.mk a₀).hom]
    [QuasiCompact (Over.mk a₀).hom]
    (T : Scheme.FiniteLocallyClosedStratification
      (D.geometricFiber (Over.mk a₀)).left.nilradical.subscheme)
    (hTred : ∀ i : Fin T.n, IsReduced (T.domain i)) :
    ∃ (m : ℕ) (hm : 1 ≤ m) (t : ℕ)
      (Z : Fin (t + 1) → Over (Spec (CommRingCat.of (D.extensionSubfield m hm))))
      (z : ∀ a : Fin (t + 1), Z a ⟶ (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)),
      (IsEmpty X₀ → t = 0) ∧
      (∀ a : Fin (t + 1), IsReduced (Z a).left) ∧
      (∀ a : Fin (t + 1), IsClosedImmersion (z a).left) ∧
      IsEmpty (Z (Fin.last t)).left ∧
      (∃ e₀ : Z 0 ≅ Over.mk
        ((pullback a₀ (Spec.map (CommRingCat.ofHom
          (D.extensionEmbedding m hm)))).nilradical.subschemeι ≫
          pullback.snd a₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))),
        (z 0).left = e₀.hom.left ≫
          (pullback a₀ (Spec.map (CommRingCat.ofHom
            (D.extensionEmbedding m hm)))).nilradical.subschemeι) ∧
      ∃ (ι : ∀ a : Fin t, Z a.succ ⟶ Z a.castSucc),
        (∀ a : Fin t, IsClosedImmersion (ι a).left) ∧
        (∀ a : Fin t, z a.succ = ι a ≫ z a.castSucc) ∧
      ∃ (U : Fin t → Over (Spec (CommRingCat.of (D.extensionSubfield m hm))))
        (u : ∀ a : Fin t, U a ⟶ Z a.castSucc),
        (∀ a : Fin t, IsOpenImmersion (u a).left) ∧
        (∀ a : Fin t, Set.range (u a).left = (Set.range (ι a).left)ᶜ) ∧
      ∃ (r : Fin t → ℕ)
        (V : ∀ a : Fin t, Fin (r a) → Over
          (Spec (CommRingCat.of (D.extensionSubfield m hm))))
        (d : ∀ a : Fin t, Fin (r a) → ℕ)
        (v : ∀ (a : Fin t) (b : Fin (r a)), V a b ⟶ U a),
        (∀ (a : Fin t) (b : Fin (r a)), Nonempty (V a b).left) ∧
        (∀ (a : Fin t) (b : Fin (r a)), IsAffine (V a b).left) ∧
        (∀ (a : Fin t) (b : Fin (r a)), GeometricallyConnected (V a b).hom) ∧
        (∀ (a : Fin t) (b : Fin (r a)),
          SmoothOfRelativeDimension (d a b) (V a b).hom) ∧
        (∀ (a : Fin t) (b : Fin (r a)),
          IsOpenImmersion (v a b).left ∧ IsClosedImmersion (v a b).left) ∧
        (∀ (a : Fin t) (b : Fin (r a)), d a b = 0 →
          Nonempty (V a b ≅ Over.mk
            (𝟙 (Spec (CommRingCat.of (D.extensionSubfield m hm)))))) ∧
        (∀ a : Fin t, ⋃ b : Fin (r a), Set.range (v a b).left = Set.univ) ∧
        (∀ (a : Fin t) (b₁ b₂ : Fin (r a)), b₁ ≠ b₂ →
          Disjoint (Set.range (v a b₁).left) (Set.range (v a b₂).left)) ∧
        (∀ (a : Fin t) (b : Fin (r a)),
          ∃ (ν : Fin T.n)
            (j : ((Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (D.extensionSubfield m hm) D.k)))).obj (V a b)).left ⟶
                T.domain ν),
            IsImmersion j ∧
            j ≫ T.immersion ν ≫
                (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι ≫
                pullback.fst a₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
              pullback.fst (V a b).hom (Spec.map (CommRingCat.ofHom
                (algebraMap (D.extensionSubfield m hm) D.k))) ≫
                (v a b ≫ u a ≫ z a.castSucc).left ≫
                pullback.fst a₀ (Spec.map (CommRingCat.ofHom
                  (D.extensionEmbedding m hm))) ∧
            j ≫ T.immersion ν ≫
                (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι ≫
                (D.geometricFiber (Over.mk a₀)).hom =
              pullback.snd (V a b).hom (Spec.map (CommRingCat.ofHom
                (algebraMap (D.extensionSubfield m hm) D.k)))) := by
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
  obtain ⟨m, hm, χ, M, hχ, _hfinal, hM⟩ :=
    exists_smooth_affine_filtration_finite_field_model D X₀ a₀ n H
  let km := D.extensionSubfield m hm
  let Sm := Spec (.of km)
  let Xm := (Over.pullback
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj (Over.mk a₀)
  let BC := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap km D.k)))
  let z : ∀ a : Fin (n + 1), M.closed a ⟶ Xm := fun a ↦ M.intoAmbient a ≫
    Over.homMk Xm.left.nilradical.subschemeι rfl
  refine ⟨m, hm, n, M.closed, z, ?_, M.reduced, ?_, M.finish, ?_,
    M.inclusion, M.closed_inclusion, ?_, M.piece, M.pieceInclusion,
    M.open_piece, M.range_piece, (fun _ ↦ 1), (fun a _ ↦ M.piece a),
    (fun a _ ↦ M.dimension a), (fun a _ ↦ 𝟙 (M.piece a)),
    (fun a _ ↦ M.nonempty_piece a), (fun a _ ↦ M.affine_piece a),
    (fun a _ ↦ M.connected_piece a), (fun a _ ↦ M.smooth_piece a), ?_, ?_, ?_, ?_, ?_⟩
  · intro hX
    have : IsEmpty X₀ := hX
    cases n with
    | zero => rfl
    | succ n =>
      obtain ⟨x⟩ := H.nonempty_piece 0
      exact isEmptyElim (pullback.fst a₀
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
          (X.left.nilradical.subschemeι
            ((H.pieceInclusion 0 ≫ H.intoAmbient 0).left x)))
  · intro a
    have : IsClosedImmersion (M.intoAmbient a).left := closed_intoAmbient M a
    have : IsClosedImmersion Xm.left.nilradical.subschemeι := inferInstance
    change IsClosedImmersion ((M.intoAmbient a).left ≫ Xm.left.nilradical.subschemeι)
    infer_instance
  · refine ⟨eqToIso M.start, ?_⟩
    dsimp only [z, Over.comp_left, Over.homMk_left]
    rw [M.intoAmbient_zero]
    rfl
  · intro a
    dsimp only [z]
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
    obtain ⟨_hdim, e, he⟩ := hM a
    have := H.reduced_piece a
    have := H.open_piece a
    have := closed_intoAmbient H a.castSucc
    have := T.isImmersion ν
    have := hTred ν
    obtain ⟨j, hj⟩ := reduced_factors_immersion
      (H.pieceInclusion a ≫ H.intoAmbient a.castSucc).left (T.immersion ν)
      (hν.trans (T.range_immersion ν).ge)
    have : IsImmersion (j ≫ T.immersion ν) := by
      rw [hj, Over.comp_left]
      infer_instance
    have : IsImmersion j := IsImmersion.of_comp j (T.immersion ν)
    have heq : ((e.hom.left ≫ j) ≫ T.immersion ν) ≫
        (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι =
        (BC.map (𝟙 (M.piece a) ≫ M.pieceInclusion a ≫ z a.castSucc) ≫ χ.hom).left := by
      simp only [Category.assoc, hj]
      simpa only [Category.id_comp, Category.assoc, z] using he.symm
    refine ⟨ν, e.hom.left ≫ j, inferInstance, ?_, ?_⟩
    · dsimp only [FiniteFieldDatum.geometricFiber]
      calc
        (((e.hom.left ≫ j) ≫ T.immersion ν) ≫
            (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι) ≫
            pullback.fst a₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          (BC.map (𝟙 (M.piece a) ≫ M.pieceInclusion a ≫ z a.castSucc) ≫ χ.hom).left ≫
            pullback.fst a₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) := by
              rw [heq]
        _ = pullback.fst (M.piece a).hom
            (Spec.map (CommRingCat.ofHom (algebraMap (D.extensionSubfield m hm) D.k))) ≫
            (𝟙 (M.piece a).left ≫ (M.pieceInclusion a).left ≫ (z a.castSucc).left) ≫
            pullback.fst a₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) := by
              rw [Over.comp_left, Category.assoc, hχ]
              simp only [BC, Over.pullback_map_left, Category.assoc]
              rw [← Category.assoc, pullback.lift_fst]
              rfl
    · dsimp only [FiniteFieldDatum.geometricFiber]
      calc
        (((e.hom.left ≫ j) ≫ T.immersion ν) ≫
            (D.geometricFiber (Over.mk a₀)).left.nilradical.subschemeι) ≫
            (D.geometricFiber (Over.mk a₀)).hom =
          (BC.map (𝟙 (M.piece a) ≫ M.pieceInclusion a ≫ z a.castSucc) ≫ χ.hom).left ≫
            (D.geometricFiber (Over.mk a₀)).hom := by
              rw [heq]
        _ = pullback.snd (M.piece a).hom
            (Spec.map (CommRingCat.ofHom (algebraMap (D.extensionSubfield m hm) D.k))) := by
              exact (BC.map (𝟙 (M.piece a) ≫ M.pieceInclusion a ≫ z a.castSucc) ≫ χ.hom).w

end WeilConjectures
