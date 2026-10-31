/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.ZeroDimIntegralPoint

/-!
# Decomposition of smooth curves into connected curves and points

Source: `literature/stacks-project/etale-cohomology.tex`, Tag 0A5B
(label `lemma-constant-smooth-statements`) (blueprint: lem-sbc-smooth-curve-points-decomposition).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/--
For an algebraically closed field, a smooth separated finite-type scheme of dimension at most
one is a finite coproduct of smooth connected one-dimensional curves and copies of the base point.
Source: Stacks Project, Etale Cohomology, Tag 0A5B, opening reduction in the proof,
under Situation `situation-what-to-prove`; Properties, Tags 0569 and 033N; Varieties, Tag 06LH.
(blueprint: lem-sbc-smooth-curve-points-decomposition)

Proof:
1. The field is Noetherian, so `Spec k` is Noetherian. Finite type makes `C` Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`), hence it has finitely many irreducible
   components (`lem-weil-pbc-noetherian-finite-components`).
2. The irreducible components cover `C` (`lem-sc-irreducible-components-cover`). Join
   intersecting components in a finite graph. The union for each graph component is closed,
   and its complement is a finite union of closed components, so it is also open. Each union
   is connected: irreducible subsets are connected, and unions along intersecting graph
   paths remain connected. These disjoint unions are the nonempty connected components;
   there are none if `C` is empty (`def-weil-irreducible-components`).
3. Equip each clopen union with its open-subscheme structure. Its inclusion is an open
   immersion (`def-weil-open-immersion`) and a closed immersion (`def-weil-closed-immersion`):
   on stalks the map to its pushforward is an isomorphism inside and has zero target outside.
   Smoothness restricts to this open (`lem-weil-pbc-smooth-restrict-open-subschemes`). Smooth
   implies locally of finite presentation, hence locally of finite type
   (`def-sbc-smooth-morphisms`, `def-sbc-locally-finite-presentation`); the closed subset of
   the quasi-compact `C` is quasi-compact, giving finite type (`def-weil-finite-type-morphism`).
   Its diagonal is a base change of the closed diagonal of `C`, giving separatedness
   (`lem-pc-closed-imm-base-change`, `def-weil-proper-morphism`).
4. Smoothness gives regular stalks (`lem-sc-smooth-regular`). The component is locally
   Noetherian as an open of `C`, hence regular (`def-weil-regular-scheme`), and its
   nonempty connected space makes it integral (`lem-sc-regular-connected-integral`).
   Chains of irreducible closed subsets of this closed component are chains in `C`, so its
   dimension is at most one; nonemptiness makes it zero or one
   (`def-sc-curves`, `def-kun-topological-krull-dimension`).
5. Partition the finite indices by dimension. The dimension-one components give the `D i`
   (`def-sc-curves`); each integral finite-type dimension-zero component is `Spec k` over `k`
   (`lem-weil-pbc-zero-dim-integral-point`). Form their coproduct
   (`lem-weil-pbc-scheme-coproduct-family`). Component inclusions give a map to `C`;
   its inverses on the disjoint covering opens glue, and both composites are identities
   on that cover. This gives an isomorphism over `k`. Replace the zero-dimensional summands
   by `Spec k` and reorder the indices. The coprojections are the clopen component
   inclusions of step 3. For empty `C`, use the empty coproduct.
-/
theorem smooth_curve_points_decomposition
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsCurve f] [Smooth f]
    : ∃ (I J : Type u) (_ : Fintype I) (_ : Fintype J)
        (D : I → Scheme.{u}) (d : ∀ i, D i ⟶ Spec (.of k)),
        (∀ i, IsConnectedCurve (d i)) ∧
        (∀ i, Smooth (d i)) ∧
        ∃ (q : (∐ fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)) ⟶ Spec (.of k)),
          (∀ i, Sigma.ι (fun s : Sum I J ↦ match s with
            | Sum.inl i => D i
            | Sum.inr _ => Spec (.of k)) (Sum.inl i) ≫ q = d i) ∧
          (∀ j, Sigma.ι (fun s : Sum I J ↦ match s with
            | Sum.inl i => D i
            | Sum.inr _ => Spec (.of k)) (Sum.inr j) ≫ q = 𝟙 _) ∧
          ∃ (e : C ≅ ∐ fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)),
            e.hom ≫ q = f ∧
            (∀ s, IsOpenImmersion (Sigma.ι (fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)) s)) ∧
            (∀ s, IsClosedImmersion (Sigma.ι (fun s : Sum I J ↦ match s with
              | Sum.inl i => D i
              | Sum.inr _ => Spec (.of k)) s))
 := by
  classical
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian C := {}
  let A := ConnectedComponents C
  let : Fintype A := Fintype.ofFinite A
  let V : A → C.Opens := fun a ↦ ⟨ConnectedComponents.mk ⁻¹' {a}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    rw [connectedComponents_preimage_singleton]
    exact TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hcl (a : A) : IsClosed (V a : Set C) :=
    isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have hconn (a : A) : ConnectedSpace (V a).toScheme := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    have h : (V (ConnectedComponents.mk x) : Set C) = connectedComponent x :=
      connectedComponents_preimage_singleton
    exact isConnected_iff_connectedSpace.mp (h ▸ isConnected_connectedComponent)
  let g : ∀ a : A, (V a).toScheme ⟶ Spec (.of k) := fun a ↦ (V a).ι ≫ f
  have hgsm (a : A) : Smooth (g a) := by dsimp [g]; infer_instance
  have hgin (a : A) : IsIntegral (V a).toScheme := by
    have := hgsm a
    have := IsRegular.of_smooth (g a)
    have := hconn a
    exact IsRegular.isIntegral (V a).toScheme
  have hgcl (a : A) : IsClosedImmersion (V a).ι :=
    .of_isPreimmersion _ ((V a).range_ι ▸ hcl a)
  have hgdim (a : A) : topologicalKrullDim (V a).toScheme ≤ 1 :=
    (topologicalKrullDim_subspace_le C (V a)).trans (IsCurve.krullDim_le_one (f := f))
  have hgcurve (a : A) : IsCurve (g a) := by
    have := hgcl a
    dsimp [g]
    exact { krullDim_le_one := hgdim a }
  have hdim (a : A) : topologicalKrullDim (V a).toScheme = 0 ∨
      topologicalKrullDim (V a).toScheme = 1 := by
    have := hgin a
    have : Nonempty (TopologicalSpace.IrreducibleCloseds (V a).toScheme) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
    have hnonneg : 0 ≤ topologicalKrullDim (V a).toScheme := Order.krullDim_nonneg
    have hle := hgdim a
    generalize topologicalKrullDim (V a).toScheme = t at hnonneg hle ⊢
    cases t with
    | bot => simp at hnonneg
    | coe t =>
      have ht : t ≤ 1 := by exact_mod_cast hle
      rcases Order.le_one_iff.mp ht with ht | ht <;> simp [ht]
  let I := {a : A // topologicalKrullDim (V a).toScheme = 1}
  let J := {a : A // topologicalKrullDim (V a).toScheme ≠ 1}
  let D : I → Scheme.{u} := fun i ↦ (V i.val).toScheme
  let d : ∀ i : I, D i ⟶ Spec (.of k) := fun i ↦ g i.val
  have hdcurve (i : I) : IsConnectedCurve (d i) := by
    have := hgin i.val
    have := hgcurve i.val
    exact { connectedSpace := inferInstance, krullDim_eq_one := i.property }
  have hdsm (i : I) : Smooth (d i) := hgsm i.val
  have hjiso (j : J) : IsIso (g j.val) := by
    let : (V j.val).toScheme.Over (Spec (.of k)) := ⟨g j.val⟩
    have := hgin j.val
    have : LocallyOfFiniteType ((V j.val).toScheme ↘ Spec (.of k)) :=
      (hgcurve j.val).toLocallyOfFiniteType
    have : QuasiCompact ((V j.val).toScheme ↘ Spec (.of k)) :=
      (hgcurve j.val).toQuasiCompact
    exact isIso_structure_of_integral_zero_dim (V j.val).toScheme
      ((hdim j.val).resolve_right j.property)
  let E : Sum I J → Scheme.{u} := fun s ↦ match s with
    | Sum.inl i => D i
    | Sum.inr _ => Spec (.of k)
  let r : Sum I J ≃ A := Equiv.sumCompl fun a ↦ topologicalKrullDim (V a).toScheme = 1
  let α : ∀ s, E s ⟶ C := fun s ↦ match s with
    | Sum.inl i => (V i.val).ι
    | Sum.inr j => (asIso (g j.val)).inv ≫ (V j.val).ι
  have hαopen (s) : IsOpenImmersion (α s) := by
    cases s with
    | inl i => dsimp [α]; infer_instance
    | inr j => have := hjiso j; dsimp [α]; infer_instance
  have hαclosed (s) : IsClosedImmersion (α s) := by
    cases s with
    | inl i => exact hgcl i.val
    | inr j =>
      have := hjiso j
      have := hgcl j.val
      dsimp [α]
      infer_instance
  have hrange (s) : (α s).opensRange = V (r s) := by
    cases s with
    | inl i => exact (V i.val).opensRange_ι
    | inr j =>
      have := hjiso j
      dsimp [α, r]
      rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
      rfl
  have hαcov : ⨆ s, (α s).opensRange = ⊤ := by
    simp only [hrange]
    rw [r.surjective.iSup_comp]
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ConnectedComponents.mk x, rfl⟩
  have hαdisj : Pairwise (fun s t ↦ Disjoint (α s).opensRange (α t).opensRange) := by
    intro s t hst
    rw [hrange, hrange]
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact (Set.disjoint_singleton.mpr (r.injective.ne hst)).preimage _
  have hcolim := nonempty_isColimit_cofanMk_of α hαcov hαdisj
  have hdesc : IsIso (Sigma.desc α) := by
    simpa only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc,
      cofan_mk_inj, Cofan.mk_pt] using hcolim
  let e : C ≅ ∐ E := (asIso (Sigma.desc α)).symm
  let q : (∐ E) ⟶ Spec (.of k) := Sigma.desc α ≫ f
  refine ⟨I, J, inferInstance, inferInstance, D, d, hdcurve, hdsm, q, ?_, ?_, e, ?_,
    ?_, ?_⟩
  · intro i
    change Sigma.ι E (Sum.inl i) ≫ (Sigma.desc α ≫ f) = d i
    rw [← Category.assoc, Sigma.ι_desc]
  · intro j
    change Sigma.ι E (Sum.inr j) ≫ (Sigma.desc α ≫ f) = 𝟙 _
    rw [← Category.assoc, Sigma.ι_desc]
    change ((asIso (g j.val)).inv ≫ (V j.val).ι) ≫ f = 𝟙 _
    rw [Category.assoc]
    exact (asIso (g j.val)).inv_hom_id
  · change (asIso (Sigma.desc α)).inv ≫ ((asIso (Sigma.desc α)).hom ≫ f) = f
    simp
  · intro s
    exact inferInstanceAs (IsOpenImmersion (Sigma.ι E s))
  · intro s
    have : IsClosedImmersion (Sigma.ι E s ≫ Sigma.desc α) := by
      rw [Sigma.ι_desc]
      exact hαclosed s
    exact IsClosedImmersion.of_comp (Sigma.ι E s) (Sigma.desc α)

end AlgebraicGeometry
