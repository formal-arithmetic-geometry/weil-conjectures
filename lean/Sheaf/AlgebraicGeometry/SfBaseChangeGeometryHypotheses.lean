/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Compactification.NagataCompactification

/-!
# Geometric hypotheses for the six-functor base-change exchanges

Source: blueprint `sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md`,
clause (4), geometric input to the base-change theorems; Stacks Tags 01T6, 0A3V,
00P3, 01W4 and 0F41 (blueprint: lem-sf-bc-geometry-hypotheses).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem dimension_empty (A : Type*) [TopologicalSpace A] [IsEmpty A] :
    topologicalKrullDim A = ⊥ := by
  apply Order.krullDim_eq_bot_iff.mpr
  exact ⟨fun Z ↦ Z.2.nonempty.elim fun x _ ↦ isEmptyElim x⟩

private theorem field_extension_dimension_le
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {Z : Scheme.{u}} (a : Z ⟶ Spec (.of k)) [LocallyOfFiniteType a]
    (d : ℕ) (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  by_cases hZ : Nonempty Z
  · let := hZ
    obtain ⟨_, I, A, rings, algebras, hft, U, V, hU, hV, ⟨eU⟩, ⟨eV⟩⟩ :=
      exists_field_baseChange_affine_covers k K a
    let := rings
    let := algebras
    refine topologicalKrullDim_le_of_iSup_eq_top V hV _ fun i ↦ ?_
    have := hft i
    calc
      topologicalKrullDim (V i : Set (pullback a b : Scheme.{u})) =
          topologicalKrullDim (Spec (.of (TensorProduct k (A i) K))) :=
        IsHomeomorph.topologicalKrullDim_eq _ (eV i).hom.homeomorph.isHomeomorph
      _ = topologicalKrullDim (Spec (.of (TensorProduct k K (A i)))) := by
        exact IsHomeomorph.topologicalKrullDim_eq
          (PrimeSpectrum.homeomorphOfRingEquiv
            (Algebra.TensorProduct.comm k (A i) K).toRingEquiv)
          (PrimeSpectrum.homeomorphOfRingEquiv
            (Algebra.TensorProduct.comm k (A i) K).toRingEquiv).isHomeomorph
      _ = topologicalKrullDim (Spec (.of (A i))) :=
        topologicalKrullDim_spec_tensorProduct_of_field_extension k K (A i)
      _ = topologicalKrullDim (U i : Set Z) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (eU i).hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim Z := topologicalKrullDim_subspace_le Z (U i)
      _ ≤ (d : WithBot ℕ∞) := hd
  · have : IsEmpty Z := not_nonempty_iff.mp hZ
    have : IsEmpty (pullback a b : Scheme.{u}) :=
      Function.isEmpty (pullback.fst a b)
    rw [dimension_empty]
    exact bot_le

private theorem corner_geometry (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) (hell : ell.Prime) (hellp : ell ≠ D.p)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))] :
    IsNoetherian T ∧ CompactSpace T ∧ QuasiSeparatedSpace T ∧
      (∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)) ∧
      (∀ t : T, IsUnit (ell : T.presheaf.stalk t)) := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (T ↘ Spec (.of D.k))
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of D.k))
  have : IsNoetherian T := ⟨⟩
  refine ⟨inferInstance, inferInstance, inferInstance,
    exists_topologicalKrullDim_le (T ↘ Spec (.of D.k)), ?_⟩
  let := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hu : IsUnit (ell : D.k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime D.k hell hellp.symm)
  intro t
  let φ : D.k →+* T.presheaf.stalk t :=
    ((T.presheaf.germ ⊤ t trivial).hom.comp (T ↘ Spec (.of D.k)).appTop.hom).comp
      (Scheme.ΓSpecIso (.of D.k)).inv.hom
  simpa only [map_natCast] using hu.map φ

/-- The corners and arrows of a Cartesian square of separated finite-type schemes over
an algebraic closure of a finite field satisfy the geometric hypotheses for base change.
The single fibre bound is chosen before the geometric point. The compactifications have
quasi-compact open factors, explicitly recorded in addition to `Compactification`.

Source: blueprint `sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md`,
clause (4); Stacks Tags 01T6, 0A3V, 00P3, 01W4, 0F41
(blueprint: lem-sf-bc-geometry-hypotheses).

Proof:
1. Apply lem-weil-pbc-qcqs-over-affine to each structure map to Spec k. A field is
   Noetherian, so lem-weil-pbc-finite-type-over-noetherian gives Noetherian corners.
   Apply lem-kun-dimension-finite-type to bound each corner's dimension. Empty
   corners also satisfy these conclusions.
2. Finite type includes quasi-compactness (def-weil-finite-type-morphism), and
   lem-pc-separated-quasi-separated supplies quasi-separated arrows. Since ell is
   different from the characteristic, its nonzero image in k has an inverse.
   The structure maps carry this inverse to every local ring, including vacuously
   the local rings of an empty corner.
3. Use lem-fin-finite-type-fibre-dimension-bound with the quasi-compact base Y to
   choose one natural bound for all ordinary fibres.
4. By lem-pod-separated-finite-type-base-change each ordinary fibre is of finite
   type over its residue field. The matching affine covers of
   lem-pc-dim-base-change-affine-covers identify scalar extension chartwise with
   tensor products. Apply lem-weil-pbc-open-subspace-dimension-monotone and
   lem-weil-pbc-dimension-preserved-field-extension to bound all extended charts.
   The pullback universal property identifies the scalar extension with the
   geometric fibre, for every algebraically closed field-valued point.
5. Schemes are sober (lem-weil-pbc-scheme-sober). Apply
   lem-weil-pbc-dimension-bound-open-cover to the extended affine cover. Empty
   fibres have dimension bottom by def-kun-topological-krull-dimension; an empty
   base permits the uniform bound zero.
6. Apply lem-weil-pbc-proper-base-change to f along g and use the chosen pullback
   identification of def-weil-pbc-cartesian-square to obtain properness of f'.
7. For any separated finite-type morphism into a corner, that corner is qcqs by
   step 1. Apply thm-nagata-compactification. Its factorization is the given
   Compactification, and its open immersion is quasi-compact because the original
   morphism is quasi-compact (def-nagata-compactification). -/
theorem sf_baseChange_geometry_hypotheses
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ)
    (hell : ell.Prime) (hellp : ell ≠ D.p)
    {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [Y'.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X' ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y' ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of D.k))] [f'.IsOver (Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (sq : ChosenCartesianSquare g' f' f g) :
    (∀ T : Scheme.{u}, (T = X ∨ T = Y ∨ T = X' ∨ T = Y') →
      IsNoetherian T ∧ CompactSpace T ∧ QuasiSeparatedSpace T ∧
      (∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)) ∧
      (∀ t : T, IsUnit (ell : T.presheaf.stalk t))) ∧
    (QuasiCompact f ∧ QuasiSeparated f) ∧
    (QuasiCompact g ∧ QuasiSeparated g) ∧
    (QuasiCompact g' ∧ QuasiSeparated g') ∧
    (QuasiCompact f' ∧ QuasiSeparated f') ∧
    (∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (↑(pullback f y) : Type u) ≤ (e : WithBot ℕ∞) ∧
      (IsEmpty (↑(pullback f y) : Type u) →
        topologicalKrullDim (↑(pullback f y) : Type u) = ⊥)) ∧
    (IsProper f → IsProper f') ∧
    (∀ T : Scheme.{u}, (T = X ∨ T = Y ∨ T = X' ∨ T = Y') →
      ∀ (U : Scheme.{u}) (h : U ⟶ T),
        IsSeparated h → LocallyOfFiniteType h → QuasiCompact h →
        ∃ c : Compactification h, QuasiCompact c.i) := by
  have hcorners : ∀ T : Scheme.{u}, (T = X ∨ T = Y ∨ T = X' ∨ T = Y') →
      IsNoetherian T ∧ CompactSpace T ∧ QuasiSeparatedSpace T ∧
      (∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)) ∧
      (∀ t : T, IsUnit (ell : T.presheaf.stalk t)) := by
    intro T hT
    rcases hT with rfl | rfl | rfl | rfl <;> exact corner_geometry D ell hell hellp _
  have : CompactSpace Y := (hcorners Y (Or.inr (Or.inl rfl))).2.1
  refine ⟨hcorners, ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩, ?_, ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_fibre_dimension_bound f
    refine ⟨e, fun Ω _ _ y ↦ ⟨?_, ?_⟩⟩
    · let q := (Scheme.SpecToEquivOfField Ω Y) y
      let : Algebra (Y.residueField q.1) Ω := q.2.hom.toAlgebra
      let j := Spec.map q.2
      have hj : j ≫ Y.fromSpecResidueField q.1 = y :=
        (Scheme.SpecToEquivOfField Ω Y).symm_apply_apply y
      have : LocallyOfFiniteType (f.fiberToSpecResidueField q.1) := by
        dsimp [Scheme.Hom.fiberToSpecResidueField]
        infer_instance
      have hb := field_extension_dimension_le (Y.residueField q.1) Ω
        (f.fiberToSpecResidueField q.1) e (he q.1)
      rw [← hj]
      let iso := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField q.1) j
      exact (IsHomeomorph.topologicalKrullDim_eq _ iso.hom.homeomorph.isHomeomorph).ge.trans hb
    · intro h
      let := h
      exact dimension_empty _
  · intro hf
    let := hf
    rw [← sq.hom_snd]
    infer_instance
  · intro T hT U h hs hft hqc
    have := (hcorners T hT).2.1
    have := (hcorners T hT).2.2.1
    let c := NagataCompactification h
    exact ⟨c, c.quasiCompact_openImmersion hqc⟩

end AlgebraicGeometry
