/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.ZetaSeries
import WeilConjectures.PointCount
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Residue-field decomposition of a finite reduced discrete scheme

Source: Stacks Project, Properties, Tag 0AAX, and Curves, Tag 0E38 (2)(a).
(blueprint: lem-trf-finite-reduced-discrete-residue-fields).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem openImmersion_fromSpecResidueField_of_discrete
    (T : Scheme.{u}) [IsReduced T] [DiscreteTopology T] (t : T) :
    IsOpenImmersion (T.fromSpecResidueField t) := by
  let U : T.Opens := ⟨{t}, isOpen_discrete _⟩
  have hclosed : IsClosed ({t} : Set T) := isClosed_discrete _
  have : IsClosedImmersion (T.fromSpecResidueField t) :=
    isClosed_singleton_iff_isClosedImmersion.mp hclosed
  let s : Spec (T.residueField t) ⟶ U :=
    IsOpenImmersion.lift U.ι (T.fromSpecResidueField t) (by
      rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
      exact Set.Subset.rfl)
  have hs : s ≫ U.ι = T.fromSpecResidueField t := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (s ≫ U.ι) := hs ▸ inferInstance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s U.ι
  have : Subsingleton U := Set.subsingleton_singleton.coe_sort
  have : Surjective s := ⟨fun y ↦
    ⟨default, Subsingleton.elim _ _⟩⟩
  have : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  rw [← hs]
  infer_instance

/-- A finite reduced discrete scheme with finite separable residue fields is the coproduct
of their spectra over the ground field.

Source: Stacks Project, Properties, Tag 0AAX, and Curves, Tag 0E38 (2)(a).
(blueprint: lem-trf-finite-reduced-discrete-residue-fields).

Proof: Each singleton is an open reduced subscheme. The canonical map from its residue-field
spectrum is a surjective closed immersion, hence an isomorphism since the singleton is reduced.
Thus the residue-field maps are open immersions with disjoint ranges covering the scheme.
Their coproduct map is an isomorphism. Reindex the finite set of points by `Fin n`; the canonical
residue-field maps commute with the structural maps to `Spec k`. For an empty scheme this is
precisely the empty coproduct. -/
theorem finite_reduced_discrete_residue_fields
    {k : Type u} [Field k] (T : Scheme.{u}) [IsReduced T]
    [Finite T] [DiscreteTopology T] (g : T ⟶ Spec (.of k))
    (hsep : ∀ t : T, (g.residueFieldAlgebraMap t).Finite ∧
      @Algebra.IsSeparable k (T.residueField t) _ _
        (g.residueFieldAlgebraMap t).toAlgebra) :
    ∃ (n : ℕ) (K : Fin n → Type u) (_ : ∀ a, Field (K a)) (ι : ∀ a, k →+* K a),
      (∀ a, (ι a).Finite ∧ @Algebra.IsSeparable k (K a) _ _ (ι a).toAlgebra) ∧
      ∃ e : (∐ fun a : Fin n ↦ Spec (.of (K a))) ≅ T,
        ∀ a : Fin n,
          Sigma.ι (fun b : Fin n ↦ Spec (.of (K b))) a ≫ e.hom ≫ g =
            Spec.map (CommRingCat.ofHom (ι a)) := by
  classical
  let : Fintype T := Fintype.ofFinite T
  let q : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  let K : Fin (Fintype.card T) → Type u := fun a ↦ T.residueField (q a)
  let α : ∀ a, Spec (.of (K a)) ⟶ T := fun a ↦ T.fromSpecResidueField (q a)
  have inst (a : Fin (Fintype.card T)) : IsOpenImmersion (α a) :=
    openImmersion_fromSpecResidueField_of_discrete T (q a)
  have : IsOpenImmersion (Sigma.desc α) :=
    isOpenImmersion_sigmaDesc _ α (by
      intro a b hab
      change Disjoint (Set.range (T.fromSpecResidueField (q a)))
        (Set.range (T.fromSpecResidueField (q b)))
      rw [Scheme.range_fromSpecResidueField, Scheme.range_fromSpecResidueField,
        Set.disjoint_singleton]
      exact q.injective.ne hab)
  have : Surjective (Sigma.desc α) := ⟨fun t ↦ by
    obtain ⟨a, rfl⟩ := q.surjective t
    refine ⟨Sigma.ι (fun b ↦ Spec (.of (K b))) a default, ?_⟩
    change (Sigma.ι _ a ≫ Sigma.desc α) default = q a
    rw [colimit.ι_desc]
    exact T.fromSpecResidueField_apply (q a) default⟩
  have : IsIso (Sigma.desc α) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  refine ⟨Fintype.card T, K, inferInstance, fun a ↦ g.residueFieldAlgebraMap (q a),
    fun a ↦ hsep (q a), asIso (Sigma.desc α), ?_⟩
  intro a
  simpa [α] using (g.specMap_residueFieldAlgebraMap (q a)).symm

end AlgebraicGeometry
