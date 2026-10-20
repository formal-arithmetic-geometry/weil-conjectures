/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.Perfect
public import Sheaf.AlgebraicGeometry.PureDimension
import Mathlib.RingTheory.Jacobson.Artinian
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.NowhereDenseDimZero

/-!
# The reduced boundary of a smooth curve over a perfect field

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-perverse,
`thm-a1-curve-perverse-heart.proof.md`, Step 2
(blueprint: lem-a1-reduced-boundary-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The reduced closed complement of a dense open in a smooth separated finite-type curve
of pure dimension one over a perfect field is reduced and of finite type, has topological
Krull dimension at most zero, and is smooth of relative dimension zero. The dimension of
an empty boundary is `⊥`, that is, minus infinity.
Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-p-dl-a1-perverse,
`thm-a1-curve-perverse-heart.proof.md`, Step 2; Stacks Tags 06LH, 00EU, 02GL and 02GK
(blueprint: lem-a1-reduced-boundary-smooth).

Proof:
1. Choose a finite affine cover of C by finitely generated k-algebras. On each chart the
   closed immersion i is a quotient by an ideal (def-weil-closed-immersion); the quotient
   is again finitely generated. This proves finite type by def-weil-finite-type-morphism.
   Reducedness is the hypothesis def-pc-reduced-scheme.
2. Every chain of irreducible closed subsets of C lies in an irreducible component by
   lem-sc-irreducible-components-cover. Pure dimension one bounds its length by one.
   The closed complement of the dense open has empty interior. Apply
   lem-pc-nowhere-dense-dim-zero, using lem-pc-scheme-dimension-local-rings to compare
   local-ring and topological dimensions. This gives dimension at most zero; for the
   empty scheme the dimension comparison gives minus infinity.
3. By lem-weil-pbc-finite-type-dim-zero-artinian, Z is finite and discrete. Its singleton
   open subschemes are therefore also closed; there are no such pieces when Z is empty.
4. Each singleton subscheme is affine by lem-weil-pbc-finite-discrete-scheme-affine.
   Its section ring is its stalk, hence reduced and local, with a unique prime ideal.
   By lem-weil-pbc-minimal-prime-reduced-localization-field its localization at that
   prime is a field. The localization is the original local ring, since its denominators
   are units. Thus the singleton is Spec of its residue field (def-weil-residue-field),
   compatibly with its k-structure (def-weil-affine-spectrum).
5. Each point is closed, so lem-kun-closed-point-field makes its residue field finite
   over k. Perfectness makes it separable. By lem-weil-pbc-scheme-coproduct-family,
   glue the singleton identifications to a k-isomorphism from Z to the finite coproduct
   of its residue-field spectra. Disjoint open gluing also includes the empty coproduct.
6. By lem-exc-etale-coproduct-etale this coproduct is etale over k. Transport this along
   the k-isomorphism and use lem-weil-pbc-etale-smooth-zero-dimensional-fibres to obtain
   smoothness and pure relative dimension zero. For the empty boundary the pointwise
   relative dimension condition is vacuous. Together with steps 1 and 2 this gives
   all the conclusions. -/
theorem reducedBoundary_smoothOfRelativeDimension_zero
    {k : Type u} [Field k] [PerfectField k] {C U Z : Scheme.{u}}
    [C.Over (Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))] [QuasiCompact (C ↘ Spec (.of k))]
    (hC : C.IsPureDimension 1) (j : U ⟶ C) [IsOpenImmersion j]
    (hj : DenseRange j) (i : Z ⟶ C) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i = (Set.range j)ᶜ) :
    LocallyOfFiniteType (i ≫ C ↘ Spec (.of k)) ∧
      QuasiCompact (i ≫ C ↘ Spec (.of k)) ∧ IsReduced Z ∧
      topologicalKrullDim Z ≤ 0 ∧ (IsEmpty Z → topologicalKrullDim Z = ⊥) ∧
      Smooth (i ≫ C ↘ Spec (.of k)) ∧
      SmoothOfRelativeDimension 0 (i ≫ C ↘ Spec (.of k)) := by
  classical
  have hdimC : topologicalKrullDim C ≤ 1 := by
    unfold topologicalKrullDim Order.krullDim
    refine iSup_le fun p ↦ ?_
    obtain ⟨W, hW, hsub⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible _ p.last.isIrreducible
    let F (q : Set.Iic p.last) : TopologicalSpace.IrreducibleCloseds W :=
      { carrier := Subtype.val ⁻¹' (q.val : Set C)
        isClosed' := q.val.isClosed.preimage continuous_subtype_val
        isIrreducible' := by
          have : IrreducibleSpace (q.val : Set C) :=
            Subtype.irreducibleSpace q.val.isIrreducible
          convert (IrreducibleSpace.isIrreducible_univ (q.val : Set C)).image
            (Set.inclusion (q.property.trans hsub))
            (continuous_inclusion _).continuousOn using 1
          ext x
          simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_preimage]
          exact ⟨fun hx ↦ ⟨⟨x.val, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩ }
    have hF : StrictMono F := by
      intro a b hab
      refine lt_of_le_of_ne (fun x hx ↦ hab.le hx) ?_
      intro heq
      apply hab.ne
      apply Subtype.ext
      apply TopologicalSpace.IrreducibleCloseds.ext
      ext x
      by_cases hx : x ∈ W
      · exact Set.ext_iff.mp (congrArg
          (fun T : TopologicalSpace.IrreducibleCloseds W ↦ (T : Set W)) heq) ⟨x, hx⟩
      · exact iff_of_false (fun ha ↦ hx (hsub (a.property ha)))
          (fun hb ↦ hx (hsub (b.property hb)))
    let p' : LTSeries (Set.Iic p.last) :=
      ⟨p.length, fun n ↦ ⟨p n, p.monotone (Fin.le_last n)⟩, fun n ↦ p.step n⟩
    have h := Order.LTSeries.length_le_krullDim (p'.map F hF)
    change (p.length : WithBot ℕ∞) ≤ topologicalKrullDim W at h
    simpa [hC W hW] using h
  have hnow : IsNowhereDense (Set.range i.base) := by
    apply (isClosed_isNowhereDense_iff_compl.mpr ?_).2
    rw [hZ, compl_compl]
    exact ⟨j.isOpenEmbedding.isOpen_range, hj⟩
  have hdimZ : topologicalKrullDim Z ≤ 0 := by
    rw [← Scheme.dim_eq_topologicalKrullDim]
    exact (dim_le_zero_of_isNowhereDense (C ↘ Spec (.of k)) i
      (by rwa [Scheme.dim_eq_topologicalKrullDim]) hnow).1
  let f := i ≫ C ↘ Spec (.of k)
  have : LocallyOfFiniteType f := inferInstance
  have : QuasiCompact f := inferInstance
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyArtinian Z := .of_topologicalKrullDim_le_zero hdimZ
  have : DiscreteTopology Z := inferInstance
  have : Finite Z := finite_of_compact_of_discrete
  have : IsAffine Z := inferInstance
  have het : Etale f := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    let R := Γ(Spec (.of k), ⊤)
    let e : R ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
    let : Field R := (e.isField (Field.toIsField k)).toField
    have : PerfectField R := PerfectField.of_ringEquiv e.symm
    algebraize [f.appTop.hom]
    have : Algebra.FiniteType R Γ(Z, ⊤) :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    have : Module.Finite R Γ(Z, ⊤) := Module.finite_of_isArtinianRing R Γ(Z, ⊤)
    exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isReduced_of_perfectField R Γ(Z, ⊤))
  refine ⟨inferInstance, inferInstance, inferInstance, hdimZ, ?_, inferInstance,
    inferInstance⟩
  intro h
  let := h
  rw [← Scheme.dim_eq_topologicalKrullDim]
  exact iSup_of_empty _

end AlgebraicGeometry
