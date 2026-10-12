module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-! Intermediate fibre facts for zero-dimensional base change.
Source: Stacks Project, schemes.tex Lemma 01JT and algebra.tex Lemma 00P4.
(blueprint: new-zdbp-fibres-point)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Point uniqueness in the base-change fibre. Source: Stacks Project, schemes.tex Lemma 01JT
and algebra.tex Theorem 00FV. The fibre-product point correspondence identifies the fibre
over each c with Spec (κ(c) ⊗ₖ k′); the residue-field isomorphism from Nullstellensatz
identifies this ring with k′, which has one prime. (blueprint: new-zdbp-fibres-point) -/
theorem zeroDimensional_baseChange_fibre_points
    (k k' : Type v) [Field k] [Field k'] [IsAlgClosed k] [Algebra k k']
    (C : Scheme.{v}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))]
    (hC : topologicalKrullDim C ≤ 0) :
    ∀ c : C, ∃! z : (pullback (C ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{v}),
      (pullback.fst (C ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).base z = c := by sorry

end AlgebraicGeometry
