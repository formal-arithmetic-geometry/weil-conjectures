/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.DimensionExtension

/-!
# Projective compactification of an affine scheme

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
`lem-kun-compactification-affine`, order 1746 (blueprint: lem-kun-compactification-affine).
See also Stacks Project, Tags 0200, 01RG and 0A21.

The compactification is the scheme-theoretic image of the composite of a closed immersion
into affine space with a standard affine chart of projective space. A finite coordinate
type `n` with distinguished coordinate `i` represents projective space of dimension
`Fintype.card n - 1`; its standard chart has coordinates `{k : n // k ≠ i}`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine scheme of finite type over a field admits a projective compactification of
the same Krull dimension, obtained by scheme-theoretic closure in projective space.

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`, order 1746;
Stacks Project, Tags 0200, 01RG and 0A21 (blueprint: lem-kun-compactification-affine).

Proof:
1. Choose finitely many algebra generators of the affine coordinate algebra over `K`.
   The resulting polynomial-algebra surjection gives a closed immersion `e` into affine
   space. Compose with the standard chart to obtain `j` into projective space, over `K`;
   this is the affine-base construction in `lem-chow-affine-immersion`.
2. Take `j.image`, the scheme-theoretic closure. The finite-type source is quasi-compact;
   projective space over `K` is separated, so `j` is quasi-compact. By
   `lem-chow-closed-model` (Stacks 01RG), `j.toImage` is an open immersion and is
   scheme-theoretically dense. Its composite with `j.imageι` is `j`.
3. Scheme-theoretic density implies topological density: a nonempty affine open disjoint
   from the closure of the image would have its ring of sections inject into the zero ring
   of the empty inverse image, forcing that affine open to be empty. Quasi-compactness
   of the open immersion follows from `lemma-nagata-open-immersion-qc-over-separated-target`.
4. The closed immersion `j.imageι` into finite-dimensional projective space gives
   `IsHProjective` for its composite with the projection. It is proper and hence finite type.
5. Apply the dense-open clause of `lem-kun-dimension-extension` to `j.toImage` and reverse
   the resulting equality. This includes the empty scheme, whose dimension is bottom. -/
theorem exists_affine_projective_compactification (K : Type u) [Field K]
    (X : Scheme.{u}) [IsAffine X] [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    ∃ (n : Type u) (_ : Finite n) (i : n)
      (e : X ⟶ 𝔸({k : n // k ≠ i}; Spec (.of K)))
      (j : X ⟶ ℙ(n; Spec (.of K))),
      IsClosedImmersion e ∧
      e ≫ 𝔸({k : n // k ≠ i}; Spec (.of K)) ↘ Spec (.of K) = X ↘ Spec (.of K) ∧
      j = e ≫ (ProjectiveSpace.standardOpenIso n (Spec (.of K)) i).inv ≫
        (ProjectiveSpace.standardOpen n (Spec (.of K)) i).ι ∧
      IsOpenImmersion j.toImage ∧ DenseRange j.toImage ∧
      IsHProjective (j.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K)) ∧
      topologicalKrullDim j.image = topologicalKrullDim X := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_closure_range_appTop_union_eq_top (X ↘ Spec (.of K))
  let n := Option s
  let i : n := none
  let v : {k : n // k ≠ i} → Γ(X, ⊤) := fun a ↦ a.val.elim 0 Subtype.val
  have hv : Set.range v = (s : Set Γ(X, ⊤)) := by
    ext x
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      cases a with
      | none => exact (ha rfl).elim
      | some b => exact b.property
    · intro hx
      exact ⟨⟨some ⟨x, hx⟩, Option.some_ne_none _⟩, rfl⟩
  let e := AffineSpace.homOfVector (X ↘ Spec (.of K)) v
  have he : IsClosedImmersion e :=
    AffineSpace.isClosedImmersion_homOfVector _ _ (by rw [hv]; exact hs)
  let j := e ≫ (ProjectiveSpace.standardOpenIso n (Spec (.of K)) i).inv ≫
    (ProjectiveSpace.standardOpen n (Spec (.of K)) i).ι
  have : IsImmersion j := by dsimp [j]; infer_instance
  have : QuasiSeparatedSpace ℙ(n; Spec (.of K)) :=
    quasiSeparatedSpace_of_quasiSeparated (ℙ(n; Spec (.of K)) ↘ Spec (.of K))
  have : QuasiCompact j := inferInstance
  have hp : IsHProjective (j.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K)) :=
    ⟨n, inferInstance, j.imageι, inferInstance, rfl⟩
  let : j.image.Over (Spec (.of K)) :=
    ⟨j.imageι ≫ ℙ(n; Spec (.of K)) ↘ Spec (.of K)⟩
  have : IsHProjective (j.image ↘ Spec (.of K)) := hp
  refine ⟨n, inferInstance, i, e, j, he, AffineSpace.homOfVector_over _ _, rfl,
    inferInstance, j.toImage.denseRange, hp, ?_⟩
  exact ((topologicalKrullDim_fieldExtension_and_denseOpen (K := K) (X := j.image)).2
    X j.toImage j.toImage.denseRange).symm

end AlgebraicGeometry
