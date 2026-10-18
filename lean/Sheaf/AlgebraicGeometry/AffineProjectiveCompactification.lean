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
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

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
  sorry

end AlgebraicGeometry
