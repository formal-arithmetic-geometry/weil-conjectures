/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Topology.Irreducible
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.FieldBaseChangeAffineCovers
import Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg

/-!
# Dimension after field extension and dense open restriction

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
`lem-kun-dimension-extension`; Stacks Project, Tags 00P3 and 0A21.
(blueprint: lem-kun-dimension-extension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Dimension of a finite type scheme over a field is unchanged by any field extension
or any dense open immersion. Source: blueprint `lem-kun-dimension-extension`,
Stacks Project, Tags 00P3 and 0A21 (blueprint: lem-kun-dimension-extension).

Proof:
1. If `X` is empty, the projection makes its base change empty and an open immersion
   into `X` makes its source empty. All three dimensions are bottom (`def-kun-dimension`).
2. Otherwise use `lem-pc-dim-base-change-affine-covers` to cover `X` by affine charts
   `Spec A` and its base change by the matching charts `Spec (A ⊗[K] L)`.
3. The finite type algebras have unchanged dimension by
   `lem-weil-pbc-dimension-preserved-field-extension`. The tensor swap and the chart
   isomorphisms preserve dimension by `lem-weil-pbc-homeomorphism-krull-dimension`.
4. On both schemes dimension is the supremum of chart dimensions: one inequality is
   `lem-weil-pbc-open-subspace-dimension-monotone`, the other is
   `lem-weil-pbc-dimension-bound-open-cover`, using `lem-weil-pbc-scheme-sober`.
   Equal chart dimensions therefore give the first conclusion.
5. For the second conclusion identify `U` with its open image. The field is Noetherian,
   and `lem-weil-pbc-finite-type-over-noetherian` makes `X` Noetherian. Its components
   form a finite closed cover (`lem-sc-noetherian-closed-subset-finite-components`).
   By `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `U` and its intersections
   with affine opens are quasi-compact.
6. Thus the open immersion is quasi-compact and finite type by
   `lem-weil-pbc-qc-open-immersion-finite-type`. Composition of locally finite type
   maps (`lem-weil-pbc-proper-fp-permanence`, clause (e)), together with the preceding
   quasi-compactness, makes `U` finite type over `K`.
7. For each component `C`, remove all other components. The resulting nonempty open
   contains its generic point and lies in `C`. Density makes its intersection with
   `U` nonempty, so the generic point lies in `U`. Hence `C ∩ U` is a nonempty closed
   irreducible subset of `U` with that same generic point (`lem-weil-pbc-scheme-sober`).
8. By `lem-sc-closed-irreducible-dimension-trdeg`, dimensions of `C` and `C ∩ U` are
   the transcendence degrees of their generic residue fields. Open restriction gives
   the same stalk, residue field and `K`-algebra structure, hence equal dimensions.
9. Every irreducible closed subset of `X` lies in a component, by the finite closed
   cover and irreducibility. Thus dimension of `X` is the maximum of its component
   dimensions (`def-kun-dimension`). The equal component dimensions in `U` give
   `dim X ≤ dim U`; open-subspace monotonicity gives the reverse inequality. -/
theorem topologicalKrullDim_fieldExtension_and_denseOpen
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    (∀ (L : Type u) [Field L] [Algebra K L],
      topologicalKrullDim (pullback (X ↘ Spec (.of K))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) =
        topologicalKrullDim X) ∧
    (∀ (U : Scheme.{u}) (j : U ⟶ X) [IsOpenImmersion j],
      DenseRange j → topologicalKrullDim U = topologicalKrullDim X) := by
  sorry

end AlgebraicGeometry
