/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.AlgebraicGeometry.Properties

/-! # Strict henselization as a limit of smaller-dimensional models

Source: Stacks Project, Tag 0F0U, and the blueprint node `lem-kun-0f0u`
(blueprint: lem-kun-0f0u).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- At a point of positive residue transcendence degree, the strict henselization is a
cofiltered inverse limit of affine finite-type schemes over a separably closed extension of
the base field, each of strictly smaller Krull dimension. The point `x` of the informal
statement is `s (IsLocalRing.closedPoint Ω)`; `s` specifies the geometric point needed to
define its strict henselization. The unused abbreviation `d = dim_x X` is omitted.

Source: Stacks Project, Tag 0F0U, positive-transcendence-degree consequence
(blueprint: lem-kun-0f0u).

Proof:
1. By `lem-kun-finite-type-residue-trdeg`, the residue transcendence degree `a` is finite.
Apply `lem-kun-strict-local-algebraic-residue-models` to `X` and the point underlying `s`.
It supplies an affine neighbourhood `U`, a separably closed extension `L/K` of transcendence
degree `a`, and a small cofiltered system of nonempty affine finite-type `L`-schemes with
affine transitions and limit the strict henselization over `U`. Each model maps to `U`
over `K`, and every induced residue extension is algebraic. Forget the maps to `U` to
obtain the asserted scheme limit; the model construction gives the compatible `L`-maps.
2. For a nonempty irreducible closed subset `C` of a model, choose its generic point `η`
 using `lem-sc-scheme-sober`. Let `v` be its image in `U` and let `D` be the closure of `v`.
By `lem-sc-closed-irreducible-dimension-trdeg`, their dimensions are respectively
`trdeg_L κ(η)` and `trdeg_K κ(v)`. The algebraic residue extension and
`lem-kun-transcendence-degree-tower` give `dim C + a = dim D ≤ dim U ≤ dim X`.
The last inequalities use `def-kun-dimension`: closed-subspace chains remain chains, and
taking closures embeds the strict chains of the open subspace `U` into those of `X`.
3. By `lem-kun-dimension-finite-type`, `N = dim X` is finite, and it is nonnegative since
`X` has the point underlying `s`. A chain of length `r` in a model, viewed inside its
largest member `C`, has `r ≤ dim C`, so step 2 gives `r + a ≤ N`. Nonemptiness gives a
length-zero chain and hence `a ≤ N`. Taking the supremum of chain lengths gives
`dim X_i ≤ N - a < N`, because `a > 0`. Combine this with the presentation from step 1.
-/
theorem exists_strictHenselization_limit_smaller_dimension
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hpos : 0 < @Algebra.trdeg K (X.residueField (s (IsLocalRing.closedPoint Ω))) _ _
      (((X ↘ Spec (.of K)).residueFieldAlgebraMap
        (s (IsLocalRing.closedPoint Ω))).toAlgebra)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : IsSepClosed L),
      ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
        (D : I ⥤ Over (Spec (.of L))) (c : Cone (D ⋙ Over.forget (Spec (.of L)))),
        Nonempty (IsLimit c) ∧ Nonempty (strictHenselizationScheme s ≅ c.pt) ∧
        (∀ i : I, IsAffine (D.obj i).left ∧ LocallyOfFiniteType (D.obj i).hom ∧
          QuasiCompact (D.obj i).hom ∧
          topologicalKrullDim (D.obj i).left < topologicalKrullDim X) ∧
        (∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f).left) := by
  sorry

end AlgebraicGeometry.Scheme
