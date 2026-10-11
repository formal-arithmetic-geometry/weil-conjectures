/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.FinitelyGeneratedEtaleSubsheaf
public import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Approximation of sheaves supported at closed points

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-cp-approximation.md`
(blueprint: lem-kun-cp-approximation); Stacks Project, Tags 0F0N and 03SA.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An abelian etale sheaf supported at closed points of a finite-type scheme over a
separably closed field is the filtered colimit of its finitely generated subsheaves.
Each such subsheaf has finite support, and is the direct image of its restriction to
that support with the reduced closed subscheme structure.
Source: blueprint `lem-kun-cp-approximation`, Stacks Project, Tags 0F0N and 03SA
(blueprint: lem-kun-cp-approximation).

Proof:
1. Finite-generator subsheaves are filtered by taking the union of finite families of
sections. Every etale chart is covered by affine opens, so their canonical colimit maps
locally surjectively to `F`. Inclusions make the map monic, hence an isomorphism.
2. A section on an affine etale chart has a closed nonvanishing locus. Its points map
into the closed-point support of `F` (`def-kun-support`, with independence given by
`lem-kun-support-geometric-point-independent`). The residue fields upstairs are finite
extensions of those downstairs (`lem-weil-pbc-etale-residue-field-extension-separable`
and finite presentation). By `lem-kun-closed-point-field` these are finite over the
base field. The affine chart is quasi-compact over the Noetherian scheme `X`, hence of
finite type over the base by `lem-kun-etale-lfp`. Its nonvanishing locus consists of
closed points, so is finite by `lem-kun-finite-closed-subscheme`. The support of the cyclic
subsheaf is its finite image downstairs, by the stalk description of the generator.
3. A finite sum of cyclic subsheaves has support the finite union of their supports.
For the reduced closed immersion on this finite set, `lem-kun-04ca` identifies the
subsheaf with the direct image of its inverse-image restriction. -/
theorem closedPointSheaf_filteredColimit_finiteSupport
    {K : Type v} [Field K] [IsSepClosed K] (X : Scheme.{v})
    [X.Over (Spec (.of K))] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    [QuasiCompact (X ↘ Spec (.of K))]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hF : etaleSheafSupport F ⊆ {x | IsClosed ({x} : Set X)}) :
    let P : ObjectProperty (Subobject F) := IsFinitelyGeneratedEtaleSubsheaf
    IsFiltered P.FullSubcategory ∧
      (∃ (c : Cocone (P.ι ⋙ Subobject.underlying)) (e : c.pt ≅ F),
        Nonempty (IsColimit c) ∧ ∀ G : P.FullSubcategory,
          c.ι.app G ≫ e.hom = G.obj.arrow) ∧
      ∀ G : Subobject F, IsFinitelyGeneratedEtaleSubsheaf G →
        (etaleSheafSupport (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})).Finite ∧
        etaleSheafSupport (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ⊆
          {x | IsClosed ({x} : Set X)} ∧
        ∃ (Z : Scheme.{v}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsReduced Z),
          Set.range i.base =
            etaleSheafSupport (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ∧
          Nonempty ((G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) ≅
            (Etale.lowerStar AddCommGrpCat.{v + 1} i).obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} i).obj
                (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))) := by
  sorry

end AlgebraicGeometry.Scheme
