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
import Sheaf.AlgebraicGeometry.ClosedPointSheafFilteredColimit
import Sheaf.AlgebraicGeometry.ClosedPointSheafFiniteSupport

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
1. The filtered-colimit theorem constructs the diagram of finitely generated subsheaves.
Finite unions of generators give common successors, and affine charts make the canonical
map to `F` locally surjective. Exact filtered colimits make it monic.
2. For each generator its closed nonvanishing locus in a Noetherian affine chart has
finitely many generic points. Their images belong to the closed-point support of `F`,
so specialization forces the entire image to be finite. On the complement of the finite
union of these images all generators vanish. Minimality puts the generated subsheaf in
the kernel of restriction, proving that its support is finite.
3. Give this finite set of closed points its reduced closed subscheme structure.
The closed-immersion essential-image theorem identifies the subsheaf with the direct
image of its inverse-image restriction. -/
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
  dsimp
  have hcol := closedPointSheaf_finitelyGenerated_filteredColimit (K := K) X F hF
  refine ⟨hcol.1, hcol.2, ?_⟩
  exact closedPointSheaf_finitelyGenerated_finiteSupport (K := K) X F hF

end AlgebraicGeometry.Scheme
