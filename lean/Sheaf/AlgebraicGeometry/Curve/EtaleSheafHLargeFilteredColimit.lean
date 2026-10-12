/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Continuity of Ext cohomology for large filtered diagrams -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Ext sheaf cohomology preserves filtered colimit cocones indexed in `Type (u + 1)`.
Source: Stacks Project, Tags 03Q5 and 0739; comparison with Ext, Tags 015A and 05TI.
(blueprint: lem-pbc-u2-sheafH-large-filtered-colimit)

Proof: Use the qcqs etale objects and their finite covers. Sections on these objects
commute with filtered colimits, as every section and every finite compatibility
relation appears at a stage. This argument works in the coefficient universe u+1,
including a diagram with object and morphism types in that universe. Embed the diagram
functorially into injectives and take its cokernel diagram. Filtered colimits are exact.
The Cech complexes of the colimit of injectives are filtered colimits of their Cech
complexes, because the covering products are finite. Exactness and injective Cech
acyclicity give vanishing in positive degrees for this colimit, by the Cech vanishing
criterion. Induction with the natural long exact sequences and the five lemma now
proves continuity in each degree. Finally use the natural comparison between Ext from
the constant integer sheaf and derived global sections, computed on the same injective
resolutions. The comparison identifies every leg, hence gives the displayed colimit
property, including degree zero, empty schemes and zero sheaves. -/
theorem sheafH_isColimit_large_filtered
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cocone D} (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit ((Sheaf.functorH X.smallEtaleTopology q).mapCocone c)) := by sorry

end AlgebraicGeometry.Scheme
