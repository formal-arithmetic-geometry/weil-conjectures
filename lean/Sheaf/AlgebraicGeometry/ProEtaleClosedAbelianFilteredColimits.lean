/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

import Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-! Filtered-colimit comparison for abelian pro-etale closed direct image. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Abelian closed direct image commutes with filtered colimits on a qcqs base.
Source: Stacks Project, Tags 0738 (4) and 098D
(blueprint: lem-weil-pbc-proetale-closed-abelian-filtered-colimits).

Proof: The canonical comparison is tested on affine objects `V` over the base.
Both `V` and its closed fibre `V_Z` are qcqs. Use localization at these objects
to identify evaluation with global sections on their pro-etale sites. Localization
is inverse image and preserves colimits. By the sections clause of the qcqs section
calculus, these global sections commute with the filtered colimit. The direct-image
formula evaluates a sheaf at `V_Z`; thus both sides of the comparison at `V` identify
with the same colimit of groups of sections at `V_Z`. The comparison is the identity
under these identifications, since all identifications respect coprojections.
Affine objects form a covering basis, so these sectionwise inverses give an inverse
of the sheaf comparison. This proves preservation of the given diagram shape. -/
theorem proEtale_closed_abelian_filteredColimits {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}) := by
  sorry

end AlgebraicGeometry.Scheme
