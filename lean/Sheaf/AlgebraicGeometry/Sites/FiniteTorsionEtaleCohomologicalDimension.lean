/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.EtaleSupport
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.Paper.HigherDirectImageSheafifiedPresheaf
import Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Finiteness of torsion étale cohomological dimension

Source: Stacks Project, Tag 0F10, Lemma 59.96.2; blueprint sec-smooth-purity,
sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0f10).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism over a field between finite-type schemes has finite torsion étale
cohomological dimension; over a separably closed field each such scheme has finite dimension.
Source: Stacks Project, Tag 0F10 (blueprint: lem-kun-0f10).

Proof plan:
1. Finite-type schemes over a field are Noetherian and qcqs, as are their opens.
   This uses finite-type algebra Noetherianity, affine Noetherianity, the affine-cover
   quasi-separatedness criterion and finite type of quasi-compact open immersions.
2. Localize the étale Mayer–Vietoris sequence over each étale object of the target.
   Pullback compatibility, exact sheafification and the sheafified-presheaf description
   of higher direct images give the relative exact segment in Tag 0EYK.
3. Over an affine target V, an affine open W of its preimage maps affinely over K to V.
   Finite dimension and the dimension formula give E_d(W) = W for some d.
   The affine direct-image support bound makes R^q vanish for q > d, by
   conservativity of geometric stalks. The empty affine has bound zero.
4. Apply quasi-compact-open induction. Bounds a, b, c on A, B, A ∩ B give
   max(a,b,c+1) on A ∪ B via step 2. Restrictions remain torsion by the
   local-section characterization of torsion sheaves.
5. Choose a finite affine cover of Y and take the maximum of its bounds.
   Étale neighbourhoods contained in a chosen open are cofinal, so the stalk criterion
   transfers these bounds to f. Empty Y has bound zero. This proves clause (1).
6. A separably closed point has torsion dimension zero. The affine torsion dimension
   theorem gives finite bounds for affine finite-type schemes over K. Absolute
   Mayer–Vietoris and the same quasi-compact-open induction prove clause (2).
The dependency nodes in the recorded proof supply these six steps. -/
theorem torsionEtaleCohomologicalDimension_finite_of_finiteType
    (K : Type u) [Field K]
    (X Y : Scheme.{u}) [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] :
    (@Scheme.Hom.torsionEtaleCohomologicalDimension _ _ f
      (@quasiCompact_of_compactSpace X Y f
        ((quasiCompact_iff_compactSpace (X ↘ Spec (.of K))).mp inferInstance)
        (@IsLocallyNoetherian.quasiSeparatedSpace Y
          (LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K)))))
      (@QuasiSeparated.of_quasiSeparatedSpace X Y f
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K)))))) < ⊤ ∧
    (IsSepClosed K →
      (@Scheme.torsionEtaleCohomologicalDimension X
        ((quasiCompact_iff_compactSpace (X ↘ Spec (.of K))).mp inferInstance)
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))))) < ⊤) :=
  sorry

end AlgebraicGeometry
