/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceDerivedTensorPullback
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import WeilConjectures.TraceFormula.SpaceQCSeparatedEtaleLocal
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.SpaceQuasiCompactAffineTests

/-! # Countable hypercohomology with a perfect factor on an algebraic space

Source: Stacks Project, Derived Categories of Spaces, Tag 0CRU,
`lemma-countable-cohomology`, hypercohomology assertion
(blueprint: lem-sfb-space-countable-hypercohomology).

The existing small affine ringed model preserves the original module universe.
Cohomology sheaves are transported back through its recorded restriction equivalence
before their sections on arbitrary affine etale charts are tested.
Degree i hypercohomology is the recorded zeroth hypercohomology of the i-shift.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u wX wU

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Tensoring with a perfect object preserves countability of hypercohomology on qcqs
etale spaces over a qcqs algebraic space, for arbitrary unbounded quasi-coherent inputs.
Source: Stacks Project, Derived Categories of Spaces, Tag 0CRU
(blueprint: lem-sfb-space-countable-hypercohomology).

Proof:
1. Fix the perfect P. For a qcqs etale T over X, let C(T) mean countability of every
   hypercohomology group of the restriction of K tensor P. By
   lem-sfb-space-derived-etale-chart-calculus restriction is exact, commutes with
   cohomology and composes. The canonical comparison of
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback identifies the restricted tensor
   with the tensor of the restrictions. The finite-free retract models for perfectness
   restrict to the pulled-back covers, so the restriction of P is perfect. On affine T,
   the hypothesis gives countable cohomology sections of the restriction of K.
   Apply lem-sfb-affine-countable-perfect-tensor, including for the empty affine.
2. On an elementary distinguished square (A subset W, B to W), set D = A times_W B.
   Apply lem-sfb-space-derived-hom-mayer-vietoris with first input the structure sheaf
   and second input (K tensor P)|W. By lem-sfb-ringed-hypercohomology-shifted-unit,
   with base ring the integers, the relevant shifted Hom groups are hypercohomology.
   This gives an exact segment H^(n-1)(D,F) to H^n(W,F) to H^n(A,F) plus H^n(B,F),
   without any boundedness assumption on F. Restriction composition identifies these
   groups with those in C.
3. If C(A), C(B), C(D) hold, the kernel in the middle group is an image of a countable
   group. The quotient embeds in the countable finite direct sum. Representatives of
   its countably many cosets give a surjection from a product of two countable sets
   onto H^n(W,F). Thus C(W) holds. Apply
   lem-sfb-space-qcqs-distinguished-square-induction using step 1 and this gluing step.
4. The source U of the stated qcqs etale morphism is qcqs. Indeed,
   lem-sfb-qc-space-affine-etale-atlas and the continuous surjection of point spaces
   from an etale atlas identify point-space compactness with the atlas criterion;
   lem-sfb-space-quasicompact-affine-tests identifies scheme and space tests.
   Since X is quasi-compact and v is quasi-compact, U is quasi-compact. Apply
   lem-sfb-space-change-base-to-integers and lem-sfb-space-qcqs-source-products to
   obtain absolute quasi-separatedness of U from that of X and v. Step 3 now applies
   to U. The small ringed-model equivalences preserve the cohomology sections,
   tensor and derived sections, so this is precisely the displayed countability.
   No truncation or boundedness of K is used. -/
theorem countable_hypercohomology_tensor_perfect
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{wX} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (K : X.DerivedModules) (hK : X.derivedQCohProperty K)
    (hcount : ∀ (j : ℤ) (V : X.EtaleSite), IsAffine (X.etaleForget.obj V) →
      Countable (((X.smallModuleEquivalence.inverse).obj
        ((DerivedCategory.homologyFunctor X.SmallModules j).obj K)).val.obj (op V)))
    (U : AlgebraicSpace S) [HasDerivedCategory.{wU} U.SmallModules] (v : U ⟶ X)
    (hvet : IsEtale v.hom.hom) (hvqc : IsQuasiCompactPresheafMap v.hom.hom)
    (hvqs : IsQuasiCompactPresheafMap (diagonalPresheafMap v.hom.hom))
    (P : X.DerivedModules)
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, wX}
      X.smallStructureSheaf P) (i : ℤ) :
    Countable ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, wU}
      U.smallEtaleModelTopology U.smallStructureSheaf).obj
        (((derivedTensorPullback.{u, wX, wU} v).obj
          ((X.derivedDualityModel.closed.tensor).obj (K, P)))⟦i⟧)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
