/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.ProjectionMateExact
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.SfCommonStageWeilCohomology

/-! # Finite truncation windows for derived tensor

Source: Stacks Project, Cohomology on Sites, Tag 094H, first equality in the proof,
with the cutoffs depending on the opposite factor's upper cohomological bound
(blueprint: lem-weil-pbc-derived-tensor-truncation-window).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules


attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A fixed cohomology degree of derived tensor depends only on the two indicated
finite good-truncation windows. The comparison is the bifunctor image of the canonical
maps, so `IsIso` asserts invertibility of that particular module-sheaf morphism.
Source: Stacks Project, Tag 094H, corrected finite-window reduction; Tags 0118 and 06YU
(blueprint: lem-weil-pbc-derived-tensor-truncation-window).

Proof:
1. Put A = tau_{<=a-1} K, B = tau_{<=c-1} L, K+ = tau_{>=a} K,
   L+ = tau_{>=c} L. Good-truncation cohomology gives the asserted windows, including
   empty intervals (`def-kun-truncations`, `def-weil-abstract-derived-category`).
2. Good upper truncation gives representatives of A,L,K+,B with terms zero above
   a-1,bL,bK,c-1. Choose flat K-flat replacements preserving these upper bounds
   (`lem-pc-kflat-bounded-flat-replacement`, `lem-pc-bounded-above-flat-kflat-site`).
   Tensor descent identifies their total tensors with the derived tensors
   (`lem-weil-pbc-site-derived-tensor-descent`).
3. A summand in total degree n requires p+q=n. Thus A tensor L is zero in terms
   above a-1+bL, and K+ tensor B above bK+c-1 (`def-pc-tensor-complex-sheaves`).
   Both bounds are strictly below i. Their cohomology in i and i+1 vanishes
   (`def-weil-derived-cohomology-sheaves`).
4. Tensor the truncation triangle A -> K -> K+ with L
   (`lem-sf-derived-truncation-triangle`, separate tensor exactness from
   `lem-weil-pbc-ringed-projection-mate-exact`). Its long exact cohomology sequence
   (`lem-sf-derived-homology-long-exact`) has zero outside terms in i and i+1,
   making H^i(K tensor L) -> H^i(K+ tensor L) an isomorphism.
5. Tensor B -> L -> L+ on the left by K+. The same argument gives the second
   isomorphism. Their composite is the bifunctor image of both truncation maps.
   This uses no points, local constancy, Noetherianity or finiteness hypothesis. -/
theorem isIso_derivedTensor_truncationWindow
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (K L : DerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (bK bL : ℤ)
    (hK : ∀ q : ℤ, bK < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hL : ∀ q : ℤ, bL < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj L))
    (i a c : ℤ) (ha : a ≤ i - bL) (hc : c ≤ i - bK) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((wfSiteDerivedTensor J R).map
        (CategoryTheory.Prod.mkHom ((DerivedCategory.TStructure.t.truncGEπ a).app K)
          ((DerivedCategory.TStructure.t.truncGEπ c).app L)))) ∧
    (∀ q : ℤ, q < a ∨ bK < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj K))) ∧
    (∀ q : ℤ, q < c ∨ bL < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncGE c).obj L))) := by
  sorry

end SheafOfModules
