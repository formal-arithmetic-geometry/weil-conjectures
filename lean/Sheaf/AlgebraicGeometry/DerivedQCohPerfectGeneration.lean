/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectLocalizingClosure

/-! # Perfect complexes generate the quasi-coherent derived category

Source: literature/stacks-project/derived-categories-of-schemes.tex, Theorem
perfect-theorem-bondal-van-den-Bergh (blueprint: lem-pc-derived-qcoh-perfect-generation).
-/

@[expose] public section

universe u1 w1

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For every quasi-compact and quasi-separated scheme, the localizing closure of all perfect
complexes is the whole quasi-coherent derived category
Source: Stacks Project, Theorem 09IS (perfect-theorem-bondal-van-den-Bergh),
with Derived Categories, Lemma 09SN (lemma-write-as-colimit).
(blueprint: lem-pc-derived-qcoh-perfect-generation).

Proof:
1. On an affine scheme, the structure sheaf is a perfect generator detecting zero by
   all shifted Hom groups (`lem-pc-perfect-generation-affine-base`, Tags 09IS and 06Z0).
2. For an open cover by a quasi-compact open U and an affine open V, extend a perfect
   generator from U and add a perfect Koszul object supported on V minus U. Their sum
   is perfect and detects zero (`lem-pc-perfect-generation-open-induction-step`).
3. Apply the qcqs open-cover induction principle (`lem-sc-invert-s-cohomology-induction`,
   Tag 08DR) to the property of having a perfect generator, obtaining such a G on X.
4. The category has direct sums (`lem-pc-derived-qcoh-direct-sums`) and G is compact
   (`lem-pc-perfect-object-compact`). The singleton family G generates in the sense of
   `def-pc-generators`. By `lem-pc-compact-generators-build-objects` (Tag 09SN), every Y
   is a homotopy colimit: the first stage and the attaching objects are direct sums of
   shifts of G, successive stages are cones, and Y is the cone of a map between sums
   of the stages. Every stage and then Y lie in the stated closure. Thus it is all
   of the quasi-coherent derived category. -/
theorem derivedQCohPerfectGeneration (X : Scheme.{u1}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w1} (SheafOfModules.{u1} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w1} (SheafOfModules.{u1} ((moduleRings X.toRingedSpace).over U))] :
    perfectLocalizingClosure X = (⊤ : ObjectProperty (schemeDerivedQCohCategory X)) := by
  sorry

end AlgebraicGeometry
