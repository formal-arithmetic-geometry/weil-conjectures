/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction
public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
public import Sheaf.AlgebraicGeometry.SpaceQcqsDistinguishedSquareInduction
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Derived coherator descent on an elementary distinguished square

Source: Stacks Project, Derived Categories of Spaces, Tag 0CR6
(remark-explain-consequence), using Tags 08GW and 0CR5
(blueprint: lem-sfb-space-coherator-distinguished-square-triangle).

All four derived categories use the existing equivalent small ringed models.
On these étale maps, the existing total derived pullback is canonically exact
restriction by `spaceEtaleDerivedRestriction_existsUnique`. Naturality of every
arrow is expressed by a natural transformation on the entire unbounded category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.AlgebraicSpace

/-- The derived coherators give a natural distinguished triangle on an elementary
square, without any boundedness or quasi-coherence assumption on the input.
The two components of the first arrow, the two signed components of the second,
and the boundary are natural transformations. All coherators are followed by the
actual full inclusions, and direct image is the canonical K-injective derived image.

Source: Stacks Project, Derived Categories of Spaces, Tag 0CR6; Tags 08GW and 0CR5
(blueprint: lem-sfb-space-coherator-distinguished-square-triangle).

Proof:
1. The quasi-compact scheme atlases make all four point spaces quasi-compact by
   lem-a1-space-finite-affine-subatlas. Absolute quasi-separatedness and
   lem-sfb-space-qcqs-permanence make each of j_U, j_V and j_T qcqs. The adjoints
   supplied by lem-sfb-space-derived-coherator-adjunction are triangulated.
2. Apply lem-sfb-space-relative-mv-exchange-triangles to the identity of W and
   arbitrary E. The unital comparison of lem-sfb-space-derived-etale-chart-calculus
   identifies its first term with E. This gives E -> B -> C -> E[1], where
   B = Rj_U E_U plus Rj_V E_V and C = Rj_T E_T. The second map is the difference
   of the two restrictions. This construction is natural on all unbounded complexes.
3. Apply the triangulated DQ_W and the full inclusion. Additivity identifies the
   image of B with the biproduct of the images of its two summands. The boundary
   uses the canonical shift comparison of the right adjoint.
4. By lem-sfb-space-derived-pushforward-coproducts each Rj preserves quasi-coherent
   cohomology. Exact restriction preserves it by the chart calculus. For P in
   D_QCoh(W) and L in D(A), the coherator and restriction/image adjunctions identify
   Hom(P,DQ_W Rj L) with Hom(j*P,L), and with Hom(P,Rj DQ_A L).
   Thus det-sp-unique-right-adjoint gives the counit-compatible natural comparison
   DQ_W Rj = Rj DQ_A, as in Tag 0CR5.
5. Use these three comparisons and the biproduct comparison to transport the
   triangle of step 3. The identity on its first vertex and the comparisons on
   its other vertices form a triangle isomorphism. Invariance under isomorphism
   in def-weil-triangulated-category proves distinguishedness. Every comparison
   and the original triangle are natural, giving the five natural transformations
   below. Empty opens, zero objects and unbounded complexes require no exception. -/
theorem exists_coherator_distinguishedSquare_triangle
    {S : Scheme.{u}} (W U V T : AlgebraicSpace S)
    (j : U ⟶ W) (p : V ⟶ W) (a : T ⟶ U) (b : T ⟶ V)
    (hsq : IsPullback a b j p)
    (hj : ∃ A : OpenSubspace W,
      ∃ e : U.obj.obj ≅ A.val.toFunctor, e.hom ≫ A.val.ι = j.hom.hom)
    (hp : IsEtale p.hom.hom)
    (Z : ClosedSubspace W) (hZ : IsReduced (Z.val : AlgebraicSpace S))
    (hZsupport : pointImage Z.val.arrow.hom.hom = (pointImage j.hom.hom)ᶜ)
    (hcomplement : IsIso (Limits.pullback.snd p.hom Z.val.arrow.hom))
    (hqcqs : ∀ A : AlgebraicSpace S, A = W ∨ A = U ∨ A = V ∨ A = T →
      (∃ (B : Over S) (q : yoneda.obj B ⟶ A.obj.obj),
        CompactSpace B.left ∧ IsEtale q ∧ IsSurjective q) ∧
      IsAbsolutelyQuasiSeparated A)
    [HasDerivedCategory.{w} W.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} V.SmallModules] [HasDerivedCategory.{w} T.SmallModules]
    (DQW : W.DerivedModules ⥤ W.DerivedQCoh)
    (DQU : U.DerivedModules ⥤ U.DerivedQCoh)
    (DQV : V.DerivedModules ⥤ V.DerivedQCoh)
    (DQT : T.DerivedModules ⥤ T.DerivedQCoh)
    (adjW : W.derivedQCohProperty.ι ⊣ DQW)
    (adjU : U.derivedQCohProperty.ι ⊣ DQU)
    (adjV : V.derivedQCohProperty.ι ⊣ DQV)
    (adjT : T.derivedQCohProperty.ι ⊣ DQT) :
    ∃ (αU : DQW ⋙ W.derivedQCohProperty.ι ⟶
        spaceDerivedPullback j ⋙ DQU ⋙ U.derivedQCohProperty.ι ⋙ derivedDirectImage j)
      (αV : DQW ⋙ W.derivedQCohProperty.ι ⟶
        spaceDerivedPullback p ⋙ DQV ⋙ V.derivedQCohProperty.ι ⋙ derivedDirectImage p)
      (βU : spaceDerivedPullback j ⋙ DQU ⋙ U.derivedQCohProperty.ι ⋙
          derivedDirectImage j ⟶
        spaceDerivedPullback (a ≫ j) ⋙ DQT ⋙ T.derivedQCohProperty.ι ⋙
          derivedDirectImage (a ≫ j))
      (βV : spaceDerivedPullback p ⋙ DQV ⋙ V.derivedQCohProperty.ι ⋙
          derivedDirectImage p ⟶
        spaceDerivedPullback (a ≫ j) ⋙ DQT ⋙ T.derivedQCohProperty.ι ⋙
          derivedDirectImage (a ≫ j))
      (δ : spaceDerivedPullback (a ≫ j) ⋙ DQT ⋙ T.derivedQCohProperty.ι ⋙
          derivedDirectImage (a ≫ j) ⟶
        DQW ⋙ W.derivedQCohProperty.ι ⋙ shiftFunctor W.DerivedModules (1 : ℤ)),
      ∀ E : W.DerivedModules,
        Triangle.mk (biprod.lift (αU.app E) (αV.app E))
          (biprod.desc (βU.app E) (βV.app E)) (δ.app E) ∈ distTriang W.DerivedModules := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
