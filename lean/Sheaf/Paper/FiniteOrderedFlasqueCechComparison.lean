/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.FirstQuadrantTotalComparison

/-!
# Finite ordered Čech comparison for flasque resolutions

Source: Stacks Project, Cohomology, Tags 09SZ, 01ET, 01EQ, 01FJ and 01FM.
(blueprint: lem-weil-pbc-finite-ordered-flasque-cech-comparison)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite ordered Čech comparison, including componentwise naturality.
Source: Stacks Project, Cohomology, Tags 09SZ, 01ET, 01EQ, 01FJ and 01FM.
(blueprint: lem-weil-pbc-finite-ordered-flasque-cech-comparison)

Proof: Write each nonempty subset in increasing order. Two successive face deletions
cancel with opposite signs. Restrictions commute with the resolution differential,
so the double complex commutes and its total differential is d_h + (-1)^p d_v.
Global restriction and the coefficient augmentation therefore give cochain maps.
For a flasque sheaf, prove positive ordered Čech exactness by induction on the number
of opens. Subtract a boundary on the first r-1 opens. The residual cocycle is supported
on subsets containing the last index. On the intersections with the last open use
induction in degrees above one. In degree one glue the residual sections on their
union, then extend to the last open by flasqueness. Degree zero is sheaf gluing.
Thus every augmented horizontal row is a quasi-isomorphism. Apply
lem-sc-first-quadrant-total-column-comparison to the row augmentation to obtain alpha.
Each vertical column augmentation is a finite product of the stipulated section
quasi-isomorphisms: cycles and boundaries are computed coordinatewise. Transpose
both double complexes and apply the same total comparison. The sign (-1)^(pq)
identifies the transposed total with the original one, giving beta; it is one on q=0.
The degree-zero composites agree by naturality of the coefficient augmentation.
For a supplied coefficient and cochain map into a pushforward, apply its section maps
to every ordered tuple. Naturality commutes with each face restriction, the cochain
identity commutes with the vertical differential, and compatibility with augmentation
gives the beta square. Restriction of global sections gives the alpha square.
Pushforward sections over V are exactly sections over h inverse V, so the target
expressions below are the inverse-image-cover expressions, with scalars restricted
from the target global ring. Identity morphisms give coefficient naturality; open
immersions give restriction naturality. No flatness is used. Apply the assertion
again on Y when the hypotheses there hold. If r=0 the covering condition forces X
empty, and every source and product is zero by the empty-cover sheaf axiom. -/
theorem finiteOrderedFlasqueCechComparison
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (.up ℤ) 0).obj F ⟶ G)
    [QuasiIso e] [G.IsStrictlyGE 0]
    (hfl : ∀ q : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (G.X (q : ℤ))))
    (r : ℕ) (V : Fin r → X.Opens) (hcover : iSup V = ⊤)
    (hsections : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      QuasiIso (((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj
          (op (alternatingCechIntersection V t))).mapHomologicalComplex (.up ℤ)).map e)) :
    QuasiIso (alternatingCechAugmentationMap V G) ∧
    ∃ β : (alternatingCechModuleFunctor V).obj F ⟶ (alternatingCechTotalFunctor V).obj G,
      (∀ n : ℤ, β.f n = ((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
        ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) n 0 n (Int.add_zero n)) ∧
      QuasiIso β ∧
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (e.f 0) ≫
          (alternatingCechAugmentationMap V G).f 0 = alternatingCechZero V F ≫ β.f 0 ∧
      ∀ (Y : Scheme.{u}) (h : Y ⟶ X) (F' : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (G' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (e' : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (.up ℤ) 0).obj F' ⟶ G') [QuasiIso e'] [G'.IsStrictlyGE 0]
        (u : F ⟶ ((Scheme.Modules.pushforward h).obj F'))
        (v : G ⟶ (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G')),
        e.f 0 ≫ v.f 0 = u ≫ (Scheme.Modules.pushforward h).map (e'.f 0) →
        ∃ β' : (alternatingCechModuleFunctor V).obj ((Scheme.Modules.pushforward h).obj F') ⟶
            (alternatingCechTotalFunctor V).obj
              (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G'),
          (∀ n : ℤ, β'.f n =
            ((alternatingCechModuleFunctor V).map
              ((Scheme.Modules.pushforward h).map (e'.f 0))).f n ≫
            ((alternatingCechDoubleFunctor V).obj
              (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G')).ιTotal
              (.up ℤ) n 0 n (Int.add_zero n)) ∧
          β ≫ (alternatingCechTotalFunctor V).map v =
            (alternatingCechModuleFunctor V).map u ≫ β' ∧
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (.up ℤ)).map v ≫ alternatingCechAugmentationMap V
              (((Scheme.Modules.pushforward h).mapHomologicalComplex (.up ℤ)).obj G') =
              alternatingCechAugmentationMap V G ≫ (alternatingCechTotalFunctor V).map v := by
  sorry

end AlgebraicGeometry
