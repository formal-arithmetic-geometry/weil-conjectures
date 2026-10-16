/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement
import Sheaf.AlgebraicGeometry.FibreProductLimit
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.CategoryTheory.ExistsDirectedReindexing
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections

/-!
# Descent of finite affine comparison Čech cocycles

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions in condition (3).
(blueprint: lem-cbc-affine-comparison-cech-cocycle-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- A comparison Čech cocycle with arbitrary étale sheaf coefficients comes from an
étale Čech cocycle by a morphism of complexes for a finite étale covering.
No injectivity, exactness or primitive is asserted.
Source: Stacks Project, Tag 099U, condition (3), the two finite Čech limit reductions;
Tag 099T for section continuity and Tags 01ZM, 01ZN, 07RP for finite étale descent.
(blueprint: lem-cbc-affine-comparison-cech-cocycle-descent).

Proof:
1. The one-factor nerve hypothesis identifies each U_i with an affine ind-étale
   Y-object. Ind-étale cancellation shows U_i -> V is ind-étale. Present these maps
   by affine étale V-schemes and use the finite product of their directed indices.
   Repeated fibre products are the limits of the corresponding stage products.
2. Comparison section continuity, in degrees q+1 and q+2, identifies each section
   group on these limits with the filtered colimit of stage sections. There are
   only finitely many tuples in either degree. Choose representatives at a common
   stage. The stage families cover V since the original family factors through
   them and is jointly surjective. Each component of the differential vanishes
   eventually, since it vanishes at the limit. A common later stage kills all these finitely many
   components. This gives a cocycle for a finite affine étale family over V.
3. Present V by affine étale Y-schemes V_b. Finite presentation descends the finite
   affine étale family to some V_b. Descend the target identification and its
   inverse, and increase b until both inverse identities hold; thus the family
   has exactly the chosen target V_b. On a cofinal tail it pulls back to the given
   family. Increase b until the descended finite family is covering; this is
   finite covering descent. Its repeated intersections and face projections
   pull back as well.
4. Apply comparison section continuity to these intersections. As in step 2,
   descend the finitely many cocycle components to one b and kill their finitely
   many differential components at a later b. At étale Y-objects the comparison
   unit identifies these sections with those of the original sheaf J.
5. The family maps to the two chosen stages induce maps on all nerve products.
   Apply the comparison unit followed by restriction to obtain additive maps on
   cochains. The projection equations imply commutation with every face; summing
   with the alternating signs proves commutation with the differential. Their
   composite is φ and sends the descended cocycle to c. The categorical product
   complex at the stage is identified with the dependent-function complex by
   the product universal property, compatibly with each projection and face.
   Reindexing by ULift preserves the family and its Čech complex.
   For n=0 all cochain groups are zero: take W to be the empty étale Y-object,
   its empty covering, the zero complex map, and the zero cocycle. Empty schemes,
   singleton families and the zero sheaf satisfy the same construction. -/
theorem exists_etale_cech_cocycle_lift
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      proAffineEtale (Presheaf.cechNerveObj U y).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) (q : ℕ)
    (c : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).X (q + 1))
    (hc : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).d (q + 1) (q + 2) c = 0) :
    ∃ (W : Y.Etale) (T : ULift.{u + 1} (Fin n) → Y.Etale)
      (f : ∀ i, T i ⟶ W),
      Sieve.ofArrows T f ∈ Y.smallEtaleTopology W ∧
      ∃ (φ : (cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj) ⟶
        (Presheaf.cechComplex U).obj
          ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj)
        (c' : ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).X (q + 1)),
        ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).d (q + 1) (q + 2) c' = 0 ∧
          φ.f (q + 1) c' = c := by
  sorry

end AlgebraicGeometry.ProEtale
