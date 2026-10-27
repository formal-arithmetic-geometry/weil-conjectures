/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.SmoothAnalyticData
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Analytification and holomorphic cotangent comparison for smooth complex schemes

Source: Serre, GAGA, nos. 4--6 and 9, with the smooth-coordinate construction specified
in the DAG (blueprint: lem-sfb-smooth-analytification-cotangent).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A separated finite-type smooth complex scheme has its usual analytification, and
scalar extension identifies its structure and cotangent sheaves with their holomorphic
counterparts, with the prescribed formulas. Closed immersions induce closed holomorphic
embeddings. The complex dimensions may vary, and the empty scheme is included.

Source: Serre, GAGA, nos. 4--6 and 9; Stacks, Tags 00TA, 00T6, 00T7, 02H6, 01HR
(blueprint: lem-sfb-smooth-analytification-cotangent).

Proof plan, following the node's ten steps:
1. Finite type gives a finite affine cover. Restrict smoothness to its members
   (lem-pc-open-immersion-smooth-composition), use the smooth affine comparison
   (lem-weil-pbc-smooth-ring-map-iff-smooth-affine), and refine to principal standard-smooth
   presentations (lem-weil-pbc-smooth-ring-map-locally-standard-smooth,
   def-weil-pbc-standard-smooth-algebra).
2. For the presentation with c relations in n variables apply the analytic inverse theorem
   to (f_1,...,f_c,z_{c+1},...,z_n). Its derivative has invertible Jacobian block. The last
   n-c coordinates give charts. Use lem-sfb-complex-analytic-inverse-toolkit,
   lem-sfb-complex-analytic-function-operations and lem-sfb-complex-analytic-derivative-rules.
3. Regular functions on principal opens are fractions
   (lem-weil-pbc-affine-open-section-vanishing-prime), hence analytic. Polynomial changes of
   generators and regular fractions on overlaps show that the topology and charts agree.
   The chain rule makes chart transitions analytic and dimensions agree on overlaps.
4. Separatedness and lem-weil-pbc-fibre-product-affine-spectra make the diagonal a common
   zero set of continuous regular functions on products of affine charts. It is closed,
   hence the topology is Hausdorff. Finite affine covers and countable bases of finite
   complex affine spaces give second countability.
5. Map each complex point to its scheme point. Evaluation of local regular fractions
   commutes with restrictions and ring operations, giving the canonical ringed-space map
   (def-weil-locally-ringed-space-morphism).
6. Glue analytic coordinate covectors by the transpose Jacobians. The chain rule proves
   the cocycle law and makes coordinate exterior differentiation well-defined. The
   universal derivation (def-weil-pbc-kahler-differentials) yields compatible maps from
   algebraic differentials (def-sc-relative-differential-sheaf).
7. Extend that map by analytic scalars. The standard-smooth algebraic basis
   (lem-weil-pbc-standard-smooth-kahler-basis) maps to the coordinate covector frame.
   Its inverse sends sum h_j dt_j to sum h_j tensor d_X t_j. These inverses agree on
   overlaps and glue; the map sends 1 tensor d_X a to d_hol(a^an).
8. Multiplication h tensor a maps to h a^an and has inverse h maps to h tensor 1;
   balancing verifies both composites, compatibly with restriction.
9. Affine quotients for a closed immersion identify the point image with a closed zero
   set, with the induced topology. Target regular coordinates pull back holomorphically.
   Lifting source regular coordinates through the quotient shows derivative injectivity.
10. Select target coordinates with an invertible source minor and apply the inverse
    theorem again. The image is a holomorphic graph; subtracting that graph straightens
    it to a coordinate subspace. Zero-dimensional charts and the empty space require
    no nonemptiness assumptions. -/
theorem exists_smoothAnalytification_cotangent {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [Smooth f] :
    ∃ D : SmoothAnalytic.Data f,
      T2Space D.space ∧ SecondCountableTopology D.space ∧
      ∃ (e0 : SmoothAnalytic.analytify D (SheafOfModules.unit X.ringCatSheaf) ≅
          SheafOfModules.unit (moduleRings D.space))
        (e1 : SmoothAnalytic.analytify D f.relativeDifferentials ≅ D.cotangent.omega),
        (∀ (U : X.Opens)
          (h : D.space.presheaf.obj (op ((Opens.map D.pi.hom.base).obj U))) (a : Γ(X, U)),
          e0.hom.val.app _
            (SmoothAnalytic.tensorSection D (SheafOfModules.unit X.ringCatSheaf) U h a) =
              @Mul.mul (D.space.presheaf.obj
                (op ((Opens.map D.pi.hom.base).obj U))) inferInstance h
                (D.pi.hom.c.app (op U) a)) ∧
        (∀ (U : X.Opens) (a : Γ(X, U)),
          e1.hom.val.app _ (SmoothAnalytic.tensorSection D f.relativeDifferentials U 1
            (f.relativeDifferentialsDerivation.d a)) =
              D.cotangent.d _ (D.pi.hom.c.app (op U) a)) ∧
        (∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of (ULift.{u} ℂ))),
          IsSeparated g → LocallyOfFiniteType g → QuasiCompact g → Smooth g →
          ∀ (E : SmoothAnalytic.Data g) (i : Over.mk f ⟶ Over.mk g),
            IsClosedImmersion i.left →
              SmoothAnalytic.IsClosedHolomorphicEmbedding D.atlas E.atlas
                (SmoothAnalytic.mapPoints D E i)) := by
  sorry

end AlgebraicGeometry
