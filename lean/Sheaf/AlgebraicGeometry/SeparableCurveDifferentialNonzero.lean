module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Sheaf.FieldTheory.FieldTower
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Nonvanishing of the differential of a separable curve morphism

Source: Stacks Project, Curves, Tag 0C1C, implication (5) implies (1).
(blueprint: lem-sfb-separable-curve-differential-nonzero)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Finite separability of the induced function-field extension makes the canonical
relative differential map nonzero. The source structure map is the composite `f ≫ g`;
thus `f` is a morphism over `k`. The function-field algebra is induced by `f`, as specified
by its compatibility with the canonical generic-point inclusions in `hfield`.

Source: Stacks Project, Curves, Tag 0C1C, implication (5) implies (1).
(blueprint: lem-sfb-separable-curve-differential-nonzero)

Proof:
1. Dominance sends the generic point of X to that of Y. The induced local-ring map
   is the given map k(Y) → k(X). On a nonempty affine open Spec A in either curve,
   its function field is Frac A by lem-sc-integral-function-field-affine-fraction.
2. Each curve has dimension one everywhere by lem-sc-dimension-locally-algebraic.
   Its smooth structure map therefore has relative dimension one, so
   lem-sc-smooth-omega-finite-locally-free makes its relative differentials locally
   free of rank one (def-amb-finite-locally-free-module). In particular the generic
   stalk of Ω_X/k is a nonzero one-dimensional vector space over k(X).
3. The affine description of def-sc-relative-differential-sheaf, the stalk formula
   lem-weil-pbc-spec-tilde-stalk-localization, and
   lem-weil-pbc-kahler-differentials-localization identify the generic stalks with
   Ω_k(Y)/k and Ω_k(X)/k, sending the germ of da to d(a/1).
4. By lem-weil-pbc-module-stalk-pullback the generic stalk of the source of df is
   k(X) ⊗[k(Y)] Ω_k(Y)/k. The generator formula of
   def-a1-relative-differentials-pullback-map sends a ⊗ db to a db. Indeed b has a
   regular representative near the generic point, and the map sends its pulled-back
   differential to the differential of its image. The db generate the differential
   module (def-weil-pbc-kahler-differentials), so this describes the whole stalk map.
5. Finite separability and lem-weil-pbc-separable-algebraic-differentials-base-change
   identify this canonical stalk map with an isomorphism. Its target is nonzero
   by step 2, so the stalk map is nonzero.
6. A zero sheaf morphism induces zero maps on all stalks, contradicting step 5.
-/
theorem relativeDifferentialsPullbackMap_ne_zero_of_finite_separable
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (g : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsIntegralCurve g] [IsIntegralCurve (f ≫ g)]
    [Smooth g] [Smooth (f ≫ g)] [IsDominant f]
    [Algebra Y.functionField X.functionField]
    (hfield : Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
      Y.fromSpecFunctionField = X.fromSpecFunctionField ≫ f)
    [Module.Finite Y.functionField X.functionField]
    [Algebra.IsSeparable Y.functionField X.functionField] :
    g.relativeDifferentialsPullbackMap f ≠ 0 := by
  sorry

end AlgebraicGeometry
