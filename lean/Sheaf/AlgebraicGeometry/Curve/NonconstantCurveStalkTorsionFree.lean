/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sober

import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Topology.KrullDimension

/-!
# Torsion-free stalks for nonconstant morphisms to integral curves

Source: Stacks Project, `curves.tex`, Tag 0CCK, proof of lemma-flat, and
`morphisms.tex`, Tag 0CC1, lemma-dominant-between-integral, (2) implies (6).
(blueprint: lem-a1-nonconstant-curve-stalk-torsion-free).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism from an integral scheme to an integral curve with at least two image points
maps generic point to generic point, has dense image, and induces injective homomorphisms
of domain stalks. The last clause is torsion-freeness for the scalar action
`a • b = (f.stalkMap x) a * b`.

Source: Stacks Project, `curves.tex`, Tag 0CCK, proof of lemma-flat, and
`morphisms.tex`, Tag 0CC1, lemma-dominant-between-integral, (2) implies (6).
(blueprint: lem-a1-nonconstant-curve-stalk-torsion-free).

Proof:
1. The source and target are integral, hence nonempty and irreducible, with unique generic
   points by `lem-sc-scheme-sober`. The target has topological dimension one: the local-ring
   convention in `def-pc-dimension` agrees with topological dimension by
   `lem-pc-scheme-dimension-local-rings`.
2. Put z = f(eta_X). Continuity places the whole image in the closure of z. If z is not
   eta_Y, that closure is proper and irreducible. Any distinct specialization w of z would
   give the strict chain closure(w) < closure(z) < Y, contradicting dimension one
   (`def-kun-topological-krull-dimension`, `def-sc-generic-point`). Thus closure(z) is a
   singleton, contradicting the two-point image hypothesis. Hence z = eta_Y, and the image
   is dense because it contains the generic point of Y.
3. By `lem-sc-integral-scheme-stalks-in-function-field`, all stalks of X and Y are domains
   embedding in their generic stalk fields. Step 2 makes the generic stalk map a unital
   homomorphism between fields, hence injective: a nonzero element has an inverse, so its
   image cannot be zero.
4. For x in X and y = f(x), the square formed by the stalk map and the two embeddings in
   generic stalks commutes. Represent a germ by a section s on a neighbourhood W of y.
   Both composites give the germ of its pullback at eta_X; eta_Y lies in W and eta_X in
   its inverse image. This uses `def-weil-pbc-module-stalk` and
   `def-weil-locally-ringed-space-morphism`. The composite through the generic stalk of Y
   is injective, so the stalk map at x is injective.
5. For a nonzero a in the target stalk, its image is nonzero by Step 4. Since the source
   stalk is a domain, (f.stalkMap x)(a) * b = 0 forces b = 0. This is precisely
   torsion-freeness for the stated scalar action, at every x.
-/
theorem Scheme.Hom.nonconstant_curve_stalk_torsion_free {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] (sY : Y ⟶ Spec (.of k)) [IsIntegralCurve sY]
    (f : X ⟶ Y) (h_nonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) :
    f (genericPoint X) = genericPoint Y ∧ DenseRange f ∧
      ∀ x : X, IsDomain (Y.presheaf.stalk (f x)) ∧ IsDomain (X.presheaf.stalk x) ∧
        Function.Injective (f.stalkMap x) ∧
        ∀ (a : Y.presheaf.stalk (f x)) (b : X.presheaf.stalk x),
          a ≠ 0 → (f.stalkMap x) a * b = 0 → b = 0 := by
  sorry

end AlgebraicGeometry
