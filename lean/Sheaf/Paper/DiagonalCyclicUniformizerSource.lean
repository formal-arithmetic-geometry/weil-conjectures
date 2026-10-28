/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.DiagonalCoefficientRouteSquare

/-! # The constant-source endpoint of cyclic coefficient continuation

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: lem-diagonal-cyclic-uniformizer-source).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

-- Read the endpoint predicate from the proved criterion's stored type.
-- The emitted signature is its ordinary quantified endpoint formula.
local elab "criterionHypothesis% " i:num f:term:max : term => do
  let e ← Lean.Elab.Term.elabTerm f none
  let mut t ← Lean.Meta.inferType e
  for _ in [:i.getNat] do
    let .forallE _ _ body _ ← Lean.Meta.whnf t
      | throwError "criterion has fewer proof arguments"
    t := body
  let .forallE _ domain _ _ ← Lean.Meta.whnf t
    | throwError "criterion has fewer proof arguments"
  if domain.hasLooseBVars then
    throwError "endpoint predicate depends on an earlier proof"
  return domain

/-- The two ordinary restriction functors have a unique underlying-identity
comparison; its derived mate has the prescribed supported constant endpoint.
There is no equality involving a diagonal arrow in this statement.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), composition of coefficient
extensions and their scalar units; the source normalization in the parent
coefficient-square proof, steps 1 and 2.
(blueprint: lem-diagonal-cyclic-uniformizer-source).

Proof: use the underlying and counit isomorphisms of each inverse finite
realization to identify its underlying abelian sheaf with the given ordinary
module. The two resulting Z_l actions coincide: the coefficient isomorphisms
are unital, hA annihilates l^(n+1), and the induced map from the cyclic quotient
is cartierResidueAlgebra. Equivalently, pull the ring maps to W, factor through
the sheafified cyclic quotient and test on its constant generators. Transporting
the identity between the two underlying sheaves therefore gives a module
isomorphism. Its naturality follows after faithful forgetting, where it is the
naturality of the two underlying isomorphisms. Faithful forgetting also proves
uniqueness. Derive this ordinary comparison and take its mate under the actual
composite scalar adjunctions. Endpoint.normalization says that each supported
endpoint is the adjoint of supportMap of its regular coefficient unit.
FiniteSourceComparison.normalization and FiniteRealization.unit_normalization
identify its finite realization with the ordinary pushed constant unit. The
normalization of maps.source agrees with that unit on every constant section;
sheafification's universal property makes the maps equal. Naturality of exact
single comparisons transports this equality to SourceEquation. These arguments
use no root endpoint or diagonal arrow. For an empty base every map is unique;
for the zero coefficient ring the supported map has zero target. -/
theorem diagonalCyclic_uniformizerSource
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    criterionHypothesis% 0 (UniformizerSquareData.endpointSquare l Y E π n A hA q)
      := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
