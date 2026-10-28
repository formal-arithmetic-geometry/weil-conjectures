/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.DiagonalCoefficientRouteSquare

/-! # The positive-root endpoint of cyclic coefficient continuation

Source: diagonal tower coefficient changes (1), root projections and tensor units.
(blueprint: lem-diagonal-cyclic-uniformizer-target).
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

/-- The mate of any underlying-identity restriction comparison has the prescribed
positive-root endpoint. No constant-source or diagonal-class equation is assumed.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), root projection and derived
scalar transitivity; parent coefficient-square proof, step 2.
(blueprint: lem-diagonal-cyclic-uniformizer-target).

Proof: transpose the two target maps through the actual scalar adjunctions.
Endpoint.normalization identifies their transposes with the single of the
prescribed semilinear maps. On underlying sheaves, the normalization of the
restriction comparison cancels the inverse realization counits. IntegralRoots
projections identify integralLineMap with the bottom-to-E transition on every
finite root projection. The scalar extension units and the two LineEndpoint
normalizations therefore identify both maps on pure root tensors with the n-th
root projection followed by coefficient extension. FiniteRoots comparisons
coincide since their composites with the monic kernel inclusion coincide.
The supplied line_normalization identifies coefficient extension on these root
tensors with maps.line. At the bottom field, each coefficient-root module is the root sheaf itself:
free extension over Z/l^(r+1) is an isomorphism on an l^(r+1)-torsion sheaf.
Consequently the bottom IntegralRoots map is an isomorphism, by the limit
universal property. Precomposing the bottom-to-E transition with this map gives
the E-root map, since every projection agrees. Thus it suffices to compare the
two transposed arrows on this bottom root sheaf. The finite root calculation
and balanced-tensor unit equations above give exactly that comparison.
The derived adjunction is compatible with shifts; naturality of the exact single
and shift comparisons translates the transposed equality to TargetEquation.
Adjunction injectivity completes the proof. No property of the initial arrow,
no finite evaluation detection of arbitrary derived morphisms, and no flatness
of A over the cyclic ring is needed. The same tensor calculation includes n=0,
the empty base, and the zero target ring. -/
theorem diagonalCyclic_uniformizerTarget
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A]
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) :
    criterionHypothesis% 1 (UniformizerSquareData.endpointSquare l Y E π n A hA q)
      := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
