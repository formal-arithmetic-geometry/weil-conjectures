/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.TowerChernPullbackData
public import Sheaf.Paper.TowerClassPullback

/-! # Ordinary scalar association for a fixed integral geometric inverse image

Source: blueprint classes proof (2), balanced coefficient extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Balanced scalar association for already constructed integral inverse image.
The coefficient arrows are specified by their ordinary adjuncts; no derived
counit or K-flatness condition occurs in the statement.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
ordinary coefficient extension; balanced association of scalar extension
(Stacks 03EL).
(blueprint: lem-sp-tower-ordinary-scalar-association).

Proof: use the forgetful comparison to identify d.pull with geometric inverse
image carrying the integral quotient action. The constant-ring comparison is
fixed on integer generators by unit_normalization. The coefficient ring map
commutes with these comparisons, since both quotient maps come from the unital
integer map. Balanced tensor association therefore gives, naturally in every
R-system M, an isomorphism from g.pull(E_Y(M)) to E_X(d.pull(M)). Its forward
map inserts the pulled-back module section, and multiplies the two target
scalars; its inverse inserts the scalar unit. The coefficient square proves
balancing. Tensor sheafification extends both maps, and the composites are the
identity on the sheafification images of pure tensors. Naturality of the ring
comparisons proves compatibility with every horizontal quotient transition.
Transport the result through the object/map equalities of the supplied scalar
models to get alpha. At the coefficient unit, the adjunct identities for eY and
eX say exactly that they are scalar multiplication. Both paths then multiply
the same pulled-back scalar; the constant-section normalization of theta0 gives
the displayed unit equation. At the root module the assumed middle Kummer
normalization identifies the underlying root map with restriction of roots by
kernel uniqueness. Evaluate the ordinary adjoints of the two root composites
at each finite level. Through lineEvaluation they send `a ⊗ z` to
`f(a) ⊗ restrictRoot(z)`. The defining normalization of theta1 is this same
formula. The tensor universal property gives equality of the finite maps;
faithfulness of evaluation on whole ordinary systems and injectivity of the
ordinary geometric adjunction give the root equation. These are ordinary
module maps, so no assertion of faithfulness of derived evaluation is used.
No flatness of the root module, of f, or of the coefficient extension is needed;
all formulas include zero rings and empty charts. -/
theorem ordinaryScalarAssociation_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (nY : cY.Normalized l E) (nX : cX.Normalized l E)
    (θ₀ : CoefficientPullback l E b f g) (θ₁ : LinePullback l E f g cY cX)
    (d : IntegralCoefficientPullback l E f cY cX)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (Opposite.op n) =
      (unitsPull f).app (Opposite.op n))
    (eY : cY.scalar.model.E.obj (coefficient Y (Rrings l Y)) ⟶
      coefficient Y (Arings l E Y))
    (eX : cX.scalar.model.E.obj (coefficient X (Rrings l X)) ⟶
      coefficient X (Arings l E X))
    (heY : (cY.scalar.ordinaryAdjunction.homEquiv _ _) eY = scalarGenerator l E Y)
    (heX : (cX.scalar.ordinaryAdjunction.homEquiv _ _) eX = scalarGenerator l E X) :
    ∃ α : cY.scalar.model.E ⋙ g.pull ≅ d.pull ⋙ cX.scalar.model.E,
      α.hom.app (coefficient Y (Rrings l Y)) ≫ cX.scalar.model.E.map d.unitIso.hom ≫ eX =
        g.pull.map eY ≫ θ₀.iso.hom ∧
      α.hom.app cY.rootModule ≫ cX.scalar.model.E.map d.rootIso.hom = θ₁.iso.hom := by sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
