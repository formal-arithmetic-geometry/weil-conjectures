/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Paper.CompletedCoefficientSystemTransport

/-!
# Construction of normalized completed-coefficient transport

Source: Stacks Project, Tags 099I and 099K; the construction in steps 1--11 of
lem-pur-completed-coefficient-monoidal-adjunction-transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u s i j
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedCoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Construct the coefficient-restriction data with the actual R structural maps
normalized against the coherent system constraints, and its constant-side expression
comparison identified with those systems. Simultaneous substitution and structural
coherence of that expression comparison are separate consequences.

Source: Stacks Project, algebraization.tex, Tags 099I and 099K; blueprint
lem-fix-operation-reduction.proof.md, final paragraph; construction steps 1--11 of
lem-pur-completed-coefficient-monoidal-adjunction-transport
(blueprint: lem-pur-completed-coefficient-normalized-transport).

Proof: take flat-term K-flat resolutions and the strict finite quotient comparison of
constant and completed coefficients. Exact scalar restriction preserves these resolutions
and total limits. The quotient-completion comparison preserves the degree-zero units,
so both completion functors have the recorded reflector Hom bijections. Reflect the
ordinary tensor structures, taking the tensor and coefficient units to be these actual
completions. Derived finite scalar-extension balancing gives the tensorator: at level n
its inverse multiplies the two quotient coefficients. This formula commutes with every
quotient transition. Its augmentation gives tensor_unit, and reassociation, coefficient
multiplication and the Koszul sign give the monoidal and braided axioms. The finite
scalar-unit maps x ↦ 1 tensor x similarly give b and b_unit, with the same strict
quotient pullbacks and the zero shifted-product component of their Roos augmentations.
Construct the completed adjunctions by the ordinary adjunction and reflector Hom
bijections. Their counits are determined by their composites with the completion units.
The ordinary restriction counit identity therefore gives the completed counit identity
by injectivity of that reflector Hom map. Naturality of b gives the inverse Hom identity;
evaluation on the identity gives the unit identity. The coefficient system operation
models are the normalized coherent-counit models. Take system_unit from their augmented
unit tower, and take compositionR from the system composition comparison; define the
constant-side composition with the b square. The same representative formulas commute
with associator, unitors, signed symmetry and pullback composition on entire systems.
They remain equal after localization and total limit. For tensor and pullback contexts,
apply functoriality; inverses and composites preserve the squares. This proves the
first system structural square for all StructuralMap constructors. The constant-side
expression comparison agrees with its system comparison by induction on expressions:
for tensor and pullback cancel the actual completion unit using its reflector Hom
bijection, and then apply balancing naturality, tensor_unit and b_unit. The reduction square
follows from the coherent counit's naturality and reductionComparison = reduction(beta)
followed by that counit. Every construction is on unbounded good resolutions, so neither
bounds nor finite Tor-amplitude enter. -/
theorem completedCoefficientNormalizedTransport {S : Type s} (W : S → Scheme.{t})
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∃ T : Transport.{t, u, s, i, j} l E W,
      ExpressionSystemLaw l E T ∧ ExpressionSystemStructuralLaw l E T := by sorry

end WeilConjectures.CompletedCoefficientTransport
