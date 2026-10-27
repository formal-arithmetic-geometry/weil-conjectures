/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.IntegrationExponentTransposeData

/-! # Exponent transport: a step of the normalized integration argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Restriction and ordered tower integration preserve a projective exponent square.
Source: accepted exponent-transport proof Steps 8--9; vector-bundle integration,
Stacks 03PK and 0B65.
(blueprint: lem-pur-affine-exponent-transport).
Proof: write the affine trace as direct image of the open counit followed by
projective inverse trace. The counit is a natural transformation, so its square
commutes with the shifted root transition. Compose with the projective trace
equality supplied by h at the current base. On every affine prefix the same
hypothesis supplies its projective equality; these prefixes are Noetherian and
l remains invertible by pullback. For coefficients, naturality of the
projection gives a square between the two projection maps. Invert this square
and tensor the trace equality to obtain equality of the coefficient counits.
Induct on the ordered tower length. At zero the coefficient transition and
counit are identities. At the successor the counit is the preceding counit
following the preceding left functor applied to the last coefficient counit.
Functoriality, the last coefficient equality, and the induction hypothesis give
the successor equality. The coefficient-descent conjugations in
integrationTowerTransition are precisely the natural tensor reassociations of
this recursion. Apply the same recursion after comparison to obtain the
pro-etale equation. No permutation of the ordered factors is made.
-/
theorem integrationAffineExponentTransport (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (h : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤))),
      IntegrationProjectiveEquations l E n T hT r s hrs hr hs) :
    IntegrationAffineEquations l E n S hS r s hrs hr hs := by sorry


end AlgebraicGeometry.ProEtale.VectorIntegrationSite
