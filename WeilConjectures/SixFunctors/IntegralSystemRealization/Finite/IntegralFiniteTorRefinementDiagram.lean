/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementDiagramAdmissibility

/-! # Domain witnesses for finite-Tor inputs in a binary refinement diagram -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- Extract the eighteen expression-domain witnesses from the common Tor interval.
Source: integral refinement diagram admissibility, restricted to a finite-Tor input.
(blueprint: lem-sf-integral-finite-tor-refinement-diagram).
Proof: The second property of K supplies a single ordered Tor interval for all
positive reductions. Apply integralRefinementDiagramAdmissibility with that
interval and K's constructibility property. Its fourth conjunct supplies, for
each expression, an admissibility witness together with the domain witness;
retain the latter. -/
theorem integralFiniteTorRefinementDiagram
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (S : Realizations l E D o)
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Fin 3 → Compactification f.left)
    (r : (c 0).Refinement (c 1)) (t : (c 1).Refinement (c 2))
    (hqc : ∀ i, QuasiCompact (c i).i)
    (K : finiteTorConstructibleIntegralCategory l E X.left) (q : Fin 18) :
    (refinementDiagramWords f c r t hqc q).2.domain l E o (fun _ ↦ K.obj) := by
  obtain ⟨a, b, hab, hTor⟩ := K.property.2
  obtain ⟨_, _, _, h⟩ := integralRefinementDiagramAdmissibility
    l E D hl o S f c r t hqc K.obj K.property.1 a b hab hTor
  exact (h q).choose_spec.choose

end WeilConjectures.IntegralSystemRealization
