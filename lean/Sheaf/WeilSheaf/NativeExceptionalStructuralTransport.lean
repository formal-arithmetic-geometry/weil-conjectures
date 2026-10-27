/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData

/-! # NativeExceptionalStructuralTransport

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- Ordinary exceptional images of the normalized point unit agree after identifying
the geometric fiber of the model point with literal Spec k.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, structural
specialization; native comparison proof Step 4 and pointGeometricIso.
(blueprint: lem-sf-native-exceptional-structural-transport).

Proof: a morphism a₀ to the model point is its structural morphism, by the Over
commutativity equation. Its geometric base change followed by pointGeometricIso.hom
is therefore the literal geometric structural map. The family isomorphism comparison
for pointGeometricIso preserves the normalized coefficient unit. Factor the ordinary
compact-support functor for this composite as compact support followed by exact
transport along the point isomorphism. Compactification coherence identifies this
factorization for c and c', retaining the proper/open normalization of both systems.
Transport the adjunctions through that isomorphism. Uniqueness of right adjoints,
with their specified units and counits, identifies the exceptional image of the unit.
Apply rho on X. This uses ordinary constructible operations only, and is independent
of a native adjunction. Identity point isomorphisms and empty X give the same formula. -/
theorem native_exceptional_structural_transport (R : Family l D)
    (X : Space D) (a₀ : X.base ⟶ (point D).base)
    [IsSeparated a₀.left] [LocallyOfFiniteType a₀.left] [QuasiCompact a₀.left]
    (S : CoefficientSystem D l a₀) (c : Compactification (geometricMap D a₀))
    (S' : StructuralSystem D l X) (c' : Compactification (geometric D X).base.hom) :
    Nonempty ((rho D l R X).obj
        ((S.ring.operation c .closed).G.obj (omega D l R (point D))) ≅
      (rho D l R X).obj
        ((S'.ring.operation c' .closed).G.obj (geometricPointOmega D l R))) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
