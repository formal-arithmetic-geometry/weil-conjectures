/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.FiniteRingFixedCoordinates
import Sheaf.Paper.FiniteRingEndpointPasting
import Sheaf.Paper.FiniteRingFixedPushComposition

/-! # Cancellation of the fixed finite endpoint coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- The explicit finite open witness has the specified intrinsic endpoint word.
This is only the endpoint equation, without existence or open-adjunction normalization.
Source: compactification-coherence proof, second paragraph; Stacks 03D6 and 0F7B
(blueprint: lem-sf-finite-ring-endpoint-cancellation).

Proof: start with finiteFixedPushIso_composition for r.hom and d.g. Insert the
explicit definition of finiteFixedRefinementOpenIso. Naturality cancels its two
inner inverse coordinate pairs, leaving the fixed proper/open map whiskered by
the outer direct image. At each endpoint apply finiteFixedEndpointModelAt: the
remaining open/direct-image coordinate is finiteImageIso followed by the inverse
image of the equivalence counit and fixedCompactModel. Associate the fixed
compositor at the object, and postcompose by the inverse of the
endpoint coordinate at d. Cancel the two inverse pairs. The remaining right word is
finiteImageIso at c followed by intrinsicRefinement: expand recordedRefinementCore
and apply recordedCore_intrinsic, or use the definition of intrinsicRefinement with
exactly its original category instances. This argument uses neither hi nor the
open-unit equation. Identity refinements, zero objects and empty opens use the same
isomorphism cancellation; no nonvanishing or nonemptiness assumption is required. -/
theorem finiteFixedEndpointCancellation
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin
      (Padic.coefficientExtensionRing l E (n + 1)) X)
    (hg : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (r.hom ≫ d.g) =
      proEtaleRingCompositeCoefficients r.hom d.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull d.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)) :
      ((PurCompactSupport.geometricPushComposition
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r.hom d.g hg ≪≫
      eqToIso (congrArg (fun h ↦ PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) h) r.hom_g)).symm.app _) ≪≫
      (PurCompactSupport.push
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.g).mapIso
          (finiteFixedRefinementOpenIso l E n r O).symm ≪≫
      (PurCompactSupport.finiteImageIso l E n d).app O.K =
    (PurCompactSupport.finiteImageIso l E n c).app O.K ≪≫
      FrobeniusExchange.intrinsicRefinement
        (Padic.coefficientExtensionRing l E (n + 1)) r O := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
