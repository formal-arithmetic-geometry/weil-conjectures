/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryKummerArrowTransport

/-! # Finite integral coordinates for a strict Chern arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Finite Chern normalization identifies the integral finite cone coordinates
with the positive Kummer class. No completed arrow or limit normalization is used. -/
theorem localChern_normalized_boundary_kummer
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (hc : FiniteChernNormalization l (ULift.{u} (Padic l)) c) (P : T.Pic) :
    finiteConeChernClass l T c r k A n hA hN
        (firstChern l (ULift.{u} (Padic l)) c P) =
      evaluatedIntegralKummerClass l T A n hA c.kummer hN P := by
  apply Ext.ext
  have hs : source_endpoint_statement l T c r k n := finiteBoundary_source_endpoint l T c r k n
  have ht : target_endpoint_statement l T c r k A n hA hN :=
    finiteBoundary_target_endpoint l T c r k A n hA hN
  exact finiteBoundary_transport_assembly l T c r k A n hA hN hc P hs ht

end AlgebraicGeometry.ProEtale.DiagonalTrace
