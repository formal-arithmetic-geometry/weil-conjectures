/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRestriction.FiniteRestrictionNormalizedAdjunction

/-!
# Definition interface for native compact-support comparison

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 4, the finite adjunction's
coefficient coordinates (blueprint: def-pur-native-compact-support-comparison).

These transparent re-exports expose the existing fixed compact-support functor and
specified comparison as definition-owned data. They call the original constructions
literally; no comparison or coefficient encoding is chosen here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

namespace WeilConjectures.NativeCompactSupport

/-- Re-export of fixed-scalar compact support for the supplied compactification.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof.md, Step 4;
sk-thm-sf-tensor-hom, Complement (blueprint: def-pur-native-compact-support-comparison).
This is exactly `FiniteRestriction.fixedSupport`, with no replacement functor.
-/
abbrev fixedSupport (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
      DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  FiniteRestriction.fixedSupport A c

/-- Re-export of the canonical comparison in inverse encoding coordinates.
Source: latest blueprint thm-pur-finite-reduction-of-purity.proof.md, Step 4;
sk-thm-sf-tensor-hom, Complement (blueprint: def-pur-native-compact-support-comparison).
The original construction cancels the coefficient equivalences from the actual
compactification encoding comparison, including its specified open-extension and
derived direct-image comparisons. This alias retains that exact construction.
-/
abbrev comparison (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (encoding : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (encoding X).fixedDerived.inverse ⋙ FiniteRestriction.support A c ≅
      fixedSupport A c ⋙ (encoding Y).fixedDerived.inverse :=
  FiniteRestriction.comparison A encoding c

end WeilConjectures.NativeCompactSupport
