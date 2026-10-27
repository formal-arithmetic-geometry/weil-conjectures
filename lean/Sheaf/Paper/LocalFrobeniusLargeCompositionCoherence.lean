/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.Paper.LocalFrobeniusLargeCoefficients

/-! # Reassociation of the prescribed common-stage pullback compositor

Source: the naturality and associativity clause of integralPullbackComposition,
localized and transported to the prescribed common-stage representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.commonStageDerivedPullback
  WeilConjectures.LocalFrobeniusLarge.composition

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocalFrobeniusLarge

variable (l : ℕ) [Fact l.Prime] (Ω : Type (u + 1)) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Reassociate three pullbacks and move an arbitrary arrow through their compositor.

Source: Stacks 099N and 0D6D, via integralPullbackComposition; the first step of
lem-zl-large-weil-iterate-addition (blueprint: lem-zl-large-composition-map-assoc).

Proof: at a finite coefficient field, the chosen integral composition family is a
natural isomorphism and satisfies the associativity equation in
integralPullbackComposition. Apply that equation to f, g, h and K. Naturality for
f, g moves t through the last compositor. Rationalization preserves these
identities: its functoriality handles integral composites, its pure-tensor map
formula handles rational maps, and additivity extends the calculation to every
rational arrow. For common-stage objects represent t at a common finite field
containing both endpoint stages. The pullback representative formula conjugates
each rational pullback by commonStagePullbackComparison. Substitute the finite
composition representatives in both words. Adjacent inverse comparisons cancel;
the remaining equality is the rational equation just proved. Compatibility of
the specified scalar comparisons with composition identifies the representatives
of composition at this field with the definition using the original field.
Passing to the Hom colimit proves the equation. The only difference of sources
is associativity of scheme composition, retained here as heterogeneous equality.
There is no Weil structure, iteration, or invariant lattice hypothesis. -/
theorem composition_map_assoc (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (f g h : X ⟶ X)
    (K L : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (t : (commonStageDerivedPullback l Ω h).obj K ⟶ L) :
    HEq
      ((composition l Ω f (g ≫ h) K).hom ≫
        (commonStageDerivedPullback l Ω f).map (composition l Ω g h K).hom ≫
        (commonStageDerivedPullback l Ω f).map
          ((commonStageDerivedPullback l Ω g).map t))
      ((composition l Ω (f ≫ g) h K).hom ≫
        (commonStageDerivedPullback l Ω (f ≫ g)).map t ≫
        (composition l Ω f g L).hom) := by sorry

end WeilConjectures.LocalFrobeniusLarge
