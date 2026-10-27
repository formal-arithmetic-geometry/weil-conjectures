/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist

/-! # Cohomology identification of native smooth dualizing purity

The native derived category of Weil sheaves retains derived morphisms.  This statement
isolates the cohomology identification. It does not identify that category with fixed pairs
of derived objects.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The degree `-2d` cohomology of the exceptional constant object is the Tate line.

Source: current blueprint, `cor-pur-adic-and-rational-smooth-dualizing-complexes`,
smooth specialization, and `lem-pur-constant-purity-frobenius-square`.
(blueprint: lem-sf-weil-smooth-dualizing-cohomology)

Proof: use the counit-normalized native exceptional-forgetting comparison to identify the
ordinary realization of `J` applied to the constant Weil complex with the geometric
exceptional constant object.  Take degree `-2d` cohomology of the geometric smooth purity
isomorphism, obtained at finite coefficients and transported through integral reconstruction,
rationalization and common-stage descent.  This gives the constant Tate sheaf of weight `d`.
For its Weil structure, first transport the native counit's equivariance equation through
the normalized compact-support comparison.  Transpose through the ordinary adjunction:
this uniquely specifies the action `v` by `ε F(v) a = θ Q(ε)`.  The native scalar Frobenius
counit lemma computes that solution as `v = G(θ)b`, with `b` the inverse-exchange mate.
The constant-purity Frobenius square identifies this exceptional mate action with the
canonical Tate action: apply degree `-2d` cohomology to that square.
Exact forgetting commutes with cohomology.  Thus the resulting sheaf isomorphism intertwines
the actual native Frobenius action with the canonical action on the Tate twist.  Its inverse
also intertwines them by composing the intertwining equation with the two inverses.
The pair is therefore an isomorphism of pro-etale Weil sheaves, and hence of constructible
Weil sheaves by fullness.  The native tensor convention presents this Tate-twisted constant
as `tateTwistSheaf.tensorObj adicConstant`.  No assertion about other cohomology degrees
is needed for this identification.
-/
theorem nonempty_smooth_dualizing_cohomology_iso
    (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J)
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty ((homologySheaf (-2 * (d : ℤ))).obj
        (J.obj (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))) ≅
      (WeilSheaf.tateTwistSheaf k₀ l X d).tensorObj (WeilSheaf.adicConstant k₀ l X)
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X d)) := by
  sorry

end AlgebraicGeometry.WeilComplex
