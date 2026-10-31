/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.NativeExceptionalForgetful

public import WeilConjectures.SixFunctors.CoefQbarVerdier

/-! # Constructible Hom into the structural exceptional image

Source: current blueprint, thm-coef-qbar-verdier, internal Hom and structural
exceptional image (blueprint: lem-sf-structural-omega-hom-pairs).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open WeilConjectures.AdicQbarRealization WeilConjectures.NativeExceptionalForgetful
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures.NativeDualPresentation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D)

/-- The actual structural exceptional image admits every constructible source.
Source: current blueprint, thm-coef-qbar-verdier, internal Hom and identification
of omega with the structural exceptional image
(blueprint: lem-sf-structural-omega-hom-pairs).

Proof: apply thm-coef-qbar-verdier on the geometric fiber. Its internal-Hom
identification makes Hom into its dualizing object constructible. Its Dualizing
clause identifies that object with the structural exceptional image of the unit.
Compare the exceptional adjoints using their adjunctions: the scalar-normalized
left comparison identifies their compact-support functors, so uniqueness of right
adjoints gives the unit-compatible right comparison. The actual point unit
geometricPointOmega agrees with the finite-stage coefficient unit under the unit
comparison. Thus the specified system S and compactification c give the same
structural dualizing object. Put the source, these comparisons and their inverses
at one common finite coefficient field. Constructibility of rational internal Hom
is invariant under these isomorphisms and further finite scalar extension.
The defining compositum predicate commonStageHomPairs therefore holds for the
literal pair in the statement. For M = 0, and on the empty scheme, the Hom is
zero; no smoothness or perfectness of M on the entire scheme is used. -/
theorem structural_omega_hom_pairs (S : StructuralSystem D l X)
    (c : Compactification (geometric D X).base.hom) (M : C D l X) :
    commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left
      (op M, (S.ring.operation c .closed).G.obj (geometricPointOmega D l R)) := by sorry

end WeilConjectures.NativeDualPresentation
