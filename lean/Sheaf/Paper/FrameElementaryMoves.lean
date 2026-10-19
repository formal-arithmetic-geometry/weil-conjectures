/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.PurityFrameClass
public import Mathlib.Logic.Relation
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.Paper.SupportedAffineLineHomotopy
import Sheaf.Paper.SupportedCupFunctoriality

/-! # Elementary moves of a concrete boundary product

Source: main-20261015, lem-pur-frame-independence.proof.md, the three operation paragraphs.
(blueprint: lem-pur-frame-elementary-moves).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- A single invertible change of a finite tuple of ring elements: multiplication
of one entry by a unit, interchange of two distinct entries, or a shear.
Source: main-20261015, lem-pur-frame-independence.proof.md, elementary operations
(blueprint: lem-pur-frame-elementary-moves). -/
def FrameElementaryMove {R : Type u} [CommRing R] {c : ℕ}
    (f g : Fin c → R) : Prop :=
  (∃ (i : Fin c) (a : Rˣ),
    ∀ k, g k = if k = i then (a : R) * f i else f k) ∨
  (∃ (i j : Fin c), i ≠ j ∧
    ∀ k, g k = if k = i then f j else if k = j then f i else f k) ∨
  (∃ (i j : Fin c) (a : R), i ≠ j ∧
    ∀ k, g k = if k = i then f i + a * f j else f k)

/-- The ordered product of individual Kummer support boundaries is unchanged by
one elementary generator move, including its canonical scheme-theoretic support
identification. Heterogeneous equality expresses transport along the equality of
zero subschemes induced by equality of the generated ideals; it does not identify
classes in unrelated supports.

Source: main-20261015, lem-pur-frame-independence.proof.md, Unit multiples,
Permutations and Elementary shears (blueprint: lem-pur-frame-elementary-moves).

Proof: A unit multiple has the same principal ideal and basic-open complement.
Kummer additivity separates the new unit contribution, which extends over X and
has zero localization boundary by exactness. Thus this individual boundary is
unchanged. For a transposition, associate the two factors next to each other and
use supported graded symmetry. Their degrees are both two, giving sign +1; the
symmetry of the rank-one Tate lines preserves their multiplication. Associate
back. For a shear use f_i+t*a*f_j on A^1_X. The other entries are unchanged and
subtracting t*a*f_j recovers f_i, so the total ideal is the extension of the
original ideal. The ordered boundary product is therefore supported on the
constant inverse-image closed subscheme. Naturality of the boundary and cup
identifies its two section pullbacks with the displayed endpoint products.
Supported affine-line invariance makes the two section pullbacks equal, since
both are inverse to projection pullback. The support comparisons are the unique
ones over X, hence agree with transport along equality of the generated ideals.
No smoothness or etaleness of the affine-line interpolation is required. -/
theorem frameBoundaryProduct_elementary (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (f g : Fin c → Γ(X, ⊤)) (h : FrameElementaryMove f g) :
    HEq (P.frameBoundaryProduct X a c f) (P.frameBoundaryProduct X a c g) := by
  sorry

end WeilConjectures.PurityFiniteSetting
