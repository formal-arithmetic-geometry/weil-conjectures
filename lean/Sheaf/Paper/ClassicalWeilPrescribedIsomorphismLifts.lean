/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.ClassicalFiniteWeilDiagramData

/-! # Unique lifting of prescribed module identifications with Weil structure

Source: BS 6.8.14(2), Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u v w z
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor (IsoAlgebra)
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

variable [Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- Lift a prescribed compatible module identification, with the supplied finite stage
and common-stage arrow fixed, independently of any finite diagram.
Source: Bhatt--Scholze 6.8.14(2), Remark 6.8.15; finite Weil-diagram proof step 9.
(blueprint: lem-zl-prescribed-weil-isomorphism-lifts).

Proof: fix E, P, N, beta, H, eta and xi from the definition of prescribed lifts.
The lisse-heart Hom bijection for P.realization lifts xi and its inverse to unique
heart arrows. Faithfulness proves their inverse identities. The ordinary pullback
comparison is natural and its unit square is P.ordinary_unit, so the compatibility
assumed for xi makes the lifted heart arrow Weil-equivariant. This gives psi.
Apply the stage isomorphism P.stage to N, the finite-stage image of psi, and eta;
precompose with R.weil applied to beta inverse. P.pinning identifies the resulting
Weil structures and gives a common-stage Weil isomorphism B. Its underlying map is
exactly the composite in the conclusion. Any other B has this same underlying map,
because the lisse-heart Hom bijection forces the same psi from xi. The faithful
Weil forgetful functor and the full-subcategory inclusion then give equality of
hom maps, hence equality of isomorphisms. All arguments apply to zero objects and
to coefficient extensions, since E and eta were arbitrary. -/
theorem zl_prescribed_weil_isomorphism_lifts
    (R : ZlClassicalRealization D l hl Ω Y₀) (M : ZlClassicalWeil D l Ω Y₀) :
    ZlPrescribedWeilLifts D l hl Ω Y₀ R M := by sorry

end WeilConjectures
