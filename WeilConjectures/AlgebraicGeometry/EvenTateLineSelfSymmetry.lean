/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EvenLineProductIntegrationMaps

/-! # The self-interchange of the shifted finite Tate line

Source: current blueprint, sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof, Steps 3--4.
(blueprint: lem-pur-even-tate-line-self-symmetry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.EvenLineProduct
open AffineLinePurity AffineSpacePurity

/-- The signed self-interchange of the finite Tate line shifted by two is the identity.
Source: affine-space composition proof Step 3, the even-degree sign calculation
(blueprint: lem-pur-even-tate-line-self-symmetry).

Proof: ell is invertible on the finite-type k-scheme Y. The finite Kummer Tate
sheaf is thus locally constant free of rank one over Ring P. Its ordinary
self-interchange is the identity, as is checked after a local trivialization on
pure tensors a tensor b: commutativity gives ab=ba. This equality descends since
it is an equality of sheaf maps. Use this flat sheaf as its own K-flat resolving
complex and shift it by two. The only nonzero bidegree for its self-tensor is
(-2,-2); the signed interchange coefficient is (-1)^4=1. Hence the interchange
of this resolving tensor complex is the identity. The normalized representative
comparison for derived tensor transports it to the published canonical signed
symmetry of shiftedLine. -/
theorem evenTateLineSelfSymmetry
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aY]
    : (signedSymmetry P Y (shiftedLine P Y) (shiftedLine P Y)).hom = 𝟙 _ := by sorry

end AlgebraicGeometry.ProEtale.EvenLineProduct
