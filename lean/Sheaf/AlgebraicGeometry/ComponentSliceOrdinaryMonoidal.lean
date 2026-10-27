/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ComponentSliceComparisonData

/-! # The ordinary component slice square

Source: Hemo--Richarz--Scholbach, Proposition 4.3(1), equation (4.2).
(blueprint: lem-sfb-component-slice-ordinary-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The ordinary component square is a normalized tensor-compatible square.

Source: HRS Proposition 4.3(1), equation (4.2); Stacks Tags 03DH and 03EL.
(blueprint: lem-sfb-component-slice-ordinary-monoidal).

Proof: Restriction on Prof/S is precomposition along Over.map, so its coefficient
comparison is the identity on sections. The ordinary sheaf tensor universal property
makes this restriction strong braided monoidal; kernels and cokernels of module sheaves
are computed locally, so restriction is exact. Transport the module action along the
sectionwise coefficient identity to obtain r, with the displayed balanced tensor formula.
For a w-contractible affine V over U, use the two normalized component evaluation
isomorphisms and the scheme localization isomorphism. Both sides become the sections of
M on pi_0(V) over pi_0(W); insert componentCompositionIso to identify their structure maps.
These maps commute with restrictions and module morphisms by Kan-unit naturality.
Cover arbitrary tests by w-contractible affines and their overlaps by such affines again;
sheaf gluing extends the maps and their inverses to a natural isomorphism e. The resulting
map has exactly OrdinaryBasisFormula. On coefficients it is the section identity; on
local pure tensors it is the tensor of these identities. Since local pure tensors generate
the sheaf tensor, its tensor square commutes, and the coefficient identity gives its unit
square. The scheme-side tensorator is precisely schemeCanonicalMonoidal, by its transport
from the native upper-star comparison. This proves OrdinaryMonoidal for that fixed
structure. Empty tests and the zero coefficient ring give the same identities. -/
theorem component_slice_ordinary_monoidal
    (W : Scheme.{u}) [IsAffine W] [IsWContractibleRing Γ(W, ⊤)]
    (U : W.ProEt) [IsAffine U.left] [IsWContractibleRing Γ(U.left, ⊤)]
    (dW : PullbackData Λ W) (dU : PullbackData Λ U.left) :
    ∃ (r : RestrictionData Λ (componentMap W U))
      (e : OrdinaryComparison Λ W U dW dU r),
      OrdinaryMonoidal Λ W U dW dU r (schemeCanonicalMonoidal Λ W U) e := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ComponentSlice
