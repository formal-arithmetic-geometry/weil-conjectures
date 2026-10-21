/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.AdicResidueLiftComparisons

/-! # Derived Nakayama on localized completed coefficient sites

Source: Stacks Project, Tags 09C6, 099M and 099F.
(blueprint: lem-sfb-adic-complete-residue-conservative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

/-- Residue reduction detects isomorphisms between locally complete objects on a slice.
Source: Stacks Project, proetale.tex, Tag 09C6, final step; Algebraization, Tags 099M and
099F, derived Nakayama.
(blueprint: lem-sfb-adic-complete-residue-conservative).

Proof: complete f to a distinguished triangle with cone Q. The completion unit is a
map of exact functors, so the complete-object criterion and two-out-of-three make Q
complete. Its residue reduction is zero. The exact constant coefficient sequence
0 -> J^n/J^(n+1) -> A/J^(n+1) -> A/J^n -> 0 gives after derived tensor with Q a triangle.
The first term is the tensor of the zero residue reduction with J^n/J^(n+1), hence
vanishes. Induction makes every finite reduction of Q zero. The same calculation
holds on the slice, because restriction is exact and preserves the coefficient maps.
Completeness identifies Q with the derived limit of these zero reductions, hence Q
is zero. The distinguished triangle then makes f an isomorphism. Neither T nor M
is assumed bounded or constructible; no quotient is assumed perfect over A. -/
theorem adicResidue_isIso_of_residue
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U)
    (_hT : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) T)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M)
    (f : T ⟶ M) (_hf : IsIso ((adicResidueLocalReduction.{u, v} X J U 0).map f)) : IsIso f := by
  sorry

end AlgebraicGeometry.Scheme
