/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.FiniteIndHeartAdjunction
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-! # Exact finite direct image on equivariant ind-sheaves

Source: Stacks 09A8; blueprint main-20261015, lem-zl-quasi-finite.proof.md, clause (1).
(blueprint: lem-zl-finite-weil-ind-push-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

/-- Finite direct image on all equivariant ind-objects is right exact. Its left
exactness already follows from its defining inverse-image adjunction. No compactification,
weight, or coefficient embedding occurs in this assertion.

Source: Stacks 09A8; Bhatt--Scholze 6.8.14--6.8.15; blueprint main-20261015,
`lem-zl-quasi-finite.proof.md`, clause (1), exact finite direct image.
(blueprint: lem-zl-finite-weil-ind-push-exact).

Proof: apply sfFiniteIndHeartAdjunction for the underlying ordinary ind-heart
adjunction and exactness. Both prescribed ind Frobenius functors are exact
autoequivalences. The mate of the normalized inverse-image square is therefore
invertible. IsoAlgebra.mapOfNatIsoAdjunction lifts this adjunction to invertible
Frobenius pairs. The lifted right adjoint preserves finite colimits because its
underlying right adjoint does, and fixed-pair colimits are computed on carriers.
The left functor in the lifted adjunction is the specified zlIndWeilPull.
Uniqueness of right adjoints gives the natural isomorphism from the lifted
right functor to the prescribed zlIndWeilPush. Transfer preservation of finite
colimits along that isomorphism. The zero sheaf, empty source, nonreduced finite
fibres and identity maps are included in the same argument. -/
theorem sfFiniteWeilIndPushExact
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsFinite f₀.left] :
    PreservesFiniteColimits (zlIndWeilPush D l hl Ω f₀) := by
  obtain ⟨R, ⟨adj⟩, hR⟩ := sfFiniteIndHeartAdjunction D l hl Ω f₀
  let := hR
  obtain ⟨haX, hlX, hcX, heX⟩ := zlIndFrobenius_exact D l hl Ω X₀
  obtain ⟨haY, hlY, hcY, heY⟩ := zlIndFrobenius_exact D l hl Ω Y₀
  let := haX
  let := hlX
  let := hcX
  let := heX
  let := haY
  let := hlY
  let := hcY
  let := heY
  let e := zlIndSquare (zlSmallPull D l hl Ω f₀)
    (zlSmallFrobenius D l hl Ω Y₀) (zlSmallFrobenius D l hl Ω X₀)
    (zlSmallSquare D l hl Ω f₀)
  let eR := IsoAlgebra.mateIso adj e
  let lifted := IsoAlgebra.mapOfNatIsoAdjunction adj e eR rfl
  have hR : PreservesFiniteColimits (IsoAlgebra.mapOfNatIso eR) := inferInstance
  have : (zlIndWeilPull D l hl Ω f₀).IsLeftAdjoint :=
    zlIndWeilPull_isLeftAdjoint D l hl Ω f₀
  have : (IsoAlgebra.mapOfNatIso e).IsLeftAdjoint :=
    zlIndWeilPull_isLeftAdjoint D l hl Ω f₀
  change PreservesFiniteColimits (zlIndWeilPull D l hl Ω f₀).rightAdjoint
  exact preservesFiniteColimits_of_natIso
    (lifted.rightAdjointUniq (Adjunction.ofIsLeftAdjoint _))

end WeilConjectures
