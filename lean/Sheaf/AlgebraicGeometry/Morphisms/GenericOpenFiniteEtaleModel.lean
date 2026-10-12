/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Spreading a generic finite étale cover to an open

Source: Stacks Project, Tags 0EYJ, 01ZM, 01ZO, and 07RP.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite étale torsor on the generic fibre spreads over an open containing the generic
point. No normality, section, or invertibility assumption is needed for this step.

Source: Stacks Project, Tag 0EYJ (choice of an initial open), Tag 01ZM
(descending finite presentation), Tag 01ZO (finiteness), and Tag 07RP (étaleness).
(blueprint: lem-sbc-generic-open-finite-etale-model)

Proof:
Write the generic point of the integral Noetherian base as the inverse limit of its
nonempty affine open neighbourhoods. The qcqs family restricts to the corresponding
inverse system with affine transition maps. Finite étale morphisms are of finite
presentation and descend through this system, as do their finite group action and the
simple-transitivity isomorphism. Descend the cover and its generic comparison at a
common stage; shrink the neighbourhood so finiteness and étaleness hold. Restricting
that neighbourhood in S gives U. The generic-fibre map j factors through c⁻¹(U),
and the descended comparison gives the asserted pullback square. -/
theorem GaloisCover.exists_generic_open_finiteEtale_model {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη) :
    ∃ U : S.Opens, genericPoint S ∈ U ∧
      ∃ (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (P : Scheme.{u})
        (π : P ⟶ (c ⁻¹ᵁ U).toScheme) (ψ : Z.P ⟶ P),
        jU ≫ (c ⁻¹ᵁ U).ι = j ∧ IsFinite π ∧ Etale π ∧ IsPullback ψ Z.π π jU := by sorry

end AlgebraicGeometry.Scheme
