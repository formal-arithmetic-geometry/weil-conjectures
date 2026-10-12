/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Comparing restricted scalar extension with the sheaf tensor product

Source: Stacks Project, Modules on Sites, Tag 03EK; Tag 06YY.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Source: Stacks Project, Tag 03EK and Tag 06YY, degree-zero tensor comparison.

Proof: Put U = restriction along φ and S = U(O'). Before sheafification the
identity on pure tensors identifies the restricted sectionwise scalar extension
O'(V) tensor over O(V) M(V) with the sectionwise tensor of S and M. It respects
restrictions because both constructions restrict each tensor factor, and respects
module morphisms because both apply id tensor a. Restriction of scalars commutes
with sheafification: the underlying abelian presheaf and its associated sheaf are
unchanged, and the induced O action is restriction of the induced O' action.
Thus these presheaf identifications sheafify to the asserted isomorphisms.
The counit at the already-sheaf module S and the monoidal localization comparison
identify the resulting sheafification with S tensor M. Naturality survives each
comparison and sheafification, giving the displayed equation for every a.
This uses no flatness; the identity on tensors also covers zero rings and modules.
(blueprint: lem-pur-change-of-rings-tensor-comparison) -/
theorem exists_changeOfRings_tensor_comparison
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O') :
    letI := monoidalCategory O
    let U := restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
    let S := U.obj (unit (𝓡 O'))
    ∃ e : ∀ M : SheafOfModules.{u} (𝓡 O), U.obj (changeOfRings φ M) ≅ S ⊗ M,
      ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
        U.map (changeOfRingsHom φ M a) ≫ (e N).hom = (e M).hom ≫ S ◁ a := by sorry

end SheafOfModules
