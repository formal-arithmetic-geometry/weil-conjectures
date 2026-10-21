/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Algebra.Homology.FlatScalarRealization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-! # Ordinary tensor comparison for canonical scalar realization -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory
namespace SheafOfModules

/-- Realization commutes naturally with ordinary right tensor by a scalar module.
Source: Stacks Project, Modules on Sites, Tags 03EK, 0GMW and 093J
(blueprint: lem-sfb-flat-scalar-tensor-comparison).
Proof: first tensor constant module presheaves sectionwise. Their tensor is the
constant presheaf of the scalar tensor product. Module sheafification commutes
with tensor: its locally bijective coefficient unit and module units extend
balanced bilinear maps uniquely, as in Tag 0GMW. Next extend scalars to R. On
sections the base-change tensor isomorphism sends (r tensor p) tensor
(s tensor q) to rs tensor (p tensor q), with inverse r tensor (p tensor q)
mapped to (r tensor p) tensor (1 tensor q). Balancing proves these inverse
identities on pure tensors. Sheafification extends the maps uniquely and
preserves their inverse equations. These maps commute with restrictions and
with every scalar module map p to f(p), giving the displayed natural
isomorphism. This argument uses no flatness: it is a tensor universal-property
calculation. Zero scalar modules, zero rings and empty covering sieves obey the
same inverse equations. -/
theorem flat_scalar_tensor_comparison
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}
    [HasSheafify J AddCommGrpCat.{max u v}]
    (α : realizationRing J A ⟶ R) (Q : ModuleCat.{max u v} A) :
    Nonempty (flatScalarRealization J α ⋙
      siteSheafTensorRight.{v, u, max u v, max u v} (A := R)
        ((flatScalarRealization J α).obj Q) ≅
      tensorRight Q ⋙ flatScalarRealization J α) := by
  sorry

end SheafOfModules
