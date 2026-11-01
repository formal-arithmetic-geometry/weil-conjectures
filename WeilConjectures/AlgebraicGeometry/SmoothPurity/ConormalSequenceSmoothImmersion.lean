/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# Conormal fibre sequence for a smooth closed subscheme

Source: Stacks Project, Morphisms, Tags 06AA and 02G1
(blueprint: lem-pur-conormal-sequence-smooth-immersion).

The two arrows are characterized on generators by their differential formulas. The conormal
fibre is written as `κ ⊗[R] I.Cotangent`: since `R → S` is surjective and `I` annihilates
`I.Cotangent`, this is canonically `κ ⊗[S] (I/I²)`. Tensor factors are in Mathlib's
extension-of-scalars order.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The conormal fibre at a point of a closed immersion, using the actual stalk kernel.
Source: Stacks Project, Tag 06AA; the quotient is Mathlib's `Ideal.Cotangent`.
The `R`-balanced tensor equals the `S`-balanced tensor because `S = R/I`.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def conormalStalkFibre {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    ModuleCat (Z.residueField z) :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  ModuleCat.of _ ((Z.residueField z) ⊗[X.presheaf.stalk (i z)]
    (RingHom.ker (i.stalkMap z).hom).Cotangent)

/-- The fibre of the existing relative differential sheaf at `i z`, extended to `κ(z)`.
Source: Stacks Project, Tags 01UM and 06AA; stalks use the canonical module structure.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def relativeDifferentialsStalkFibre {X Z B : Scheme.{u}}
    (f : X ⟶ B) (i : Z ⟶ X) (z : Z) : ModuleCat (Z.residueField z) :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  ModuleCat.of _ ((Z.residueField z) ⊗[X.presheaf.stalk (i z)]
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i z)).obj f.relativeDifferentials))

/-- The germ of the differential of a section, tensored with one in the residue field.
Source: Stacks Project, Tags 01UM and 06AA; the derivation is the existing universal derivation.
(blueprint: lem-pur-conormal-sequence-smooth-immersion). -/
noncomputable def relativeDifferentialsStalkFibreGerm {X Z B : Scheme.{u}}
    (f : X ⟶ B) (i : Z ⟶ X) (z : Z) (U : X.Opens) (hz : i z ∈ U)
    (a : Γ(X, U)) : relativeDifferentialsStalkFibre f i z :=
  letI := (i.stalkMap z ≫ Z.residue z).hom.toAlgebra
  1 ⊗ₜ[X.presheaf.stalk (i z)]
    (TopCat.Presheaf.germ f.relativeDifferentials.val.presheaf U (i z) hz
      (f.relativeDifferentialsDerivation.d (X := op U) a))

section Proof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v w t

open TensorProduct CategoryTheory.Limits TopologicalSpace

-- Take the stalk of the additive sheaf derivation, preserving its germ formula.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end Proof

end AlgebraicGeometry.Scheme.Hom
