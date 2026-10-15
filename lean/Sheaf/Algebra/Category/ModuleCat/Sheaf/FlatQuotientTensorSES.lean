/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.FlatCoverFunctor

/-!
# Tensor exactness for a flat quotient of module sheaves

Source: Stacks Project, Modules on Sites, Tags 03EX (2) and 03EY (2)
(blueprint: lem-weil-pbc-site-flat-quotient-tensor-ses).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

/-- A short exact sequence with flat quotient remains short exact after tensoring with
any module sheaf. If its middle term is flat, its first term is flat as well.
Source: Stacks Project, Modules on Sites, Tags 03EX (2) and 03EY (2)
(blueprint: lem-weil-pbc-site-flat-quotient-tensor-ses).

Proof: The tensor-Hom adjunction and additivity of
`lem-pc-sheaf-modules-tensor-closed` make tensoring right exact; its natural symmetry
allows either tensor orientation. Choose the functorial flat cover P → N from
`lem-pc-sites-modules-functorial-flat-cover`, and write Q for its kernel. Form the tensor
rows with Q, P and N. The middle row is short exact because P is flat; the others and
all columns are right exact. Flatness of the quotient makes H ⊗ Q → H ⊗ P monic.
For an element in the kernel of F ⊗ N → G ⊗ N, lift to F ⊗ P; its image lifts from
G ⊗ Q, whose image in H ⊗ Q vanishes by that monomorphism. Lift again from F ⊗ Q
and subtract; the middle-row monomorphism makes the difference zero. These are
categorical lifts after epic pullback refinements, so the argument needs no points
or sectionwise surjectivity. This proves the first assertion with right exactness.
If G is flat, apply the first assertion with both ends U and V of an arbitrary mono
U → V. The composite F ⊗ U → G ⊗ U → G ⊗ V is monic and factors through
F ⊗ V. Thus F ⊗ U → F ⊗ V is monic. Together with right exactness and symmetry,
this says the tensor functor defining `IsFlat F` is exact. -/
theorem flat_quotient_tensor_shortExact
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (hS : S.ShortExact) (hH : IsFlat S.X₃) :
    (∀ N : CategoryTheory.ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      (S.map (@tensorRight _ _ (monoidalCategory R) N)).ShortExact) ∧
      (IsFlat S.X₂ → IsFlat S.X₁) := by
  sorry

end SheafOfModules
