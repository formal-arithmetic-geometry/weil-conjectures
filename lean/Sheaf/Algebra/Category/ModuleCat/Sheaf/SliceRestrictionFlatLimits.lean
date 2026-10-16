/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.RingedSliceExtensionExactness
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-!
# Finite-limit part of flatness after restriction to a slice

Source: Stacks Project, Modules on Sites, Tag 0E8J, Lemma `lemma-restriction-flat`
(blueprint: lem-weil-pbc-slice-restriction-flat-finite-limits).

This is the finite-limit component of the tensor exactness argument used for restriction
of a flat module sheaf to a slice. The remaining colimit component follows from the
closed monoidal structure, while this component requires transporting the exactness
comparison through extension by zero.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- If `F` is flat on a ringed site, tensoring by its restriction to a slice preserves
finite limits. The proof extends a finite-limit diagram by zero, applies finite-limit
preservation of tensoring by `F`, and transports the resulting cone comparison through
the natural extension-by-zero tensor isomorphism and exactness/reflection for the
slice extension.

Proof: extend a finite-limit cone from the slice by the sheafified direct-sum extension.
The extension exactness equivalence identifies exactness and monomorphisms after extension.
Tensor the extended cone with the flat sheaf, then use the natural extension-by-zero tensor
comparison to identify it with the extension of the restricted tensor cone. Reflect the
resulting exactness and monomorphism statements back to the slice.
Source: Stacks Project, Modules on Sites, Tag 0E8J
(blueprint: lem-weil-pbc-slice-restriction-flat-finite-limits). -/
theorem isFlat_over_preservesFiniteLimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : C) (hF : IsFlat F)
    (m : MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))))
    (hm : m = SheafOfModules.monoidalCategory (R.over U)) :
    @PreservesFiniteLimits _ inferInstance _ inferInstance
      (@tensorRight _ _ m (F.over U)) := by
  sorry

end SheafOfModules
