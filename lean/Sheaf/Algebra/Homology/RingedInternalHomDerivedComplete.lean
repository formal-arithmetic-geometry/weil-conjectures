/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.RingedSiteLocalization
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.EtaleDerivedScalarTensor

/-!
# Derived internal Hom into a locally derived complete object

Source: Stacks Project, algebraization.tex, Lemma 099A and Definition 0999
(blueprint: lem-sf-ringed-rhom-derived-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

/-- Derived internal Hom with arbitrary source preserves local derived ideal completeness.
The ideal subsheaf is presented by the monomorphism `ι` into the rank-one module sheaf.
There are no boundedness, finite-generation, finite-type-ideal, or flatness assumptions.

Source: Stacks Project, algebraization.tex, Lemma 099A and Definition 0999
(blueprint: lem-sf-ringed-rhom-derived-complete).

Proof:
1. Fix an object U and a section f of the ideal on U. Exact slice restriction identifies
   RHom(K,N)|_U with RHom(K|_U,N|_U), by
   lem-weil-pbc-ringed-internal-hom-exact-restriction (Stacks 08JB).
2. Apply the derived tensor--internal-Hom adjunction on the slice (Stacks 08J9) to identify
   RHom(O_U[1/f],RHom(K|_U,N|_U)) with RHom(O_U[1/f] tensor^L K|_U,N|_U).
   The localization is def-weil-pbc-ringed-site-section-localization.
3. By lem-pur-derived-change-of-rings, K|_U tensor^L O_U[1/f] is an object over O_U[1/f].
   Its underlying O_U-object is O_U[1/f] tensor^L K|_U, by tensor interchange on a K-flat
   representative; the localization is in degree zero, so there is no sign. Completeness
   of N gives RHom(O_U[1/f],N|_U)=0. Apply
   lem-sf-ringed-localization-rhom-orthogonality (Stacks 0996 and 0997) to obtain vanishing
   of RHom(O_U[1/f] tensor^L K|_U,N|_U).
4. Combine the restriction, currying and vanishing from the first three steps. For every
   U and f in the ideal, RHom(O_U[1/f],RHom(K,N)|_U)=0. This is exactly
   def-weil-pbc-locally-derived-ringed-ideal-complete, hence the conclusion. -/
theorem isLocallyDerivedRingedIdealComplete_derivedInternalHom
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] (K N : ringedSiteDerived O)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι
      ((derivedInternalHomOfUniverses.{u, u, u, w} J O).obj (op K, N)) := by
  sorry

end CategoryTheory
