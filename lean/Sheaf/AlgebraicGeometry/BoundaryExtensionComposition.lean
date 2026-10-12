/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import Sheaf.AlgebraicGeometry.BoundaryUnitExtensionClass
import Sheaf.AlgebraicGeometry.Modules.BoundaryConnectingNaturality
import Sheaf.AlgebraicGeometry.Modules.PullbackExtensionClass

/-!
# Cohomology boundary as composition with an extension class

Source: literature/stacks-project/cohomology.tex, Lemma Tag 0B3A and Derived Section Tag 06XP
(blueprint: lem-sc-p1-boundary-extension-composition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The connecting map of a short exact sequence is composition with its Yoneda class.
Source: Stacks Project, Cohomology Lemma Tag 0B3A, with Derived Section Tag 06XP.
Proof:
1. Regard the section as `s : O_X ⟶ C`. Naturality of the connecting map under
   pullback (lem-sc-p1-boundary-connecting-naturality) says its boundary is the
   boundary of the unit section for the pulled-back sequence.
2. The pulled-back sequence ends in O_X, so lem-sc-p1-boundary-one-extension-class
   identifies this boundary with its Yoneda extension class under the canonical
   Ext-to-cohomology comparison of lem-sc-ext-locally-free.
3. By lem-sc-p1-pullback-extension-class, that class is the original extension class
   precomposed with s. Combine the three equalities.
The degree-zero comparison renders the section in H^0, and the degree-one comparison
renders the composite in H^1. Both use the canonical unit specialization of
lem-sc-ext-locally-free.
(blueprint: lem-sc-p1-boundary-extension-composition). -/
theorem boundary_extension_composition {X : Scheme.{u}} [HasExt.{u} X.Modules]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (s : 𝟙_ X.Modules ⟶ S.X₃) :
    H.δ hS 0 (locallyFreeUnitExtAddEquivH S.X₃ 0 (Abelian.Ext.mk₀ s)) =
      locallyFreeUnitExtAddEquivH S.X₁ 1
        ((Abelian.Ext.mk₀ s).comp hS.extClass (Nat.zero_add 1)) := sorry

end AlgebraicGeometry.Scheme.Modules
