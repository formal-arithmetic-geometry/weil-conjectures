/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.SetTheory.Cardinal.Basic

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.SetSheafCoverDescent

/-!
# Representatives for locally cardinal-generated module sheaves

Source: Stacks Project, Properties, Tag 077M, `lemma-set-of-iso-classes`, and
Tag 077L, `definition-kappa-generated`
(blueprint: lem-sfb-bounded-generated-module-isoclasses).

The local-generation predicate is the definition introduced in the statement of
this node, expressed on an arbitrary ringed space `X : RingedSpace` with the project's
ring sheaf `AlgebraicGeometry.moduleRings X` (the structure sheaf forgotten to `RingCat`).
It uses Mathlib's stalks and scalar action. The space, rings, modules, cardinal and
representing index set all live in the common fixed universe of
`def-weil-size-convention`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false in
/-- The local-generation condition introduced in Tag 077L: an open cover with at
most `κ` sections on each member whose germs span every stalk there.

Source: Stacks Project, Properties, Tag 077L, `definition-kappa-generated`
(blueprint: lem-sfb-bounded-generated-module-isoclasses).
This is the arbitrary-ringed-space form of the same stalk-span formula used by
`AlgebraicGeometry.Scheme.Modules.IsCardinalGenerated` for schemes. In particular,
it does not require the stronger condition that sections span on every open. -/
def IsLocallyCardinalGenerated {X : RingedSpace.{u}}
    (M : ringedSiteModules.{u} (AlgebraicGeometry.moduleRings X)) (κ : Cardinal.{u}) : Prop :=
  ∃ C : Set (Opens X), sSup C = ⊤ ∧
    ∀ U ∈ C, ∃ S : Set (M.val.obj (op U)), Cardinal.mk S ≤ κ ∧
      ∀ (x : X) (hx : x ∈ U),
        Submodule.span
          (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.carrier)
            (AlgebraicGeometry.moduleRings X).obj x)
          ((fun s : M.val.obj (op U) ↦
            TopCat.Presheaf.germ M.val.presheaf U x hx s) '' S) = ⊤

/-- Locally `κ`-generated module sheaves on an arbitrary ringed space have a small
set of representatives, all of which are themselves locally `κ`-generated.

Source: Stacks Project, Properties, Tag 077M, `lemma-set-of-iso-classes`, using
Tag 077L, `definition-kappa-generated`
(blueprint: lem-sfb-bounded-generated-module-isoclasses).

Proof:
1. On each open U, sheafify the free presheaf with basis a set of cardinal κ.
   Coefficientwise restriction gives actual presheaf data. Its maps into N are
   exactly κ-indexed families in N(U), by module sheafification's universal property.
2. Pad any generating subset of N(U) of cardinal at most κ with zero. The induced
   map from the free sheaf is epic: a difference of maps annihilating its image
   has a kernel subsheaf containing the generators, hence the whole sheaf.
3. In the abelian category of module sheaves, every epi is the cokernel of its
   kernel. Indeed, express it as a cokernel, factor the original relation through
   its kernel, and use the two universal properties. Thus N is isomorphic to the
   cokernel of a submodule sheaf of this fixed free sheaf.
4. These submodule sheaves form a set: they are sectionwise submodules, selected
   from the product of the power sets of the free sheaf's section sets. Sheafify
   their sectionwise quotients to obtain a set of local representatives.
5. Remove repeats from covering families. Covers are subsets of the set of opens.
   Local representatives, overlap isomorphisms and identity/cocycle conditions
   therefore form a set of gluing codes; morphisms are families of section maps.
6. Apply set-sheaf cover descent to each code on the site of opens. Define module
   operations by gluing local operations. Linearity of transition maps ensures
   agreement, and uniqueness of gluing proves all module laws and restrictions.
7. Retain the codes producing κ-generated sheaves. Every κ-generated sheaf gives
   such a code by choosing its local quotient representatives. Descent glues the
   local identifications and inverses to a module isomorphism. Empty covers on the
   empty space and empty generating subsets are included. No quasi-coherence or
   finiteness or separation property of the space is used.
-/
theorem boundedGeneratedModuleRepresentatives (X : RingedSpace.{u})
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ∃ (T : Type u) (M : T → ringedSiteModules.{u} (AlgebraicGeometry.moduleRings X)),
      (∀ t, IsLocallyCardinalGenerated (M t) κ) ∧
      ∀ N : ringedSiteModules.{u} (AlgebraicGeometry.moduleRings X),
        IsLocallyCardinalGenerated N κ →
        ∃ t : T, Nonempty (N ≅ M t) := by
  sorry

end SheafOfModules
