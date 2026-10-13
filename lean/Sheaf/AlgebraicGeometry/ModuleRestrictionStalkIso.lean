/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks
import Sheaf.Algebra.Homology.ModuleRestrictionStalkComponents

/-! # Open restriction does not change a module stalk

Source: Stacks Project, Sheaves, Lemma 00A0, part (3), and Modules, Tag 01CP.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Restriction to an open neighborhood preserves a module stalk after scalar transport.

Source: Stacks Project, Sheaves, Lemma 00A0, part (3); Modules, Tag 01CP,
third paragraph, localization before taking the source-stalk exact sequence.
(blueprint: lem-weil-pbc-module-restriction-stalk-iso)

Proof: Let Y be the restriction of X to U and y the point (x,hxU). The
neighborhood functor from Y to X is final after taking opposites: intersecting
any neighborhood of x with U provides a refinement. Apply the final-functor
colimit comparison to the underlying abelian presheaf of F. This gives an
additive isomorphism from the restricted stalk to F_x, sending the germ of a
section on V in U to the germ of that section on the image of V in X.
The component maps of exists_moduleRestrictionStalk_components satisfy this
same germ formula and are linear over O_{X,x} after restricting scalars along
the inverse restriction-stalk ring map. Since germs jointly generate the
colimit, their underlying additive maps equal the additive comparison above.
They are therefore bijective. The forgetful functor from modules to abelian
groups reflects isomorphisms, so the linear component is an isomorphism.
This argument applies to every F, requires no finiteness, and includes the
zero module and zero stalk ring. If U is empty there is no hxU. -/
theorem nonempty_moduleRestrictionStalk_iso
    (X : RingedSpace.{u}) (F : Modules X) (U : Opens X) (x : X) (hxU : x ∈ U) :
    Nonempty
      ((ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv.hom).obj
        ((moduleStalkFunctor (X.restrict U.isOpenEmbedding) ⟨x, hxU⟩).obj
          ((U.sheafOfModulesEquivOver (moduleRings X)).functor.obj (F.over U))) ≅
        (moduleStalkFunctor X x).obj F) := by sorry

end AlgebraicGeometry.RingedSpace
