/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction

/-! # Canonical Ext/section identification on an injective resolution

Source: Stacks Project, Tag 01EQ, resolution computation of global cohomology,
and Mathlib's InjectiveResolution.extEquivCohomologyClass.
(blueprint: lem-pc-abelian-cech-ext-section-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Ext cohomology is the homology of the section complex, with compatible representatives.
Source: Stacks 01EQ, resolution computation; Mathlib InjectiveResolution.Ext.
(blueprint: lem-pc-abelian-cech-ext-section-iso)

Proof: Apply extAddEquivCohomologyClass to the constant integral sheaf and I.
In every degree the constant-sheaf adjunction followed by evaluation at 1
identifies morphisms from this sheaf with sections over the terminal open.
The inverse sends a section s to the additive map n ↦ n • s and then applies
the inverse adjunction. Naturality of the adjunction shows these mutually
inverse additive maps commute with the resolution differentials. Thus they
identify cycles and boundaries, inducing an additive isomorphism on homology.
Compose it with the Ext equivalence and convert the additive equivalence to
an AddCommGrpCat isomorphism. For t choose a cocycle using extMk_surjective;
the corresponding section is a cycle by differential compatibility. Its
cycle lift z exists by the kernel universal property. The formula for extMk
under extEquivCohomologyClass gives e(t) = homologyπ(z). This also proves that
the representative condition determines e on every class, independently of
choices. In degree zero boundaries vanish; zero sheaves and empty spaces give
zero groups. No open cover or finiteness assumption occurs in this assertion. -/
theorem abelianCechExtSectionIso_exists
    {X : Scheme.{u}}
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (q : ℕ) :
    ∃ (e : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F ≅
        (abelianCechSections I).homology q),
    ∀ (t : (Sheaf.functorH (Opens.grothendieckTopology X) q).obj F),
      ∃ (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
        (ha : a ≫ I.cocomplex.d q (q + 1) = 0)
        (z : (abelianCechSections I).cycles q),
        I.extMk a (q + 1) rfl ha = t ∧
        ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
            (abelianCechSections I).iCycles q z ∧
        e.hom t = (abelianCechSections I).homologyπ q z := by sorry

end AlgebraicGeometry.Scheme.Modules
