/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import WeilConjectures.Blowup.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The actual branch scheme from the closed graph

Source: Stacks Project, Curves, Tag 0CBT (3), and Divisors, Tag 01OG;
the fixed coborder construction in the node (blueprint: def-sfb-nodal-branch-scheme).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.Scheme

/-- The graph of the first-Fitting singular inclusion.
Source: Curves, Tag 0CBT (3) (blueprint: def-sfb-nodal-branch-scheme). -/
def nodalBranchGraph {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] :
    (firstFittingIdealSheaf f).subscheme ⟶
      pullback f (firstFittingSingularSubscheme f ≫ f) :=
  pullback.lift (firstFittingSingularSubscheme f) (𝟙 _) (Category.id_comp _).symm

/-- The graph is an immersion even when the family is not separated.
Source: Morphisms, Tag 07RK (blueprint: def-sfb-nodal-branch-scheme).
Proof: its composite with the first projection is the closed singular inclusion;
apply immersion cancellation (`IsImmersion.of_comp`). -/
theorem nodalBranchGraph_isImmersion {X T : Scheme.{u}} (f : X ⟶ T)
    [LocallyOfFiniteType f] : IsImmersion (nodalBranchGraph f) := by
  sorry

attribute [instance] nodalBranchGraph_isImmersion

/-- The fixed closed graph in the canonical open coborder neighbourhood.
Source: Divisors, Tag 0630 (blueprint: def-sfb-nodal-branch-scheme). -/
def nodalBranchClosedGraph {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] :
    (firstFittingIdealSheaf f).subscheme ⟶ (nodalBranchGraph f).coborderRange.toScheme :=
  (nodalBranchGraph f).liftCoborder

/-- The coborder factor of the graph is closed, as required for its kernel blow-up.
Source: Divisors, Tag 0630; Morphisms, Tag 07RK
(blueprint: def-sfb-nodal-branch-scheme).
Proof: the graph is an immersion by cancellation with its first projection. The canonical
coborder factorization of an immersion has closed first factor (`liftCoborder`); apply
that property to `nodalBranchGraph f` and unfold `nodalBranchClosedGraph`. -/
theorem nodalBranchClosedGraph_isClosedImmersion {X T : Scheme.{u}} (f : X ⟶ T)
    [LocallyOfFiniteType f] : IsClosedImmersion (nodalBranchClosedGraph f) := by
  sorry

attribute [instance] nodalBranchClosedGraph_isClosedImmersion

/-- The exceptional fibre of the blow-up of the closed graph's actual kernel ideal.
Source: Divisors, Tag 01OG; Curves, Tag 0CBT (3)
(blueprint: def-sfb-nodal-branch-scheme). -/
def nodalBranchScheme {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] :
    Scheme.{u} :=
  pullback (nodalBranchClosedGraph f).ker.blowupMap (nodalBranchClosedGraph f)

/-- The projection from the actual exceptional fibre to the singular subscheme.
Source: Curves, Tag 0CBT (3) (blueprint: def-sfb-nodal-branch-scheme). -/
def nodalBranchMap {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] :
    nodalBranchScheme f ⟶ (firstFittingIdealSheaf f).subscheme :=
  pullback.snd _ _

end AlgebraicGeometry.Scheme
