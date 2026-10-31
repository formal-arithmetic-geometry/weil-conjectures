/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionLocalAlgebra

/-!
# Complete-intersection local rings of scheme-theoretic fibres

Source: Stacks Project, Morphisms, Tags 02V3 and 01UE; Algebra, Tag 00SD
(blueprint: def-sfb-complete-intersection-fibres).

The pointwise predicate uses the canonical residue-field action on a fibre stalk.
The all-fibres predicate quantifies over every base point and every fibre point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The local ring at `y` of the scheme-theoretic fibre over `s` is a complete-intersection
local algebra over `κ(s)`. Scalars are induced by the fibre's canonical structure map,
the global sections of `Spec κ(s)`, and the germ at `y`.
Source: Stacks Project, Morphisms, Tag 02V3, and Algebra, Tag 00SD
(blueprint: def-sfb-complete-intersection-fibres). -/
def Scheme.Hom.IsCompleteIntersectionAtFiberPoint {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) : Prop :=
  @Algebra.IsCompleteIntersectionLocalAlgebra (S.residueField s)
    ((f.fiber s).presheaf.stalk y) _ _
    (((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appLE ⊤ ⊤ le_top ≫
      (f.fiber s).presheaf.germ ⊤ y trivial).hom.toAlgebra)

/-- Every local ring of every fibre is a complete-intersection local algebra over the
residue field of the base point. Empty fibres impose no condition.
Source: Stacks Project, Morphisms, Tag 02V3 and Tag 01UE
(blueprint: def-sfb-complete-intersection-fibres). -/
def Scheme.Hom.HasCompleteIntersectionFibres {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (s : S) (y : f.fiber s), f.IsCompleteIntersectionAtFiberPoint s y

end AlgebraicGeometry
