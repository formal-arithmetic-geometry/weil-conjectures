/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Mathlib.Topology.Irreducible

/-! # Opposite effective line classes on a proper integral algebraic space

Source: Stacks Project, Spaces over Fields, Tag 0DMZ,
lemma-characterize-trivial-pic-integral
(blueprint: lem-sfb-space-dual-effective-line-triviality).

Global sections are written as module morphisms from the structure module, via
`SheafOfModules.unitHomEquiv`. Global sections of the internal dual are module
morphisms from the line to the structure module, by the definition of sheaf Hom.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A line module on a proper integral algebraic space is trivial when the line and
its internal dual both have nonzero global sections. The second section is written
as a module morphism to the structure module, namely a global section of sheaf Hom.
The local evaluation pairing is therefore evaluation of this morphism.

Source: Stacks Project, Spaces over Fields, Tag 0DMZ,
lemma-characterize-trivial-pic-integral
(blueprint: lem-sfb-space-dual-effective-line-triviality).

Proof:
1. Choose the nonzero sections s and t. Locally a basis e of L gives the dual basis
   e-dual with e-dual(e) = 1, so the dual is itself a line module. Apply
   lem-sfb-space-generic-line-section-injectivity to both lines: properness gives
   separatedness and finite type. Both germs at a geometric generic point are
   nonzero in one-dimensional vector spaces over its field stalk. In the dual
   bases they have nonzero coefficients a and b, so the germ of c = t(s) is
   ab, which is nonzero. Hence the global function c is nonzero.
2. Nonempty irreducibility implies connectedness. By
   lem-sfb-space-proper-connected-function-field the global functions form a
   field K; it need not equal k. Set d = c-inverse in K.
3. The map s : O_X -> L and the map d t : L -> O_X are inverse. On every
   trivializing etale chart their two composites have coefficient d a b = 1.
   The sheaf axiom detects their equality with the identity on such a cover.
   Thus these maps exhibit L as isomorphic to the structure module. -/
theorem lineModule_trivial_of_dual_effective
    (k : Type u) [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hf : MapIsProper f) (hred : X.IsReduced)
    [IrreducibleSpace (Point X.obj.obj)]
    (L : X.Modules) (hL : X.IsLineModule L)
    (hs : ∃ s : SheafOfModules.unit X.structureSheaf ⟶ L, s ≠ 0)
    (ht : ∃ t : L ⟶ SheafOfModules.unit X.structureSheaf, t ≠ 0) :
    Nonempty (L ≅ SheafOfModules.unit X.structureSheaf) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
