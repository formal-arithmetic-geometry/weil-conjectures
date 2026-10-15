/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
import Sheaf.Paper.StrictHenselizationPointEvaluationPointed

/-!
# The distinguished geometric closed point lies over the original point

Source: Stacks Project, Tag 04HX
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The coordinate-ring evaluation gives the canonical closed-point lift over `s`.
Source: Stacks Project, Tag 04HX
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof: select a representative affine pointed neighbourhood. The structural map is its
limit leg followed by its structure morphism. The evaluation cocone, followed by this
limit leg, is the specified geometric point of that neighbourhood by the colimit cocone
identity (`strictHenselizationPointEvaluation_pointed`). Its composite with the structure
morphism is `s` by pointedness. Associativity gives the asserted factorization. -/
theorem strictHenselizationClosedLift_over
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Spec.map (CommRingCat.ofHom (strictHenselizationPointEvaluation s)) ≫
      strictHenselizationStructuralMap s = s := by
  sorry

end AlgebraicGeometry.Scheme
