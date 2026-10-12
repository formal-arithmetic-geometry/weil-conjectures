/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHomProperties

/-!
# Faithfully flat descent of relative smooth dimension

Source: Stacks Project, Descent, Tag 02VL, and Morphisms, Tag 02G1;
Algebra, Tag 00T7, part (2).
(blueprint: lem-pd-relative-smooth-dimension-codescent).
-/

@[expose] public section

namespace RingHom

/-- Locally standard smooth maps of fixed relative dimension descend under faithfully flat
base change. Source: Stacks Project, Tags 02VL, 02G1 and 00T7 (2).
(blueprint: lem-pd-relative-smooth-dimension-codescent).

Proof: Let R -> S and R -> T be the maps in the codescent square, with R -> T faithfully
flat. The tensor product S -> T tensor_R S is faithfully flat. Smoothness of R -> S
follows from faithfully flat descent of smooth algebras (02VL, or its affine algebraic
proof). Around any prime of S choose a standard smooth presentation. Its differentials
are free of rank the presentation dimension, by 00T7 (2). Choose a prime upstairs over
this prime, possible by faithful flatness. Differentials commute with base change;
their fibre vector space at this prime is obtained by extending the residue field of
the original prime. Its dimension is n since the upstairs map is locally standard
smooth of dimension n. Extension of a field preserves the dimension of a finite
vector space, so the standard smooth chart downstairs has presentation dimension n.
The chart therefore witnesses locally standard smooth of relative dimension n at the
original prime. Such charts cover Spec S. If S is the zero ring, Spec S is empty and
local standard smoothness of every relative dimension is vacuous. -/
theorem locally_standardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat (n : ℕ) :
    CodescendsAlong (Locally (IsStandardSmoothOfRelativeDimension n)) FaithfullyFlat := by
  sorry

end RingHom
