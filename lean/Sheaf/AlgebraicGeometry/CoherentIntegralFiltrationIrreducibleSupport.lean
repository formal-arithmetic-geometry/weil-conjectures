/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The irreducible-support step of coherent integral filtration

Source: Stacks Project, Tag 01YF, irreducible-support paragraphs, using Tag 01YE.
(blueprint: lem-pc-s3-irreducible-support-filtration-step)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Filter a coherent module with irreducible support, assuming smaller supports filtered.

Source: Stacks Project, Tag 01YF, ideal-power and generic-inclusion paragraphs,
using Tags 01Y9 and 01YE (https://stacks.math.columbia.edu/tag/01YF).
(blueprint: lem-pc-s3-irreducible-support-filtration-step)

Proof: Let J be the vanishing ideal of T with its reduced induced closed subscheme
structure. Some power J^n kills F by Tag 01Y9. The powers J^k F and their successive
cokernels are coherent; each graded quotient is supported in T and annihilated by J.
A graded quotient with proper support has a filtration by hsmaller. For a quotient G
with full support T, the stalk of J at ξ is the ambient maximal ideal: a local function
vanishing at ξ vanishes on T in its domain, since ξ specializes to every point of T.
Thus the maximal ideal kills Gξ. Give T its reduced induced integral scheme structure
and apply Tag 01YE to obtain a monomorphism from the pushforward of a finite sum of a
coherent ideal I into G, invertible near ξ. Since Gξ is nonzero, I is nonzero. The source
has a coherent filtration by partial sums with each factor the pushforward of I; finite
closed pushforward preserves coherence and finite sums. The cokernel Q is coherent,
its support is contained in T by stalk exactness, and its stalk at ξ is zero. Its support
is therefore strictly smaller than T, so hsmaller supplies its filtration. The coherent
short-exact extension theorem concatenates these filtrations to filter G. Descending
through the J-adic powers, concatenate the graded filtrations to filter F. If n = 0,
F is zero and the length-zero filtration suffices. No induction on full support occurs
inside this step; all uses of support induction are precisely the supplied hsmaller. -/
theorem coherentIntegralFiltration_of_irreducible_support
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (hsmaller : ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊂ (T : Set X) →
      HasCoherentIntegralFiltration G)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X)) :
    HasCoherentIntegralFiltration F := by sorry

end AlgebraicGeometry.Scheme.Modules
