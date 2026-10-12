/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Splitting a coherent module with reducible closed support

Source: Stacks Project, Tags 01YD and 01YF, the reducible-support paragraph.
(blueprint: lem-pc-s3-coherent-reducible-support-exact-sequence)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The reducible-support case gives a short exact sequence with two smaller supports.

Source: Stacks Project, Tag 01YD, Lemma 30.12.1, and Tag 01YF, Lemma 30.12.3,
reducible-support paragraph (https://stacks.math.columbia.edu/tag/01YD).
(blueprint: lem-pc-s3-coherent-reducible-support-exact-sequence)

Proof: A reducible closed set T is the union of two proper closed subsets T₁ and T₂:
use the closed-union characterization of preirreducibility and intersect both closed
sets with T. Tag 01YD gives a coherent submodule H of F with support in T₂ and a
coherent quotient supported in T₁. Concretely, let J be the ideal of the reduced
induced structure on T₁, and take H = J^n F. On X minus T₂, a power of J kills F
by Tag 01Y9; hence H is supported in T₂. Outside T₁ the ideal J is the unit ideal,
so F/H has zero stalk there. Coherence follows from Noetherian coherence stability
for ideal products and cokernels. The inclusion H to F is a monomorphism, and its
canonical cokernel sequence is short exact. Support containment followed by strict
inclusion T₁,T₂ into T gives both strict-support conclusions. Empty or singleton
supports cannot satisfy hred; either of H or its quotient may be zero, which causes
no exception since T is nonempty. This theorem constructs no filtration and uses
no support-induction hypothesis. -/
theorem exists_coherent_submodule_of_reducible_support
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hred : ¬ IsPreirreducible (T : Set X)) :
    ∃ (H : X.Modules) (f : H ⟶ F),
      RingedSpace.IsCoherent X.toRingedSpace H ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel f) ∧
      (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact ∧
      {x : X | ¬ Subsingleton (H.presheaf.stalk x)} ⊂ (T : Set X) ∧
      {x : X | ¬ Subsingleton ((cokernel f).presheaf.stalk x)} ⊂ (T : Set X) := by sorry

end AlgebraicGeometry.Scheme.Modules
