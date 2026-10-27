/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # A local exactness criterion for continuous scalar sheaf complexes

Source: step 5 of `lem-sfb-procyclic-scalar-cochain-evaluation`, the ordinary
kernel/image sheaf cohomology argument below blueprint direct-images paragraph (3).
(blueprint: lem-sfb-continuous-scalar-local-quasi-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar Profinite.CondensedAction

namespace ContinuousCohomology

/-- Low-degree section cohomology and local higher primitives suffice to detect a
quasi-isomorphism to a complex supported in degrees zero and one. This criterion uses
only the sheaves and their actual section maps; it assumes no cochain coordinates,
coefficient-field completeness, or internal derived-invariants comparison.

Source: step 5 of `lem-sfb-procyclic-scalar-cochain-evaluation`, the ordinary sheaf
cohomology assembly in the current blueprint direct-images proof, paragraph (3).
(blueprint: lem-sfb-continuous-scalar-local-quasi-iso).

Proof: Transport internal modules to sheaves of modules by the section-module
equivalence. This exact equivalence reflects homology isomorphisms. For degrees zero
and one, first take homology of the section presheaf complexes and then sheafify.
Sheafification is exact, so this gives the homology sheaves of the original complexes.
The assumed sectionwise isomorphisms form a natural presheaf isomorphism: the maps
are induced by epsilon, and their inverses are natural by uniqueness. Sheafifying
therefore proves the required homology isomorphisms in these two degrees.
For degree q>=2 the target term, hence its homology, is zero. Sections of the source
kernel are precisely the sections x killed by the next differential. The hypothesis
gives a finite jointly surjective cover and a preimage of each restricted x under the
previous differential. Thus the map from the previous term to this kernel is locally
surjective, hence epi as a map of sheaves. The ordinary image equals the kernel, so
the source homology sheaf is zero. In negative degrees both middle terms are zero,
so both homology objects vanish. These cases exhaust the integer degrees and prove
that epsilon is a quasi-isomorphism. For the empty parameter the empty cover works.
-/
theorem continuousScalar_quasiIso_of_local_primitives
    (F : Type u) [NormedField F]
    [∀ S : Profinite.{u},
      (sectionsFunctor (continuousScalarRing F) ⋙
        SheafOfModules.evaluation _ (op S)).PreservesZeroMorphisms]
    (U K : CochainComplex (Modules (continuousScalarRing F)) ℤ) (epsilon : U ⟶ K)
    (hU : ∀ i : ℤ, i < 0 → IsZero (U.X i))
    (hK : ∀ i : ℤ, (i < 0 ∨ 1 < i) → IsZero (K.X i))
    (hLow : ∀ (S : Profinite.{u}) (i : ℤ), i = 0 ∨ i = 1 →
      IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).map
        (((sectionsFunctor (continuousScalarRing F) ⋙
          SheafOfModules.evaluation _ (op S)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map epsilon)))
    (hLocal : ∀ (n : ℕ) (S : Profinite.{u})
      (x : sections (continuousScalarRing F) (U.X ((n + 2 : ℕ) : ℤ)) S),
      (((U.d ((n + 2 : ℕ) : ℤ) ((n + 3 : ℕ) : ℤ)).hom.hom.app (op S)) x) = 0 →
      ∃ (m : ℕ) (T : Fin m → Profinite.{u}) (a : ∀ j : Fin m, T j ⟶ S)
        (y : ∀ j : Fin m,
          sections (continuousScalarRing F) (U.X ((n + 1 : ℕ) : ℤ)) (T j)),
        (∀ s : S, ∃ (j : Fin m) (t : T j), a j t = s) ∧
        ∀ j : Fin m,
          (((U.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom.hom.app (op (T j)))
            (y j)) = (U.X ((n + 2 : ℕ) : ℤ)).X.obj.map (a j).op x) :
    QuasiIso epsilon := by
  sorry

end ContinuousCohomology
