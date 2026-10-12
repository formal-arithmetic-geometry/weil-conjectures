/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.RingTheory.MPseudoCoherent
import Sheaf.RingTheory.DerivedMapLift

/-!
# Finite-free approximation triangles

Source: Stacks Project, Tag 064R, first half of the proof of assertion (1).
(blueprint: lem-pc-ring-pseudo-coherent-approximation-triangle).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A compatible finite-free triangle, before checking cohomology on its third vertex.
Source: Stacks Project, Tag 064R, proof of assertion (1), through construction of
 the morphism of distinguished triangles.
(blueprint: lem-pc-ring-pseudo-coherent-approximation-triangle).

Proof: choose the finite-free witnesses for the first two vertices. Brutally truncate
 the first witness below `m + 1`; its cohomology above `m + 1` is unchanged, and its
 cohomology in degree `m + 1` surjects onto that of the original witness. The truncated
 complex is bounded finite free and vanishes below `m`. Finite free modules are
 projective. Apply the derived map lift (Tag 064E) to lift the composite to the second
 witness as a chain map. Its mapping cone is bounded finite free: each term is the
 direct sum of a term of the second witness and a shifted term of the first witness.
 The cone triangle is distinguished. TR3 extends the commuting square to a morphism
 of triangles. Its first two components retain exactly the witness conditions.
 This statement makes no assertion about cohomology of the third component. -/
theorem exists_pseudoCoherent_approximation_triangle
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R)))
    (hA : IsMPseudoCoherent (m + 1) T.obj₁)
    (hB : IsMPseudoCoherent m T.obj₂) :
    ∃ (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ),
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)) ∧
      ∃ (S : Triangle (DerivedCategory (ModuleCat.{v} R))) (φ : S ⟶ T),
        S ∈ distTriang (DerivedCategory (ModuleCat.{v} R)) ∧ S.obj₃ = Q.obj E ∧
        (∀ i : ℤ, m + 1 < i →
          IsIso ((homologyFunctor (ModuleCat.{v} R) i).map φ.hom₁)) ∧
        Epi ((homologyFunctor (ModuleCat.{v} R) (m + 1)).map φ.hom₁) ∧
        (∀ i : ℤ, m < i →
          IsIso ((homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂)) ∧
        Epi ((homologyFunctor (ModuleCat.{v} R) m).map φ.hom₂) := by
  sorry

end DerivedCategory
