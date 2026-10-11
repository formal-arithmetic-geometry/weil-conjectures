/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties

/-! # Coherent sheaf with prescribed generic support

Source: Stacks Project, Cohomology of Schemes, Lemma 01YO (blueprint:
lem-weil-pbc-finite-surjective-coherent-generic-support).
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- A finite surjective map to a locally Noetherian scheme admits a coherent module whose
pushforward is supported on a prescribed integral closed subscheme and is annihilated at its
generic point by the maximal ideal.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YO, lines 3479--3521
(blueprint: lem-weil-pbc-finite-surjective-coherent-generic-support).

Proof:
1. Finite implies locally finite type, so Y is locally Noetherian
   (lem-weil-pbc-finite-iff-integral-lft, pqf-lem-locnoeth-lft). Lift ξ by surjectivity
   and take its reduced closure (lem-weil-pbc-reduced-induced-closed-subscheme).
2. Its image is exactly closure {ξ}, since a finite map is closed
   (lem-weil-pbc-finite-closed-map-finite-fibres). Factor its reduced source through Z
   (lem-weil-pbc-reduced-source-factors-through-closed-subscheme).
3. Push forward its structure sheaf along the closed immersion into Y. This is coherent
   (lem-weil-pbc-closed-immersion-finite, pqf-lem-coherent-ft-locnoeth,
   lem-weil-pbc-finite-pushforward-coherent). Sectionwise pushforward composes.
4. On affine neighborhoods the generic stalk is (B/q)_p. Integrality and incomparability
   (lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-integral-incomparability) show
   this is the residue field of the chosen lift and therefore nonzero.
5. The stalk action factors through the residue field of ξ (def-weil-residue-field,
   def-weil-pbc-module-stalk), so the maximal ideal annihilates the stalk.
6. The pushforward has closed support (lem-weil-pbc-finite-type-module-support-closed).
   Closed-pushforward stalks put it inside i(Z) (lem-weil-pbc-closed-pushforward-stalks).
   It contains ξ by step 4, hence contains its closure and equals i(Z).
-/
theorem exists_coherent_pushforward_support_eq_range
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X) (ξ : X)
    [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    [IsClosedImmersion i] [IsIntegral Z]
    (hξ : IsGenericPoint ξ (Set.range i.base)) :
    ∃ F : Y.Modules,
      RingedSpace.IsCoherent Y.toRingedSpace F ∧
      {x : X | ¬ Subsingleton (((Modules.pushforward f).obj F).presheaf.stalk x : Type u)} =
        Set.range i.base ∧
      ∀ a : (X.toRingedSpace.presheaf.stalk ξ : Type u),
        a ∈ IsLocalRing.maximalIdeal (X.toRingedSpace.presheaf.stalk ξ) →
        ∀ s : ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
          ((Modules.pushforward f).obj F) : Type u),
          a • s = 0 := by
  sorry

end AlgebraicGeometry.Scheme
