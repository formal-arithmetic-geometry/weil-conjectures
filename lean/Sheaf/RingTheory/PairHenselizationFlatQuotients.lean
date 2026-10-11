/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.PairHenselization
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness and ideal-power quotients of a pair henselization

Source: Stacks Project, More on Algebra, Lemma 15.12.2, Tag 0AGU
(blueprint: lem-weil-pbc-henselization-flat-quotients).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The structure map of the pair henselization is flat and induces isomorphisms on
quotients by every positive power of the ideal. The cocone and its colimit condition
are exactly those in `pair_henselization`; its vertex is `Aʰ`, and its map is `η`.
The extended ideal is `I.map η`, and `Ideal.map_pow` identifies the extension of
`I ^ n` with `(I.map η) ^ n`.
Source: Stacks Project, More on Algebra, Lemma 15.12.2, Tag 0AGU
(blueprint: lem-weil-pbc-henselization-flat-quotients).

Proof (the four steps of the node):
1. Use `lem-weil-pbc-pair-henselization` to express the henselization as the filtered
   colimit of étale A-algebras whose quotient modulo I is canonically A/I. Products of
   generators, or `Ideal.map_pow`, identify the extended powers of I.
2. Each stage is flat by `lem-weil-pbc-etale-algebra-flat`. The underlying A-module
   of the colimit is the filtered colimit of the stage modules by
   `lem-weil-pbc-filtered-colimit-algebras-elementwise`. Flatness follows from
   `lem-weil-pbc-filtered-colimit-flat-modules` and `def-weil-pbc-flat-ring-map`.
3. For each positive n, `lem-weil-pbc-flat-iso-mod-ideal-powers` gives the canonical
   isomorphism A/Iⁿ → B/IⁿB at every stage. These commute with all transition maps
   since they are induced by the A-algebra structure maps.
4. The index category is nonempty filtered, hence connected. Apply
   `lem-weil-pbc-colimit-constant-connected-diagram` to the constant A/Iⁿ diagram.
   Quotients of the filtered algebra colimit are colimits of the stage quotients by
   `lem-weil-pbc-filtered-colimit-algebras-elementwise`. Taking the colimit of the
   compatible stage isomorphisms proves bijectivity of the stated quotient map. -/
theorem pair_henselization_flat_quotients (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun B : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map B.hom.hom) B.hom.hom
            Ideal.le_comap_map))))
    (hc : IsColimit c) :
    RingHom.Flat c.pt.hom.hom ∧
      ∀ n : ℕ, 1 ≤ n →
        Function.Bijective (Ideal.quotientMap ((I ^ n).map c.pt.hom.hom) c.pt.hom.hom
          Ideal.le_comap_map) := by
  sorry

end RingTheory
