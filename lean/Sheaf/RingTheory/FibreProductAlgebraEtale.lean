/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.RingTheory.FibreProductAlgebraFlatPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods

/-!
# Etaleness of a patched algebra over a ring fibre product

Source: Stacks Project, More on Algebra, Situation 08KH and Lemma 08KQ (5),
implication from the two component algebras to the patched algebra
(blueprint: lem-sfb-fibre-product-algebra-etale).

The canonical map `CommRingCat.FibreProductAlgebra.structureMap` is the map
`B ×[A] A' → D ×[C] C'` of the node. Pushouts represent tensor products;
`pushout q c` represents `C'/IC'` for `I = ker q`. The isomorphism `φ` and
its compatibility equation encode exactly the given A-algebra isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat.FibreProductAlgebra

/-- Compatible etale algebras patch to an etale algebra along an arbitrary surjection.
Source: Stacks Project, Situation 08KH and Lemma 08KQ (5), reverse implication
(blueprint: lem-sfb-fibre-product-algebra-etale).

Proof:
1. Etale algebras are flat [lem-weil-pbc-etale-algebra-flat] and finitely presented
   [def-weil-etale-morphism, lem-weil-pbc-lfp-affine-opens-finite-presentation].
   Apply [lem-sfb-fibre-product-algebra-flat-presentation] to conclude that E/R is
   flat and finitely presented. Its spectrum morphism is flat
   [lem-weil-pbc-flat-ring-map-iff-flat-affine] and locally of finite presentation
   [def-sbc-locally-finite-presentation].
2. The canonical recovery maps E tensor_R B to D and E tensor_R A' to C' are
   bijective by [lem-sfb-patched-module-base-change]. Their formulas on pure tensors
   preserve multiplication and units, hence give algebra isomorphisms. The map
   R to B is surjective by lifting along q, with kernel J consisting of (0,i), i in I.
3. For a field map u : R to k killing J, u factors through B. Reassociation and the
   first recovery map identify E tensor_R k with D tensor_B k. The reassociation
   sends (e tensor b) tensor t to e tensor u(b)t, with inverse sending e tensor t
   to (e tensor 1) tensor t; balancing gives the inverse identities. This fibre is
   etale by [lem-weil-pbc-etale-ring-base-change].
4. Otherwise choose h = (0,i) in J with u(h) nonzero. Then u factors through R_h.
   By [lem-sfb-ring-fibre-product-spectrum], R_h identifies with A'_i, since the
   B and A localizations at zero are zero rings. The induced map A' to k and the
   second recovery map identify E tensor_R k with C' tensor_A' k. The same
   reassociation formulas as in step 3 give mutually inverse algebra maps. This
   fibre is etale by [lem-weil-pbc-etale-ring-base-change].
5. Apply this dichotomy to every residue field of R. The scheme-theoretic fibres
   are the corresponding tensor-product spectra [lem-weil-pbc-fibre-product-affine-spectra].
   The flat, locally finitely presented spectrum morphism therefore has etale
   neighbourhoods at all source points [lem-sbc-flat-fibre-etale-neighbourhoods].
   These cover the source, so [lem-weil-pbc-etale-local-on-source] gives etaleness.
   The empty source is covered by the empty family. No nilpotence, Noetherian,
   finite-generation, or nonzero-ring hypothesis is needed.
-/
theorem etale_of_components
    {A A' B D C' : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (hq : Function.Surjective q) (d : B ⟶ D) (c : A' ⟶ C')
    (φ : pushout b d ≅ pushout q c)
    (hφ : pushout.inl b d ≫ φ.hom = pushout.inl q c)
    (hd : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map d))
    (hc : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map c)) :
    AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (structureMap b q d c φ hφ)) := by
  sorry

end CommRingCat.FibreProductAlgebra
