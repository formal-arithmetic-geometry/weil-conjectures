/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.RingTheory.GRing
import Mathlib.RingTheory.Extension.ExtendScalars
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Geometric regularity and the first cotangent homology of the residue field

Source: Stacks Project, More on Algebra, Proposition Tag 07E5, implication (1) ⇒ (3)
(blueprint: lem-weil-pbc-geometrically-regular-h1-injective).
-/

universe u v

namespace Algebra

/-- A geometrically regular Noetherian local algebra over a field of positive characteristic
is regular local, and the canonical map from the first cotangent homology of its residue field
into the maximal ideal modulo its square is injective. The residue field is the canonical
quotient `K = A / maximalIdeal A`. The map is the composite of `H1Cotangent.map k A K K`
with the surjection-to-conormal equivalence for `A → K`; the latter's target is the cotangent
module of the kernel of the residue map, namely the maximal ideal modulo its square.

Source: Stacks Project, More on Algebra, Proposition Tag 07E5, implication (1) ⇒ (3)
(blueprint: lem-weil-pbc-geometrically-regular-h1-injective).

Proof, following the node's ten steps:
1. The trivial finite purely inseparable extension in def-weil-pbc-g-ring gives regularity
   of A. Locality gives regular locality; lem-weil-pbc-regular-local-cotangent-dimension
   identifies its dimension d with the dimension of its conormal space.
2. Use lem-weil-pbc-nl-presentation-h1-functoriality and
   lem-weil-pbc-jacobi-zariski-surjection-h1 for the stated composite. By
   lem-weil-pbc-jacobi-zariski-connecting-map-naturality, its composite with the conormal
   differential equals the differential comparison c after the Jacobi-Zariski boundary.
   The boundary is injective by lem-weil-pbc-jacobi-zariski-homology-sequence and
   lem-weil-pbc-field-char-p-h1-cotangent-vanishing. It suffices that c is injective.
3. Choose a basis of differentials using def-weil-pbc-kahler-differentials. Reduce injectivity
   of c to independence of the images of every finite independent family da₁, …, daₙ.
4. Adjoin their p-th roots. By lem-weil-pbc-pth-roots-extension-degree the extension has
   degree pⁿ; its polynomial quotient presentation, together with
   lem-weil-pbc-finite-dimensional-domain-is-field, identifies it with k' and shows it is
   finite purely inseparable.
5. By lem-weil-pbc-purely-inseparable-base-change-local-ring, A' = A ⊗ k' is finite free and
   local with finite residue extension K'/K. Geometric regularity makes A' regular local.
   The flat height formula lem-weil-pbc-flat-height-formula and the zero-dimensional fibre
   give dim A' = d; its conormal space also has dimension d.
6. By lem-weil-pbc-pth-root-presentation-differentials, after tensoring with K', the comparison
   β of absolute differentials has kernel spanned by the n chosen differentials and cokernel
   of dimension n. The relative differentials are free, so this tensoring preserves the
   needed exact sequences. Thus dim ker β ≤ n.
7. The Jacobi-Zariski sequence, field H₁ vanishing, the surjection-to-conormal equivalence,
   and connecting-map naturality give exact conormal rows for A and A'. Tensor the first
   row with K', which is flat over K.
8. Apply lem-weil-pbc-cartier-equality and the Jacobi-Zariski sequence to the finite extension
   K'/K: the comparison γ on residue-field differentials has kernel and cokernel of the
   same finite dimension.
9. The conormal comparison α has source and target of dimension d. The squares commute
   by compatibility of differentials with ring maps. Apply lem-weil-pbc-snake-lemma-modules
   to the conormal rows: cancellation of the kernel/cokernel dimensions for α and γ gives
   dim ker β = dim coker β = n.
10. The n spanning differentials in ker β are therefore independent over K', and hence
    over K. Step 3 gives injectivity of c and step 2 gives injectivity of the stated map.
-/
theorem isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hA : IsGeometricallyRegular k A) :
    let K := IsLocalRing.ResidueField A
    let P := Extension.ofSurjective (Algebra.ofId A K) (IsLocalRing.residue_surjective)
    IsRegularLocalRing A ∧
      Function.Injective
        (P.h1CotangentEquivCotangent.toLinearMap.comp (H1Cotangent.map k A K K)) := by
  sorry

end Algebra
