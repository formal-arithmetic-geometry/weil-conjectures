/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Field.ULift

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Filtration

/-! # Persistence of components under equal Hilbert--Samuel specialization

Source: Bierstone--Milman--Temkin, arXiv:0905.3580v1, sections 6.1 and 6.3,
Remark 6.2; the schematic-closure argument in the DAG
(blueprint: lem-per-hilbert-specialization-component-persistence).

The ambient scheme is smooth and quasi-compact over the rational field, hence finite type.
The immersion makes the intrinsic scheme locally of finite type; quasi-compactness of its
structure morphism gives finite type. No reducedness hypothesis is imposed.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Equal extended Hilbert--Samuel sequences at specializing points retain precisely the
same irreducible components, and therefore the same sets of component dimensions.
Source: BMT arXiv:0905.3580v1, sections 6.1 and 6.3, Remark 6.2, with the following
schematic-closure argument
(blueprint: lem-per-hilbert-specialization-component-persistence).

Proof:
1. Finite type over Q makes X Noetherian, with finitely many irreducible components
   (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-noetherian-finitely-many-components`). Remove the components not containing
   z to obtain an open U containing z. Its inclusion j is quasi-compact
   (`lem-sfb-noetherian-open-immersion-qc`) and quasi-separated. Its scheme-theoretic image
   Y has quasi-coherent ideal I and support closure U
   (`lemma-nagata-scheme-image-ideal-qc`). Restriction to U is the identity image
   (`lemma-nagata-scheme-image-restrict-open`,
   `lemma-nagata-scheme-image-of-closed-immersion`), so I_z = 0 and H_Y(z) = H_X(z).
   Specialization puts x in Y.
2. The closed subscheme Y is finite type and has the induced locally closed smooth
   embedding. Upper semicontinuity, including nilpotents, from
   `lem-per-scheme-hilbert-samuel-test-presentations` gives H_Y(z) <=lex H_Y(x).
3. At x write R = O_X,x and O_Y,x = R/I. The local ring is Noetherian
   (`lem-weil-pbc-localization-noetherian`); its maximal-adic quotients have finite length
   (`lem-trf-maximal-adic-graded-length-bridge`). Their surjections to the corresponding
   quotients for Y, together with `lem-weil-pbc-length-additive-short-exact`, give
   h_Y,x <= h_X,x pointwise. The residue fields agree; summation preserves the inequality.
   Thus H_X(z) = H_Y(z) <=lex H_Y(x) <=lex H_X(x) = H_X(z), forcing equality.
4. Finite differences cancel the common summation exponent. Equality of all finite
   quotient lengths makes every kernel (I + m^(n+1))/m^(n+1) have length zero
   (`lem-weil-pbc-length-additive-short-exact`, `def-weil-pbc-module-length`). Hence I is
   contained in every power of m. Krull intersection for the finite module R gives I = 0
   (`lem-weil-pbc-krull-intersection-jacobson`).
5. Finite generation of the ideal on a Noetherian affine neighborhood gives an open V
   containing x on which I vanishes: annihilate finitely many generators after localization
   and multiply their denominators (empty product 1). Thus V lies in closure U, which lies
   in the finite closed union of components containing z.
6. For any component C containing x, V intersect C is nonempty and dense in C. Therefore
   C lies in that finite union; irreducibility and maximality force it to equal a component
   containing z. Conversely a closed component containing z contains its specialization x.
   The component families agree, and applying their subspace Krull dimensions gives the
   asserted equality of sets. -/
theorem components_eq_of_function_eq_specialization {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [QuasiCompact p] [IsImmersion i] [QuasiCompact (i ≫ p)]
    (z x : X) (hspecializes : x ∈ closure ({z} : Set X))
    (heq : function (i ≫ p) z = function (i ≫ p) x) :
    (∀ C : Set X, C ∈ irreducibleComponents X → (x ∈ C ↔ z ∈ C)) ∧
      {d : WithBot ℕ∞ | ∃ C : Set X,
        C ∈ irreducibleComponents X ∧ x ∈ C ∧ topologicalKrullDim C = d} =
      {d : WithBot ℕ∞ | ∃ C : Set X,
        C ∈ irreducibleComponents X ∧ z ∈ C ∧ topologicalKrullDim C = d} := by
  sorry

end AlgebraicGeometry.HilbertSamuel
