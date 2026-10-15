/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.AlgebraicGeometry.FiniteIffProperFiniteFibres

/-!
# Projective morphisms with finite geometric fibres are finite

Source: the Weil conjectures blueprint, chapter `sec-smooth-purity`, unit `sk-prop-sf-cbc`,
lemma `lem-fin-projective-finite-fibres`; Stacks Project, Tag 02OG, using Tag 01WC
(blueprint: lem-fin-projective-finite-fibres).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A projective morphism with Noetherian target and finite geometric fibres is finite.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-projective-finite-fibres`;
Stacks Project, Tags 01WC and 02OG (blueprint: lem-fin-projective-finite-fibres).

Proof outline from the DAG:
1. Projectivity implies properness (`lem-pc-projective-proper`, Tag 01WC). The target is
   locally Noetherian by hypothesis (`pqf-def-locnoeth`).
2. For each `t`, the inclusion of its residue field into its algebraic closure is faithfully
   flat (`lem-weil-pbc-field-extension-base-change-faithfully-flat`), using the canonical
   isomorphism of the scalar-extension tensor product with the algebraic closure. Its spectrum
   map is surjective (`lem-weil-pbc-faithfully-flat-surjective-spectrum`). Surjectivity is
   preserved by base change (`lem-weil-pbc-surjective-base-change`), so the geometric fibre
   surjects onto the ordinary fibre (`def-weil-geometric-fibre`). The latter therefore has
   finitely many points, including when empty. The fibre homeomorphism identifies these with
   the set-theoretic fibre (`def-pc-scheme-fibre`).
3. Apply `thm-pqf-finite-iff-proper-finite-fibres`, implication (2) to (1), to the proper
   morphism with finite ordinary fibres over the locally Noetherian target (Tag 02OG). -/
theorem isFinite_of_isProjective_of_finite_geometricFibres
    {D T : Scheme.{u}} (f : D ⟶ T) [IsProjective f]
    [IsLocallyNoetherian T] [CompactSpace T]
    (hf : ∀ t : T, Finite ((pullback f
      (Spec.map (CommRingCat.ofHom
        (algebraMap (T.residueField t) (AlgebraicClosure (T.residueField t)))) ≫
          T.fromSpecResidueField t)) : Scheme.{u})) :
    IsFinite f := by
  sorry

end AlgebraicGeometry
