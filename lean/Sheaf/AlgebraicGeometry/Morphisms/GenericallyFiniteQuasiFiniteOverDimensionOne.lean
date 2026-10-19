/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.RingTheory.AffineDimensionInequality
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Generic algebraicity gives quasi-finiteness over dimension one

Source: Stacks Project, Varieties, Tag 0AB6, lemma `quasi-finite-in-codim-1`, condition (1)
(blueprint: lem-per-generically-finite-quasifinite-over-dimension-one).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A locally finite type morphism with algebraic residue-field extensions at generic points
is quasi-finite at every point over a point whose local ring is Noetherian of Krull dimension
at most one, in the sense of Stacks Project Tag 0AB6, condition (1).
(blueprint: lem-per-generically-finite-quasifinite-over-dimension-one).

Proof (Stacks Project, Varieties, Tag 0AB6, condition (1), with the affine localization
argument expanded): choose affine neighborhoods of a point over `s`, localize the target
at its prime, and base change the finite-type affine algebra to the resulting local ring.
Transfer algebraicity from generic points of components through localization. For each prime in
the closed fibre, apply the dimension inequality to the quotient domains: the residue field has
transcendence degree zero over the residue field of the base. Thus every point of the finite-type
closed fibre over the residue field is closed, so the fibre is finite and discrete. The finite
fibre criterion for `IsQuasiFiniteAtPoint` then gives the conclusion. The proof uses
`lem-weil-pbc-lft-affine-pairs`, `lem-weil-pbc-affine-open-stalk-localization`,
`lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-localization-base-change`,
`lem-weil-pbc-spec-irreducible-components-minimal-primes`,
`lem-sc-irreducible-components-cover`, `lem-weil-pbc-localization-prime-residue-field-iso`,
`lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`,
`lem-trf-affine-dimension-inequality`, `lem-kun-closed-point-field`,
`lem-weil-pbc-finite-type-dim-zero-artinian`, and `pqf-lem-locqf-fibre-discrete`.
-/
theorem quasiFiniteAtPoint_of_generic_algebraic_of_local_dim_le_one
    {Z S : Scheme.{u}} (g : Z ⟶ S) [LocallyOfFiniteType g] (s : S)
    [IsNoetherianRing (S.presheaf.stalk s)]
    (hdim : ringKrullDim (S.presheaf.stalk s) ≤ 1)
    (hgeneric : ∀ (T : Set Z), T ∈ irreducibleComponents Z →
      ∀ (η : Z), IsGenericPoint η T →
        @Algebra.IsAlgebraic (S.residueField (g η)) (Z.residueField η) _ _
          (g.residueFieldMap η).hom.toAlgebra) :
    ∀ z : Z, g z = s → Scheme.Hom.IsQuasiFiniteAtPoint g z := by
  sorry

end AlgebraicGeometry
