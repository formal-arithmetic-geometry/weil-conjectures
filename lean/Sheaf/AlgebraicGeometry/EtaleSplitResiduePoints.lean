/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField
import Sheaf.AlgebraicGeometry.FibreProductPointResidueField
import Sheaf.FieldTheory.SeparableSplitPurelyInseparableResidueFields

/-!
# Splitting the residue fields of finitely many points by an étale neighborhood

Source: Stacks Project, More on Morphisms, proof of Lemma 02LM, lines 12056--12079.
(blueprint: lem-weil-pbc-etale-split-residue-points).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Source: Stacks Project, More on Morphisms, proof of Lemma 02LM,
lines 12056--12079 (blueprint: lem-weil-pbc-etale-split-residue-points).

Proof:
1. Transport the finite extensions at `f (x i)` to extensions of `κ(s)` using `hx`.
   Apply `exists_separable_split_purelyInseparable_prime_quotients` to these fields.
2. Realize the resulting finite separable extension `L/κ(s)` as the residue field of
   an étale neighborhood by `Scheme.exists_etale_neighbourhood_prescribed_residueField`.
   Its compatible field isomorphism transports the tensor products and their prime spectra.
3. The fibre-product point correspondence identifies points over `(x i,u)` with the primes
   of `κ(u) ⊗[κ(s)] κ(x i)`. Those spectra are finite; choose bijections with `Fin (m i)`.
   Each list is injective and exhausts exactly the points over that pair.
4. Every tensor prime quotient is a finite purely inseparable field over `κ(u)` by step 1.
   `exists_residueField_equiv_ofPointTensor` identifies it with the point's residue field,
   compatibly with the second projection, giving the asserted extension properties.
The empty family requires no points; choose the identity neighborhood. No distinctness or
isolatedness is needed: only the individual finite residue extensions are used. -/
theorem exists_etale_split_residue_points
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (n : ℕ) (x : Fin n → X)
    (hx : ∀ i, f (x i) = s)
    (hfinite : ∀ i, letI := (f.residueFieldMap (x i)).hom.toAlgebra
      Module.Finite (S.residueField (f (x i))) (X.residueField (x i))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U), Etale φ ∧ φ u = s ∧
      ∃ (m : Fin n → ℕ) (y : (i : Fin n) → Fin (m i) → ↥(pullback f φ)),
        (∀ i, Function.Injective (y i)) ∧
        (∀ i j, pullback.fst f φ (y i j) = x i) ∧
        (∀ i j, ∃ (hy : pullback.snd f φ (y i j) = u),
          letI := ((U.residueFieldCongr hy.symm).hom ≫
            (pullback.snd f φ).residueFieldMap (y i j)).hom.toAlgebra
          Module.Finite (U.residueField u) ((pullback f φ).residueField (y i j)) ∧
            IsPurelyInseparable (U.residueField u)
              ((pullback f φ).residueField (y i j))) ∧
        (∀ (i : Fin n) (w : ↥(pullback f φ)),
          pullback.snd f φ w = u → pullback.fst f φ w = x i →
            ∃ j : Fin (m i), w = y i j) := by
  sorry

end AlgebraicGeometry
