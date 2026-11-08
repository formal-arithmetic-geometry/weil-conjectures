/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.RingTheory.Etale.StandardEtale

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finiteness and étaleness of `adjoinRootCover`

For a monic polynomial `P`, the base change `adjoinRootCover S P` of `Spec Γ(S)[T]/(P)` is
finite locally free of degree `deg P`; when moreover `P'` is a unit modulo `P` it is étale.
Source: blueprint, lem-fd-as-cover, step (1); lem-weil-pbc-monic-quotient-free,
lem-weil-pbc-standard-etale-monic-derivative.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {P : Polynomial Γ(S, ⊤)}

/-- A monic polynomial whose derivative is a unit modulo it gives a standard étale pair with
`g = 1`. -/
def standardEtalePairOfIsUnitDerivative {R : Type*} [CommRing R] {Q : R[X]} (hQ : Q.Monic)
    (hd : IsUnit (AdjoinRoot.mk Q (derivative Q))) : StandardEtalePair R where
  f := Q
  monic_f := hQ
  g := 1
  cond := by
    obtain ⟨v, hv⟩ := hd.exists_right_inv
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective v
    rw [← map_mul, ← (AdjoinRoot.mk Q).map_one, AdjoinRoot.mk_eq_mk] at hv
    obtain ⟨r, hr⟩ := hv
    exact ⟨q, -r, 0, by rw [pow_zero]; linear_combination hr⟩

/-- `R[T]/(Q)` is étale when `Q` is monic and `Q'` is a unit modulo `Q`. -/
lemma Algebra.etale_adjoinRoot_of_isUnit_derivative {R : Type u} [CommRing R] {Q : R[X]}
    (hQ : Q.Monic) (hd : IsUnit (AdjoinRoot.mk Q (derivative Q))) :
    Algebra.Etale R (AdjoinRoot Q) := by
  let E := standardEtalePairOfIsUnitDerivative hQ hd
  have hmap : E.HasMap (AdjoinRoot.root Q) :=
    ⟨by simp [E, standardEtalePairOfIsUnitDerivative, AdjoinRoot.aeval_eq], by
      simp [E, standardEtalePairOfIsUnitDerivative]⟩
  have hX : aeval E.X Q = 0 := StandardEtalePair.hasMap_X.1
  let e : E.Ring ≃ₐ[R] AdjoinRoot Q := AlgEquiv.ofAlgHom (E.lift _ hmap)
    (AdjoinRoot.liftAlgHom Q (Algebra.ofId R E.Ring) E.X hX)
    (AdjoinRoot.algHom_ext (by simp)) (StandardEtalePair.hom_ext (by simp))
  exact Algebra.Etale.of_equiv e

variable (S P)

end AlgebraicGeometry
