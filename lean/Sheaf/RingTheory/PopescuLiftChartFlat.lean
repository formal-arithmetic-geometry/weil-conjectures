/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.AnnihilatorElementFlatBaseChange
import Sheaf.RingTheory.EquationCountFibreDimensionFlat
import Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension
import Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension

/-! # Flat local maps on the prepared Popescu charts

Source: Stacks Project, Tag 07CP, the equation count for D_k and vanishing of the kernel
of D_k to D at primes containing pi.
(blueprint: lem-weil-pbc-popescu-lift-chart-flat).
-/

@[expose] public section

universe a c

namespace Algebra

/-- Flatness of the lifting algebra at a special-fibre prime on a prepared chart.

Source: Stacks Project, Tag 07CP (lemma-lifting), equation count for D_k and the final
local kernel calculation using equality of annihilators.
(blueprint: lem-weil-pbc-popescu-lift-chart-flat).

Proof: Put Q=R[x,z], u_l=f_l-pi z_l, and
p_{kl}=a_k z_l-sum_{j in E_k}h_{klj}z_j-pi g_{kl}. Define
D_k=Q/(u_j for j in E_k, p_{kl} for l outside E_k). Normalization makes p_{kl}=0
for l in E_k. This is a presentation with n+m variables and m equations.
The values of c on the original generators extend to all polynomials by algebra-map
extensionality and the scalar tower. Thus a_k avoids the pullback q_k of qD to D_k,
and pi belongs to q_k. Modulo pi, after inverting a_k, the cleared relations generate
all f_l from f_j, j in E_k. Eliminate each z_l outside E_k to identify the quotient
with (Cbar/pi Cbar)_{a_k}[z_j : j in E_k]. Prepared.smooth and its differential basis,
base change, and the polynomial differential decomposition give a smooth residue-field
fibre with differential rank (n-|E_k|)+|E_k|=n. Its topological dimension at the
fibre prime is n (not the Krull dimension of its local ring).
The equation-count flatness theorem gives flatness of R to the local ring (D_k)_{q_k}.
The key identity pi p_{kl}=-a_k u_l+sum h_{klj}u_j makes every u_l zero in (D_k)_{a_k}.
For another chart k', compare its conormal relation with that of k: the coefficient
b_j=a_{k'}h_{klj}-sum_{j' in E_{k'}}h_{k'lj'}h_{kj'j} is zero in Cbar_{a_k} by basis
independence. Clearing denominators and using the cleared f relations gives
 a_k^N b_j in I_{E_k}+pi^2P. Expanding the p relations then puts p_{k'l} in
pi(D_k)_{a_k}. The key identity also kills it by pi. In the flat local ring
(D_k)_{q_k}, flat base change of annihilators identifies Ann(pi) with Ann(pi^2).
Writing p_{k'l}=pi y, pi^2 y=0 therefore forces pi y=0. All generators of the kernel
D_k to D vanish in this local ring. The induced map of local rings is an isomorphism,
so its flatness transfers to D_{qD}. Since R_p to D_{qD} is obtained by localizing
the base R at the contraction p of qD, it is flat as well. No principal neighbourhood
annihilating the kernel is needed for this local flatness conclusion. -/
theorem popescu_lift_chart_flat (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] [IsNoetherianRing R] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (hAnnR : Module.annihilator R (Ideal.span ({π} : Set R)) =
      Module.annihilator R (Ideal.span ({π ^ 2} : Set R)))
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (q : PrimeSpectrum (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (k : Fin d.r) (hk : c (d.ε (d.reduced (d.a k))) ∉ q.asIdeal) :
    let qD := PrimeSpectrum.comap (Ideal.Quotient.mk _) q
    (Localization.localRingHom (PrimeSpectrum.comap (algebraMap R d.liftingAlgebra) qD).asIdeal
      qD.asIdeal (algebraMap R d.liftingAlgebra) rfl).Flat := by sorry

end Algebra
