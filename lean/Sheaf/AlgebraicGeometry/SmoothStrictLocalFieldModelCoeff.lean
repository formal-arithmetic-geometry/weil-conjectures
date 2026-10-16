/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCore
import Sheaf.RingTheory.StrictHenselizationTriples
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Separable
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PrimitiveElement
import Sheaf.RingTheory.HenselianLocalRootLifting
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Coefficient fields of a smooth strict localization

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04HX, 04GP, 06LN, 06LK and 04GG.
(blueprint: lem-sc-smooth-strict-local-field-model-coeff)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A coefficient field and its transcendence degrees in a smooth strict localization.
Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04HX, 04GP, 04GG, 06RR, 030N, 030H and 0A21.
(blueprint: lem-sc-smooth-strict-local-field-model-coeff)

Proof: apply smooth_strict_local_field_model_core to obtain the residue
isomorphism e with l = separableClosure (Y.residueField y) Omega and the
structural algebraic embedding Y.functionField -> Q = Frac(R).
The triples description of this strict henselization also makes R henselian.
Use rho = e composed with reduction. The displayed structural equations,
hK, hKappa (hκ in Lean) and hOmega imply that rho is K-linear: compose the
spectral maps with f, cancel the monomorphism Spec(kappa(y)) -> Y to identify
the maps on kappa(y), and use the injectivity of l -> Omega. All local and
domain structures are propositions, so these conclusions use the given
instances as well as the instances supplied by the core theorem.

The finite-type residue-field theorem makes kappa(y)/K finitely generated.
Since K is algebraically closed, it is perfect; choose a finite separating
transcendence basis t_1,...,t_a of kappa(y)/K. Choose lifts u_i in R using the
surjectivity of rho. Every nonzero polynomial P over K has P(t) nonzero;
therefore P(u) has nonzero residue and is a unit in R. Evaluation thus embeds
L = K(t_1,...,t_a) into R, compatibly with reduction. The empty basis gives
L = K. Since kappa(y)/L and l/kappa(y) are separable algebraic, l/L is
separable algebraic, and l is separably closed. Thus l is the directed union
of its finite separable subextensions E/L.

For such E choose a primitive element alpha with monic separable minimal
polynomial P over L. Map its coefficients to R. Its residual root alpha is
simple, as a Bezout identity for P and P' shows. Henselian lifting supplies
v in R with P(v)=0 and rho(v)=alpha. Evaluation factors through
E = L[T]/(P), giving an L-algebra map E -> R reducing to E -> l. Here
L[alpha] = L(alpha): Bezout with P expresses the inverse of every nonzero
polynomial in alpha as a polynomial in alpha. For any beta in E, the images
under two such maps are roots of its separable minimal polynomial with the
same residue and unit derivative. Simple-root uniqueness makes them equal.
It follows that the maps E -> R are unique and compatible under inclusions.
Their directed union defines a K-algebra map j : l -> R with rho composed
with j equal to the identity. Taking F = l with the induced K-algebra
structure gives a separably closed field. Since reduction is e inverse
composed with rho, its composite with j is bijective. Moreover l is algebraic
over kappa(y), so trdeg_K F = a.

The generic-point dimension formula gives trdeg_K Y.functionField = d.
The core theorem's structural equality makes its embedding into Q K-linear
for the K-algebra structure on Q induced by hK. Its algebraic image therefore
gives trdeg_K Q = d. The two K-structures on Q agree since j is K-linear.
The transcendence-degree tower formula for K -> F -> Q gives
 d = a + trdeg_F Q. Both d and a are finite, so trdeg_F Q is finite and equals
the natural subtraction d-a, which is the last displayed equality. -/
theorem smooth_strict_local_field_model_coeff
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f)
    [IsLocalRing (strictHenselizationRing s)]
    [IsDomain (strictHenselizationRing s)] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F),
      ∃ j : F →ₐ[K] strictHenselizationRing s,
        IsSepClosed F ∧
        Function.Bijective ((IsLocalRing.residue (strictHenselizationRing s)).comp
          j.toRingHom) ∧
        Algebra.trdeg K F = (a : Cardinal) ∧
        (letI := ((algebraMap (strictHenselizationRing s)
            (FractionRing (strictHenselizationRing s))).comp j.toRingHom).toAlgebra
         Algebra.trdeg F (FractionRing (strictHenselizationRing s)) =
           ((d - a : ℕ) : Cardinal)) := by
  sorry

end Scheme
end AlgebraicGeometry
