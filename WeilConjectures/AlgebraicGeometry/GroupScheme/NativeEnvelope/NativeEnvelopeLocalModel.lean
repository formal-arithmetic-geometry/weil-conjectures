/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeLisseLocalFrobeniusModule

/-! # The local linear model of the native envelope

Source: latest blueprint, lem-wf-envelope-real, dual and direct-sum calculation.
(blueprint: lem-wf-envelope-real-native-local-model)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeEnvelope

/-- The native envelope has the local polynomial of V plus its contragredient dual.
No weight, embedding or reality hypothesis is used. The model V is the actual scalar
fibre of the normalized twist, with its invertible local Frobenius.
Source: latest blueprint, lem-wf-envelope-real.proof.md, local-factor paragraph;
lem-fd-condensed-fibre-linear-operations, dual and finite-sum clauses.
(blueprint: lem-wf-envelope-real-native-local-model).

Proof: use a finite-free pro-etale trivialization of F. Tensor with the constant line
has the same underlying module by the right unitor, so its fibre V is finite dimensional.
Equip V with the linear equivalence furnished by native Frobenius transport. This is M,
and its endomorphism is the native closedOperator, as in localFrobeniusModule.
The dual comparison in condensed_fibre_linear_operations identifies the internal-dual
fibre with Hom(V,K). Its Frobenius-compatibility equation identifies the operator with
f mapped to f composed with A inverse. The finite-sum comparison, followed by the
Fin 2 product coordinates, identifies the envelope fibre with V times Hom(V,K);
compatibility with both projections identifies Frobenius with the product operator.
Characteristic polynomials are invariant under this linear conjugacy; reversing them
and using basis independence gives the displayed equality for every finite basis.
For rank zero the vector spaces vanish and both reverse characteristic polynomials
are 1. No basis or model is chosen in any public data definition. -/
theorem envelope_local_model
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (b : (PadicAlgCl l)ˣ)
    (hF₀ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (normalizedTwist D l X₀ hl F b).carrier)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (n : ℕ)
    (e : Module.Basis (Fin n) (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D (realEnvelope D l X₀ hl F b).carrier
        (NativeCondensedModule.localClosedPoint D X₀ x i hi))) :
    NativeCondensedWeil.localFactorInBasis D l X₀ (realEnvelope D l X₀ hl F b)
        x i hi n e =
      let M := localFrobeniusModule D l X₀ (normalizedTwist D l X₀ hl F b) hF₀ x i hi
      (M.prod M.dual).localPolynomial := by
  sorry

end WeilConjectures.NativeEnvelope
