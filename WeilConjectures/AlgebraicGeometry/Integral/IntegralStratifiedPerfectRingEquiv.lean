/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile

/-! # Completed coefficients under isomorphisms of coefficient data

A ring isomorphism `φ : A ≃+* A'` carrying the ideal of one adic coefficient datum onto the
ideal of another identifies all finite quotients, hence the quotient coefficient sheaves and
their limit. Restriction of scalars along this completed isomorphism transports completed
derived objects, intrinsic completeness and the uniform reduction profile.

Source: Bhatt--Scholze, Proposition 6.6.11 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace AdicCoefficients

variable (T : Scheme.{u})

/-- Postcomposition is functorial in the finite coefficient ring.
(auxiliary; not a blueprint node). -/
theorem functionPresheafMap_comp {Λ Λ' Λ'' : Type (u + 1)} [CommRing Λ] [CommRing Λ']
    [CommRing Λ''] [Finite Λ] [Finite Λ'] [Finite Λ''] (f : Λ →+* Λ') (g : Λ' →+* Λ'') :
    functionPresheafMap T (g.comp f) = functionPresheafMap T f ≫ functionPresheafMap T g := by
  ext U s
  rfl

/-- Postcomposition with the identity is the identity.
(auxiliary; not a blueprint node). -/
theorem functionPresheafMap_id (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    functionPresheafMap T (RingHom.id Λ) = 𝟙 _ := by
  ext U s
  rfl

/-- The coefficient sheaf map is functorial. (auxiliary; not a blueprint node). -/
theorem coefficientMap_comp' {Λ Λ' Λ'' : Type (u + 1)} [CommRing Λ] [CommRing Λ']
    [CommRing Λ''] [Finite Λ] [Finite Λ'] [Finite Λ''] (f : Λ →+* Λ') (g : Λ' →+* Λ'') :
    coefficientMap T (g.comp f) = coefficientMap T f ≫ coefficientMap T g := by
  rw [coefficientMap, coefficientMap, coefficientMap, functionPresheafMap_comp, Functor.map_comp]

/-- The coefficient sheaf map of the identity. (auxiliary; not a blueprint node). -/
theorem coefficientMap_id' (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    coefficientMap T (RingHom.id Λ) = 𝟙 _ := by
  rw [coefficientMap, functionPresheafMap_id]
  exact (presheafToSheaf _ _).map_id _

/-- A ring isomorphism of finite coefficient rings induces an isomorphism of coefficient
sheaves. (auxiliary; not a blueprint node). -/
def coefficientRingIso {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Finite Λ]
    [Finite Λ'] (e : Λ ≃+* Λ') : coefficientRing T Λ ≅ coefficientRing T Λ' where
  hom := coefficientMap T e.toRingHom
  inv := coefficientMap T e.symm.toRingHom
  hom_inv_id := by
    rw [← coefficientMap_comp', ← coefficientMap_id']
    congr 1
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    rw [← coefficientMap_comp', ← coefficientMap_id']
    congr 1
    ext x
    exact e.apply_symm_apply x

end AdicCoefficients

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

/-- The induced isomorphism of positive quotients. (auxiliary; not a blueprint node). -/
def AdicCoefficientDatum.quotientRingEquiv (n : ℕ) :
    A ⧸ d.ideal ^ (n + 1) ≃+* A' ⧸ d'.ideal ^ (n + 1) :=
  Ideal.quotientEquiv _ _ φ (by rw [← hφ, Ideal.map_pow]; rfl)

theorem AdicCoefficientDatum.quotientRingEquiv_mk (n : ℕ) (a : A) :
    d.quotientRingEquiv d' φ hφ n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) :=
  rfl

/-- The quotient isomorphisms commute with the quotient transitions.
(auxiliary; not a blueprint node). -/
theorem AdicCoefficientDatum.quotientRingEquiv_factor (n : ℕ) :
    (Ideal.Quotient.factorPowSucc d'.ideal (n + 1)).comp
        (d.quotientRingEquiv d' φ hφ (n + 1)).toRingHom =
      (d.quotientRingEquiv d' φ hφ n).toRingHom.comp
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

/-- The map of finite quotient coefficient systems. (auxiliary; not a blueprint node). -/
def AdicCoefficientDatum.ringSystemHom (T : Scheme.{u}) :
    pbcAdicRings T d ⟶ pbcAdicRings T d' :=
  letI := d.quotientFinite
  letI := d'.quotientFinite
  NatTrans.ofOpSequence (fun n ↦ (AdicCoefficients.coefficientRingIso T
      (d.quotientRingEquiv d' φ hφ n)).hom) (fun n ↦ by
    simp only [pbcAdicRings, AdicCoefficients.ringSystem,
      Functor.ofOpSequence_map_homOfLE_succ, AdicCoefficients.coefficientRingIso]
    rw [← AdicCoefficients.coefficientMap_comp', ← AdicCoefficients.coefficientMap_comp',
      d.quotientRingEquiv_factor d' φ hφ n])

instance (T : Scheme.{u}) : IsIso (d.ringSystemHom d' φ hφ T) := by
  have (n : ℕᵒᵖ) : IsIso ((d.ringSystemHom d' φ hφ T).app n) := by
    letI := d.quotientFinite
    letI := d'.quotientFinite
    change IsIso (AdicCoefficients.coefficientRingIso T
      (d.quotientRingEquiv d' φ hφ n.unop)).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The isomorphism of completed coefficient rings induced by a datum isomorphism.
(auxiliary; not a blueprint node). -/
def AdicCoefficientDatum.completionIso (T : Scheme.{u}) :
    pbcAdicCompletion T d ≅ pbcAdicCompletion T d' :=
  HasLimit.isoOfNatIso (asIso (d.ringSystemHom d' φ hφ T))

/-- The completed isomorphism is compatible with the level projections.
(auxiliary; not a blueprint node). -/
theorem AdicCoefficientDatum.completionIso_hom_projection (T : Scheme.{u}) (n : ℕ) :
    (d.completionIso d' φ hφ T).hom ≫ pbcAdicProjection T d' n =
      pbcAdicProjection T d n ≫ (d.ringSystemHom d' φ hφ T).app (op n) := by
  simp only [completionIso, pbcAdicProjection, HasLimit.isoOfNatIso_hom_π, asIso_hom]

/-- Restriction of scalars along the inverse completed isomorphism: the transport of
completed derived objects from `d` to `d'`. (auxiliary; not a blueprint node). -/
abbrev AdicCoefficientDatum.transportDerived (T : Scheme.{u}) :
    PbcCompletedDerived T d ⥤ PbcCompletedDerived T d' :=
  pbcDerivedRestrict (d.completionIso d' φ hφ T).inv

/-- Intrinsic completeness transports along an isomorphism of coefficient data.
Source: Stacks Tags 099M and 099N (auxiliary; not a blueprint node).
Proof: by the normalized Roos triangle, completeness of `K` means that the canonical map
from `K` to the product of its reductions is the first map of a derived-limit triangle
for the reduction transitions, with the canonical unit legs. Restriction along the
completed isomorphism is an exact equivalence preserving products; since it is
compatible with the level projections, the scalar-extension adjunctions identify it with
the reductions of the transported object, their units and transitions. Hence the
transported object has a derived-limit Roos triangle with the canonical legs, so its
completion unit is invertible. -/
theorem AdicCoefficientDatum.transport_intrinsicallyComplete (T : Scheme.{u})
    (K : PbcCompletedDerived T d) (hK : PbcIsIntrinsicallyComplete T d K) :
    PbcIsIntrinsicallyComplete T d' ((d.transportDerived d' φ hφ T).obj K) := by
  sorry

/-- The uniform reduction profile transports along an isomorphism of coefficient data.
Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node).
Proof: the completed isomorphism is compatible with the level projections and the quotient
isomorphisms with the constant level comparisons; by uniqueness of scalar extension the
constant reductions of the transported object are the restrictions of those of `K` along
the constant quotient ring isomorphisms. This exact equivalence preserves the cohomological
bounds and identifies the cohomology sheaves; constructibility is invariant under
restriction of scalars along an isomorphism of constant finite coefficient rings, since
inverse image, slice restriction and constant module sheaves commute with it. -/
theorem AdicCoefficientDatum.transport_uniformReductionProfile (T : Scheme.{u})
    (K : PbcCompletedDerived T d) (hK : PbcUniformReductionProfile T d K) :
    PbcUniformReductionProfile T d' ((d.transportDerived d' φ hφ T).obj K) := by
  sorry

end RingEquiv

end AlgebraicGeometry.Scheme
