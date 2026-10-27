/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Bounded finite-projective product-Hom dual involution

Source: Stacks Project, More on Algebra, Tags 07VI, 0FNG and 0A8H.
(blueprint: lem-trf-finite-projective-hom-dual-involution).

The coordinate equivalences use the existing cochain projection and insertion.
The scalar dual is exactly the recorded module-valued product total Hom complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {B : Type u} [CommRing B]

/-- The ring in degree zero, the target of the scalar Hom dual.
Source: Stacks, Tags 07VI and 0A8H
(blueprint: lem-trf-finite-projective-hom-dual-involution). -/
abbrev moduleScalarDualTarget (B : Type u) [CommRing B] :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)

/-- The scalar dual, retaining the product Hom complex and its differential.
Source: Stacks, Tags 07VI and 0A8H
(blueprint: lem-trf-finite-projective-hom-dual-involution). -/
abbrev moduleScalarDual (P : CochainComplex (ModuleCat.{u} B) ℤ) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  moduleHomComplex P (moduleScalarDualTarget B)

/-- Projection to the unique potentially nonzero Hom coordinate, with inverse insertion.
The equation `i + r = 0` permits using the same projection without degree casts.
Source: Stacks, Tags 0A8H and 07VI
(blueprint: lem-trf-finite-projective-hom-dual-involution). -/
def moduleScalarDualCoordinates (P : CochainComplex (ModuleCat.{u} B) ℤ)
    (i r : ℤ) (h : i + r = 0) :
    (moduleScalarDual P).X r ≃ₗ[B] Module.Dual B (P.X i) :=
  ({ HomComplex.Cochain.toSingleEquiv h with
      map_smul' := fun _ _ ↦ rfl } :
    HomComplex.Cochain P (moduleScalarDualTarget B) r ≃ₗ[B]
      (P.X i ⟶ ModuleCat.of B B)).trans ModuleCat.homLinearEquiv

/-- The double-dual coordinates obtained by projecting twice and transposing the
inverse of the first projection. No choice of an abstract biduality map is made.
Source: Stacks, Tags 0A8H and 07VI
(blueprint: lem-trf-finite-projective-hom-dual-involution). -/
def moduleScalarBidualCoordinates (P : CochainComplex (ModuleCat.{u} B) ℤ) (p : ℤ) :
    (moduleScalarDual (moduleScalarDual P)).X p ≃ₗ[B]
      Module.Dual B (Module.Dual B (P.X p)) :=
  (moduleScalarDualCoordinates (moduleScalarDual P) (-p) p (neg_add_cancel p)).trans
    (moduleScalarDualCoordinates P p (-p) (add_neg_cancel p)).symm.dualMap

/-- Bounded finite-projective Hom duality, with its signed chain involution and naturality.
Source: Stacks, Tag 07VI, proof of lemma-dual-perfect-complex; Tag 0FNG, item-evaluation;
Tag 0A8H, section-hom-complexes
(blueprint: lem-trf-finite-projective-hom-dual-involution).

Proof:
1. The degree-r product has just the potentially nonzero coordinate i=-r. Projection
and insertion give moduleScalarDualCoordinates. Applying this twice gives
moduleScalarBidualCoordinates. Projection and insertion commute with precomposition,
so both coordinate identifications are natural.
2. Since B[0] has zero differential, the total Hom formula gives
D(phi)=(-1)^(r+1) phi d_P in degree r. Applying the formula a second time gives
D(u)(psi)=(-1)^(p+1)(-1)^(-p)u(psi d_P)=-u(psi d_P), the negative double transpose.
3. Outside [-b,-a], P^(-r) is zero, so its dual is zero. For every term, the
finite-projective duality input lem-sf-finite-projective-dual (Mathlib Module.dual_finite
and Module.dual_projective) gives finite projectivity of its dual.
4. Insert (-1)^p ev(x) in the degree -p coordinate, zero elsewhere. When p+q=0,
pq=-p^2 has the parity of p, giving the homogeneous sign (-1)^(pq).
The double-dual differential from step 2 makes these components a chain map.
5. By lem-sf-finite-projective-dual, ordinary evaluation is an isomorphism
(Mathlib Module.evalEquiv). Its inverse multiplied by (-1)^p is a two-sided inverse
to the component in step 4. Multiplying the chain identity by these inverse components
shows they form the inverse chain map.
6. Precomposition by f has coordinate phi ↦ phi f. Double precomposition thus sends
u to (phi' ↦ u(phi' f)). Evaluating this on (-1)^p ev(x) gives
(-1)^p phi'(f(x)), proving naturality of the specified signed evaluation isomorphisms.
All identities hold over the zero ring and in characteristic two as well. -/
theorem finiteProjective_homDual_involution
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ) (hab : a ≤ b)
    (hP : ∀ p : ℤ, p < a ∨ b < p → IsZero (P.X p))
    [∀ p : ℤ, Module.Finite B (P.X p)] [∀ p : ℤ, Module.Projective B (P.X p)] :
    (∀ (r : ℤ) (z : (moduleScalarDual P).X r),
      moduleScalarDualCoordinates P (-(r + 1)) (r + 1) (neg_add_cancel (r + 1))
          ((moduleScalarDual P).d r (r + 1) z) =
        (r + 1).negOnePow •
          (moduleScalarDualCoordinates P (-r) r (neg_add_cancel r) z).comp
            (P.d (-(r + 1)) (-r)).hom) ∧
    (∀ (p : ℤ) (z : (moduleScalarDual (moduleScalarDual P)).X p),
      moduleScalarBidualCoordinates P (p + 1)
          ((moduleScalarDual (moduleScalarDual P)).d p (p + 1) z) =
        -(P.d p (p + 1)).hom.dualMap.dualMap (moduleScalarBidualCoordinates P p z)) ∧
    (∀ r : ℤ, r < -b ∨ -a < r → IsZero ((moduleScalarDual P).X r)) ∧
    (∀ r : ℤ, Module.Finite B ((moduleScalarDual P).X r) ∧
      Module.Projective B ((moduleScalarDual P).X r)) ∧
    ∃ δ : P ≅ moduleScalarDual (moduleScalarDual P),
      (∀ (p : ℤ) (x : P.X p),
        moduleScalarBidualCoordinates P p (δ.hom.f p x) =
          p.negOnePow • Module.Dual.eval B (P.X p) x) ∧
      (∀ (p : ℤ) (z : (moduleScalarDual (moduleScalarDual P)).X p),
        δ.inv.f p z = p.negOnePow •
          (Module.evalEquiv B (P.X p)).symm (moduleScalarBidualCoordinates P p z)) ∧
      (∀ (p q : ℤ) (hpq : p + q = 0) (x : P.X p)
          (φ : (moduleScalarDual P).X q),
        (((δ.hom.f p x).v q 0 ((add_comm q p).trans hpq)) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of B B)).hom).hom φ =
          (p * q).negOnePow • (moduleScalarDualCoordinates P p q hpq φ) x) ∧
      (∀ (p q r : ℤ) (h : q + p = r) (hr : r ≠ 0) (x : P.X p),
        (δ.hom.f p x).v q r h = 0) ∧
      (∀ (Q : CochainComplex (ModuleCat.{u} B) ℤ) (c d : ℤ) (hcd : c ≤ d)
          (hQ : ∀ p : ℤ, p < c ∨ d < p → IsZero (Q.X p))
          [∀ p : ℤ, Module.Finite B (Q.X p)] [∀ p : ℤ, Module.Projective B (Q.X p)]
          (f : P ⟶ Q),
        (∀ (r : ℤ) (z : (moduleScalarDual Q).X r),
          moduleScalarDualCoordinates P (-r) r (neg_add_cancel r)
              ((moduleHomPrecomp (moduleScalarDualTarget B) f).f r z) =
            (moduleScalarDualCoordinates Q (-r) r (neg_add_cancel r) z).comp
              (f.f (-r)).hom) ∧
        (∀ (p : ℤ) (z : (moduleScalarDual (moduleScalarDual P)).X p),
          moduleScalarBidualCoordinates Q p
              ((moduleHomPrecomp (moduleScalarDualTarget B)
                (moduleHomPrecomp (moduleScalarDualTarget B) f)).f p z) =
            (f.f p).hom.dualMap.dualMap (moduleScalarBidualCoordinates P p z)) ∧
        ∃ ε : Q ≅ moduleScalarDual (moduleScalarDual Q),
          (∀ (p : ℤ) (x : Q.X p),
            moduleScalarBidualCoordinates Q p (ε.hom.f p x) =
              p.negOnePow • Module.Dual.eval B (Q.X p) x) ∧
          δ.hom ≫ moduleHomPrecomp (moduleScalarDualTarget B)
              (moduleHomPrecomp (moduleScalarDualTarget B) f) = f ≫ ε.hom) := by
  sorry

end CochainComplex
