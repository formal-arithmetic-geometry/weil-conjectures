/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus

/-! # Direct condensed point-fibre representative transport

Source: latest blueprint, def-weil-finite-coefficient-point, final paragraph on finite
fields of definition, and def-sfb-derived-extend-comp-iso.proof.md.
(blueprint: lem-weil-point-fibre-representative-transport).
-/

@[expose] public section
set_option autoImplicit false

universe u u₀ u₁ u₂ v₀ v₁ v₂
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedGeometricPoint

namespace WeilConjectures

/-- Extending a representative from G to H does not change its direct point-fibre arrow.
Source: latest blueprint, def-weil-finite-coefficient-point, finite fields of definition;
def-sfb-derived-extend-comp-iso.proof.md, canonical tensor multiplication comparison.
(blueprint: lem-weil-point-fibre-representative-transport).

Proof:
1. Work on a small representative of the pro-etale site of Spec k. Sheaf tensor is
closed and additive, module categories are abelian, and scalar extension is a left
adjoint. Finite-subfield and algebraic-closure flatness therefore make every extension
in each tower E_C <= G <= H <= Omega exact. Constructibility is preserved, so evaluation
restricts to the direct bounded constructible categories and the ordinary bounded
finite-dimensional target of def-weil-finite-coefficient-point.
2. The canonical comparison of an exact total left derived functor with its termwise
derived functor identifies all displayed comparisons with those of
lem-sfb-flat-scalar-tower-coherence. Coefficient inclusions compose to the displayed
inclusions. For C = A, B its four-ring equation reads
kappa_C,H composed with T_H,Omega(alpha_C) = kappa_C,G composed with beta_C,
where beta_C is the G,H,Omega comparison at T_E_C,G(C).
3. Naturality of beta on the arbitrary derived morphism f gives beta_B composed with
T_H,Omega(T_G,H(f)) = T_G,Omega(f) composed with beta_A. This applies to all derived
morphisms and does not choose a chain-map representative.
4. Expand the left side below. Substitute the four-ring equation at both endpoints,
using its inverse form at A. Apply the naturality equation and cancel beta_A and its
inverse. The remaining arrow is exactly the right side. Apply the direct fibre functor.
Faithfulness of the full-subcategory inclusion reads this same equality in D^b_fd(Omega).
Identity comparisons cover repeated fields, and the same cancellation covers zero objects.
-/
theorem pointQbarFibreRepresentative_transport_condensed
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (E_A E_B G H : PadicAlgCl.FiniteIntermediateField ℓ)
    (hA : E_A ≤ G) (hB : E_B ≤ G) (h : G ≤ H)
    (A : BoundedConstructible (padicSubfieldRingObj (Spec (.of D.k)) ℓ E_A))
    (B : BoundedConstructible (padicSubfieldRingObj (Spec (.of D.k)) ℓ E_B))
    (f : (derivedExtendScalarsSubfield (Spec (.of D.k)) ℓ hA).obj A.obj ⟶
      (derivedExtendScalarsSubfield (Spec (.of D.k)) ℓ hB).obj B.obj) :
    (fiber (Profinite.padicAlgClRingObj.{u} ℓ) D.k).map
        ((derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ (hA.trans h)).inv.app A.obj ≫
          (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ H).map
            ((condensedCoefficientCompIso (Spec (.of D.k)) ℓ hA h).inv.app A.obj ≫
              (derivedExtendScalarsSubfield (Spec (.of D.k)) ℓ h).map f ≫
              (condensedCoefficientCompIso (Spec (.of D.k)) ℓ hB h).hom.app B.obj) ≫
          (derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ (hB.trans h)).hom.app B.obj) =
      (fiber (Profinite.padicAlgClRingObj.{u} ℓ) D.k).map
        ((derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ hA).inv.app A.obj ≫
          (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ G).map f ≫
          (derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ hB).hom.app B.obj) := by
  apply congrArg (fiber (Profinite.padicAlgClRingObj.{u} ℓ) D.k).map
  refine representative_transport
    (derivedExtendScalarsSubfield (Spec (.of D.k)) ℓ h)
    (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ H)
    (derivedExtendScalarsToPadicAlgCl (Spec (.of D.k)) ℓ G)
    (derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ h)
    ((condensedCoefficientCompIso (Spec (.of D.k)) ℓ hA h).app A.obj)
    ((condensedCoefficientCompIso (Spec (.of D.k)) ℓ hB h).app B.obj)
    ((derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ hA).app A.obj)
    ((derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ hB).app B.obj)
    ((derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ (hA.trans h)).app A.obj)
    ((derivedExtendScalarsCompIso (Spec (.of D.k)) ℓ (hB.trans h)).app B.obj) ?_ ?_ f
  · have hc := congr_app (congrArg Iso.hom
        ((condensedCoefficientCoherence (Spec (.of D.k)) ℓ).2.1 E_A G H hA h)) A.obj
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp, Iso.app_hom] using hc
  · have hc := congr_app (congrArg Iso.hom
        ((condensedCoefficientCoherence (Spec (.of D.k)) ℓ).2.1 E_B G H hB h)) B.obj
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp, Iso.app_hom] using hc

#print axioms pointQbarFibreRepresentative_transport_condensed

end WeilConjectures
