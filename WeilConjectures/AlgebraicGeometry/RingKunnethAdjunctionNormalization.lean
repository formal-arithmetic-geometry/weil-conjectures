/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingKunnethNormalizationData
public import WeilConjectures.AlgebraicGeometry.EtaleConstantProjectionMap

/-! # Counit normalization of the point Leray comparison
Source: Stacks Tags 09T5, 0D6E and 0F1E.
(blueprint: lem-sf-ring-kunneth-adjunction-normalization).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
  {k : Type u} [Field k] [IsSepClosed k]

/-- Leray is the conjugate of the specified constant-pullback comparison.
Source: Stacks Tags 09T5 and 0D6E, with the point equivalence of Tag 0F1E.
(blueprint: lem-sf-ring-kunneth-adjunction-normalization).

Proof: On sheaves, the constant-pullback comparison is defined by uniqueness of
left adjoints to evaluation at the base-changed terminal object. Transport evaluation
between that terminal object, the identity etale object, and the chosen terminal object.
Uniqueness of maps between terminal objects identifies their composites. Thus the
conjugate of this constant comparison is lowerStarCompGlobalSectionsIso. Derive the
identity on K-injective resolutions: exact inverse image makes direct image preserve
K-injectives, so its composition with sections computes the composite right derived
functor. The uniqueness of the derived transformation identifies it with canonical
Leray. Finally transport the exact left adjoints along their left-derived/map-derived
comparisons. At the point, derive the specified constant/evaluation equivalence and
transport evaluation to RΓ using rightDerivedGlobalSectionsIsoOfIsSepClosed. Its derived
unit and counit are the ones in ringKunnethPointAdjunction. Conjugacy is invariant under
these transports by naturality and the triangle identities. The resulting left comparison
is exactly ringKunnethConstantComparison, giving the displayed transformation equality.
The argument uses unbounded K-injectives and applies to zero complexes and the empty X. -/
theorem ringKunnethAdjunctionNormalization
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) a).hom =
      conjugateEquiv
        ((ringKunnethPointAdjunction Λ).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a))
        (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} Λ) X)
        (ringKunnethConstantComparison Λ a).hom := by sorry

end AlgebraicGeometry.Etale
