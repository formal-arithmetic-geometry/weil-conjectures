/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.Algebra.Homology.OpenExtensionRestrictionIso
import Sheaf.Algebra.Homology.OpenExtensionCounitStalk
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.AlgebraicGeometry.DerivedTensorStalkVanishing

/-! # Tensor stability of derived open test objects
Source: Stacks Project, Tags 00A7, 08BT and 06YB.
(blueprint: lem-sc-derived-open-tensor-hom-bijective).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048

/-- Tensoring an extension object preserves the restriction Hom bijection.
Source: Stacks Project, Tags 00A7, 08BT, 06YB and 06YH.
(blueprint: lem-sc-derived-open-tensor-hom-bijective).

Proof: Write J for exact extension by zero, transported through Modules.overEquiv,
and R for derived restriction. The unit of J ⊣ R is invertible. For any C, the
restricted counit R(J(R(C))) → R(C) is invertible by the triangle identity. Thus
precomposition with the counit J(R(B)) → B is a bijection on Hom(-,E): identify
Hom(J(R(B)),E) with Hom(R(B),R(E)) by adjunction and cancellation of the unit,
and use the assumed bijectivity of R.map on Hom(B,E). Yoneda then makes this
counit invertible. In particular B is an extension object, whose cohomology
stalks vanish outside U, by exactness and the exterior stalk computation.
Choose a complex P representing B and a K-flat resolution Q representing L.
The stalk vanishing theorem shows that Tot(P tensor Q) has zero cohomology
stalks outside U. The K-flat tensor comparison, using symmetry to place Q
first, identifies its derived image with B tensor L.
For any C with this vanishing, represent C by a complex and take the termwise
extension/restriction counit. Inside U its stalk maps are invertible. Outside U
its source stalk complex is zero and its target stalk complex is acyclic.
Hence the counit is a stalkwise quasi-isomorphism, and thus a quasi-isomorphism
of sheaf complexes. Its image J(R(C)) → C in the derived category is invertible.
Apply this to C = B tensor L. The adjunction and its invertible unit identify
restriction on Hom(J(R(C)),E) with a bijection. Precompose with the invertible
counit and cancel its invertible restriction to obtain precisely R.map on
Hom(C,E). No bound, flatness of L itself, or finiteness is assumed. -/
theorem derivedOpen_tensorHom_bijective
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (B : schemeDerivedCategory X) :
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    (∀ E : schemeDerivedCategory X,
      Function.Bijective (fun f : B ⟶ E ↦ R.map f)) →
    ∀ L E : schemeDerivedCategory X,
      Function.Bijective (fun f : B ⊗ L ⟶ E ↦ R.map f) := by sorry

end AlgebraicGeometry.Scheme
