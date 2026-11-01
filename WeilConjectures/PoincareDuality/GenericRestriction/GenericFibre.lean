/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.GenericRestriction.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-!
# Restriction to a generic fibre over the affine line commutes with internal homs

Let `X` be a separated `k`-scheme of finite type with a morphism `b : X ⟶ 𝔸¹_k`, and let
`t : Spec L ⟶ 𝔸¹_k` be a point lying over the generic point of `𝔸¹_k`: a field extension
`k(x) ⟶ L` followed by the generic point `Spec k(x) ⟶ 𝔸¹_k`
(`AlgebraicGeometry.affineLineGenericPoint`); for instance the geometric generic point
`Spec \overline{k(x)} ⟶ 𝔸¹_k`. For the base change `g : X ×_{𝔸¹_k} Spec L ⟶ X` of `t` along `b`,
the derived pullback `Lg^*` commutes with internal homs of bounded constructible
`ℚ̄_ℓ`-complexes (`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isPullback`): this is
blueprint `det-pd-generic-closed-hom` (2) for `B = 𝔸¹_k` (`sk-lem-pd-generic-restriction`).

## Proof

The base change `g` is the composite of the base change `X_L ⟶ X_{k(x)}` of the field extension
`k(x) ⟶ L`, along which internal homs commute with pullback
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_fieldExtension`), and of the base
change `X_{k(x)} ⟶ X` of the generic point, which is weakly étale
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_weaklyEtale`); the comparison maps are
compatible with composition
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_comp`).

## Main statements

- `ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_isPullback`
- `ProEtale.CondensedRing.isIso_nearbyDualityMap_upperStarOfMap_id_of_isIso`: the form on bounded
  constructible complexes, for the duality maps of `CategoryTheory.Verdier`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Restriction to a generic fibre over the affine line commutes with internal homs**
(blueprint `det-pd-generic-closed-hom` (2), for `B = 𝔸¹_k`): let `X` be a separated `k`-scheme
of finite type with a morphism `b : X ⟶ 𝔸¹_k`, `φ : k(x) ⟶ L` a field extension and
`g : X' ⟶ X` the base change of `Spec L ⟶ Spec k(x) ⟶ 𝔸¹_k` along `b`. For bounded
constructible `ℚ̄_ℓ`-complexes `K` and `M` on `X`, the comparison
`Lg^* RHom(K, M) ⟶ RHom(Lg^* K, Lg^* M)` is an isomorphism. -/
theorem isIso_ihomUpperStarComparison_of_isPullback (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (b : X.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k) = X.hom)
    {L : Type u} [Field L] (φ : FractionRing (MvPolynomial (ULift.{u} (Fin 1)) k) →+* L)
    {X' : Scheme.{u}} {g : X' ⟶ X.left} {b' : X' ⟶ Spec (.of L)}
    (sq : IsPullback g b' b (Spec.map (CommRingCat.ofHom φ) ≫ affineLineGenericPoint k))
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) M) :
    IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) g K M) := by
  sorry

section BoundedConstructible

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂] [Fact (ringChar k₁).Prime]
  [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]

/-- The duality map `g^* RHom(A, N) ⟶ RHom(g^* A, g^* N)` of the pullback on bounded constructible
complexes, with the identity as dualizing map, is an isomorphism as soon as the comparison
`ProEtale.CondensedRing.ihomUpperStarComparison` of the ambient derived pullback is one at
`(A, N)` (`ProEtale.CondensedRing.ι_map_ihomComparison_upperStarOfMap_app`). -/
theorem isIso_nearbyDualityMap_upperStarOfMap_id_of_isIso {P : Over (Spec (.of k₁))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    {P' : Over (Spec (.of k₂))} [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom]
    [IsSeparated P'.hom] (g : P'.left ⟶ P.left)
    (N A : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (h : IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) g A.obj N.obj)) :
    IsIso (Verdier.nearbyDualityMap (fun A B ↦ Functor.LaxMonoidal.μ
      (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P') g) A B)
      (𝟙 ((boundedConstructibleUpperStarOfMap ℓ g).obj N)) A) := by
  sorry

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
