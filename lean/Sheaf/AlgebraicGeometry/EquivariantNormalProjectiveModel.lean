/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Ring.Equiv
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.GeometricIrreducibilityAffineLocal
import WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality

/-! # Finite normalization of a semilinear projective modification

Source: Stacks Project, varieties.tex, Tag 0BXR; morphisms.tex, Tags 035K, 035L,
035Q and 087S; de Jong, Lemma 5.2, printed p. 613.
(blueprint: lem-sfb-equivariant-normal-projective-model)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Normalization preserves an equivariant projective modification of a normal integral
proper scheme. The actions need not be faithful, and the specified dense open need not be
invariant. `rho` is a left field action; contravariance requires its inverse in the associated
left action on `Spec k`. The equations with `fromSpecFunctionField` say that the field
isomorphisms are induced by the given morphisms, rather than arbitrary field isomorphisms.
Normality is the assertion that each local ring is integrally closed; integrality supplies
that those local rings are domains. The normalization and its map are the canonical ones
from `def-sc-normalization`, with structure morphism `T.fromNormalization ≫ g`.

Source: Stacks Project, Tag 0BXR, lemma-normalization-locally-algebraic; morphisms.tex,
Tags 035K, 035L, 035Q and 087S; de Jong, Lemma 5.2, printed p. 613.
(blueprint: lem-sfb-equivariant-normal-projective-model)

Proof:
1. Apply lem-sfb-finite-normalization-model-functoriality to T and the identity extension
   of k(T), obtaining normal integral finite-type N and finite surjective n with the
   canonical identification k(N) = k(T). Use lem-sc-normalization-exists for the dense-open
   isomorphism. Compose the induced field identification with the specified e.
2. The field spectrum is affine Noetherian. The finite-type H-projective structure map
   of T is projective, so lem-fin-finite-over-projective applied to n gives an embedding
   of N in finite-dimensional projective space over k.
3. For each h apply the semilinear-isomorphism clause of
   lem-sfb-finite-normalization-model-functoriality. Uniqueness and compatibility with
   composition give a group action on N, compatible with n and the original field action.
   Any other lift induces the same action on k(N), so uniqueness gives equality.
4. Put V = p inverse U. It is normal because it is isomorphic to the open U of X.
   By lem-sc-normalization-over-normal-locus, n is an isomorphism over V, and hence pn
   is an isomorphism over the original U.
5. X is separated over k. Apply lem-sfb-finite-constant-projective-graph with the trivial
   extension k/k, R = N and c = pn. Its graph embedding makes pn H-projective, with no
   assertion of an equivariant embedding. By lem-kun-projective-implies-proper it is
   proper, and its closed image contains dense U, proving surjectivity.
6. If X is geometrically integral, a nonempty affine open A of X is geometrically
   irreducible by lem-zl-geometric-irreducibility-affine-local and geometrically reduced
   because reducedness is local. For each nonempty affine open B of T or N, identify its
   fraction field with that of A using lem-sc-integral-function-field-affine-fraction
   and the induced k-compatible field isomorphisms. Apply
   lem-sbc-field-fraction-ring-geometric-integrality to conclude that B is geometrically
   irreducible and geometrically reduced.
7. Apply lem-zl-geometric-irreducibility-affine-local to obtain geometric irreducibility
   of T and N. After every field extension their base-changed affine opens cover and are
   reduced, so both whole schemes are reduced. Irreducible and reduced means integral,
   proving the two geometric-integrality claims.
-/
theorem equivariant_normal_projective_model
    (k : Type u) [Field k] (X T : Scheme.{u}) [IsIntegral X] [IsIntegral T]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : T ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] [IsHProjective g]
    (H : Type v) [Group H] [Finite H] (rho : H →* (k ≃+* k))
    (aX : H →* Aut X) (aT : H →* Aut T)
    (haX : ∀ h : H, (aX h).hom ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom))
    (haT : ∀ h : H, (aT h).hom ≫ g =
      g ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom))
    (p : T ⟶ X) (hp : p ≫ f = g)
    (hequiv : ∀ h : H, (aT h).hom ≫ p = p ≫ (aX h).hom)
    (e : X.functionField ≃+* T.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecFunctionField =
      T.fromSpecFunctionField ≫ p)
    (U : X.Opens) (hU : Dense (U : Set X)) (hpU : IsIso (p ∣_ U)) :
    IsFinite T.fromNormalization ∧ Surjective T.fromNormalization ∧
    (∃ V : T.Opens, Dense (V : Set T) ∧ IsIso (T.fromNormalization ∣_ V)) ∧
    IsIntegral T.normalization ∧
    (∀ x : T.normalization, IsIntegrallyClosed (T.normalization.presheaf.stalk x)) ∧
    LocallyOfFiniteType (T.fromNormalization ≫ g) ∧
    QuasiCompact (T.fromNormalization ≫ g) ∧ IsHProjective (T.fromNormalization ≫ g) ∧
    IsProper (T.fromNormalization ≫ p) ∧ Surjective (T.fromNormalization ≫ p) ∧
    IsHProjective (T.fromNormalization ≫ p) ∧ IsIso ((T.fromNormalization ≫ p) ∣_ U) ∧
    (∃ eN : T.functionField ≃+* T.normalization.functionField,
      Spec.map (CommRingCat.ofHom eN.toRingHom) ≫ T.fromSpecFunctionField =
        T.normalization.fromSpecFunctionField ≫ T.fromNormalization ∧
      Spec.map (CommRingCat.ofHom (e.trans eN).toRingHom) ≫ X.fromSpecFunctionField =
        T.normalization.fromSpecFunctionField ≫ (T.fromNormalization ≫ p)) ∧
    (∃ aN : H →* Aut T.normalization,
      (∀ h : H, (aN h).hom ≫ (T.fromNormalization ≫ g) =
        (T.fromNormalization ≫ g) ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)) ∧
      (∀ h : H, (aN h).hom ≫ T.fromNormalization = T.fromNormalization ≫ (aT h).hom) ∧
      (∀ aN' : H →* Aut T.normalization,
        (∀ h : H, (aN' h).hom ≫ (T.fromNormalization ≫ g) =
          (T.fromNormalization ≫ g) ≫ Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)) →
        (∀ h : H, (aN' h).hom ≫ T.fromNormalization =
          T.fromNormalization ≫ (aT h).hom) → aN' = aN) ∧
      (∀ h : H, (aN h).hom ≫ (T.fromNormalization ≫ p) =
        (T.fromNormalization ≫ p) ≫ (aX h).hom)) ∧
    (GeometricallyIntegral f →
      GeometricallyIntegral g ∧ GeometricallyIntegral (T.fromNormalization ≫ g)) := by
  sorry

end AlgebraicGeometry
