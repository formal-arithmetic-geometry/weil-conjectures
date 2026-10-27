/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.ReducedNormalization
import Sheaf.AlgebraicGeometry.ComponentDominantNormalizationLift
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper

/-! # Normalization of an equivariant projective generic model

Source: Stacks Project, Varieties, Tags 0BXR and 0GK4; Morphisms, Tags 035Q(4) and 0BAI
(blueprint: lem-sfb-equivariant-projective-model-normalization).

All generic identifications below are expressed by their maps from field spectra, so they
retain the specified identification of the generic fibre and the action on its field.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical normalization of an integral projective model preserves its specified
finite generic fibre and lifts a finite semilinear action uniquely.

Source: Stacks Project, Varieties, Tags 0BXR and 0GK4; Morphisms, Tags 035Q(4) and 0BAI
(blueprint: lem-sfb-equivariant-projective-model-normalization).

Proof plan:
1. Apply lem-sfb-finite-normalization-model-functoriality to C and the identity extension
   of k(C). The definition def-fin-normalization-extension identifies this with C.normalization.
   It is normal integral, finite type, finite and surjective over C, with the same function
   field. Apply lem-fin-finite-over-projective over the affine Noetherian spectrum of k
   to obtain its global projective embedding.
2. For integral C, def-weil-pbc-reduced-normalization is its single-component normalization.
   Apply lem-sfb-componentwise-normalization-generic-properties: the normalization has
   trivial fibre over Spec k(C). The given generic-fibre identification and associativity
   of fibre products identify its fibre over Spec k(S) with Spec M. The projection equations
   below express precisely the identifications induced by the normalization morphism.
3. The isomorphism clause of lem-sfb-finite-normalization-model-functoriality lifts each
   group automorphism compatibly with identities, composition, scalars and the function
   field. Uniqueness among all morphism lifts follows from
   lem-sfb-component-dominant-normalization-lift applied to the dominant composite g nu.
   On fields use inverse pullback for the left action, both on C and on its normalization.
4. By lem-kun-projective-implies-proper, S is separated over k. Apply
   lem-sfb-finite-constant-projective-graph with the degree-one extension k/k to the
   composite p nu. Its closed graph gives a global projective embedding over S and
   properness. Equivariance follows by composing the two equivariance squares.
5. By lem-weil-pbc-finite-type-over-noetherian, S is Noetherian. The proper image contains
   its generic point by the nonempty generic fibre, and is therefore all of S. Apply
   lem-per-generic-fibre-finiteness-criterion to the finite extension M/k(S) to get a
   dense open over which the composite is finite. Properness, surjectivity and this dense
   open are exactly the alteration convention in the node.
-/
theorem equivariant_projective_model_normalization
    (k : Type u) [Field k] (S C : Scheme.{u}) [IsIntegral S] [IsIntegral C]
    (s : S ⟶ Spec (.of k)) (c : C ⟶ Spec (.of k))
    [IsHProjective s] [IsHProjective c]
    [LocallyOfFiniteType s] [QuasiCompact s] [LocallyOfFiniteType c] [QuasiCompact c]
    (J : Type v) [Group J] [Finite J] (rho : J →* (k ≃+* k))
    (aS : J →* Aut S) (aC : J →* Aut C)
    (hs : ∀ g : J, (aS g).hom ≫ s =
      s ≫ Spec.map (CommRingCat.ofHom (rho g⁻¹).toRingHom))
    (hc : ∀ g : J, (aC g).hom ≫ c =
      c ≫ Spec.map (CommRingCat.ofHom (rho g⁻¹).toRingHom))
    (p : C ⟶ S) (hp : p ≫ s = c)
    (heq : ∀ g : J, (aC g).hom ≫ p = p ≫ (aS g).hom)
    (M : Type u) [Field M] [Algebra S.functionField M]
    [FiniteDimensional S.functionField M]
    (eC : C.functionField ≅ CommRingCat.of M)
    (e : pullback p S.fromSpecFunctionField ≅ Spec (.of M))
    (heC : e.inv ≫ pullback.fst p S.fromSpecFunctionField =
      Spec.map eC.hom ≫ C.fromSpecFunctionField)
    (heS : e.inv ≫ pullback.snd p S.fromSpecFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField M))) :
    IsFinite C.fromNormalization ∧ Surjective C.fromNormalization ∧
    IsIntegral C.normalization ∧
    (∀ w : C.normalization, IsDomain (C.normalization.presheaf.stalk w) ∧
      IsIntegrallyClosed (C.normalization.presheaf.stalk w)) ∧
    IsHProjective (C.fromNormalization ≫ c) ∧
    LocallyOfFiniteType (C.fromNormalization ≫ c) ∧ QuasiCompact (C.fromNormalization ≫ c) ∧
    ∃ (eW : C.normalization.functionField ≅ CommRingCat.of M)
      (eF : pullback (C.fromNormalization ≫ p) S.fromSpecFunctionField ≅ Spec (.of M))
      (aW : J →* Aut C.normalization) (rhoM : J →* (M ≃+* M)),
      (Spec.map eW.hom ≫ C.normalization.fromSpecFunctionField) ≫ C.fromNormalization =
        Spec.map eC.hom ≫ C.fromSpecFunctionField ∧
      eF.inv ≫ pullback.fst (C.fromNormalization ≫ p) S.fromSpecFunctionField =
        Spec.map eW.hom ≫ C.normalization.fromSpecFunctionField ∧
      eF.inv ≫ pullback.snd (C.fromNormalization ≫ p) S.fromSpecFunctionField =
        e.inv ≫ pullback.snd p S.fromSpecFunctionField ∧
      (∀ g : J, (aW g).hom ≫ C.fromNormalization = C.fromNormalization ≫ (aC g).hom) ∧
      (∀ (g : J) (l : C.normalization ⟶ C.normalization),
        l ≫ C.fromNormalization = C.fromNormalization ≫ (aC g).hom → l = (aW g).hom) ∧
      (∀ g : J, (aW g).hom ≫ (C.fromNormalization ≫ c) =
        (C.fromNormalization ≫ c) ≫ Spec.map (CommRingCat.ofHom (rho g⁻¹).toRingHom)) ∧
      (∀ g : J, (Spec.map eC.hom ≫ C.fromSpecFunctionField) ≫ (aC g).hom =
        Spec.map (CommRingCat.ofHom (rhoM g⁻¹).toRingHom) ≫
          (Spec.map eC.hom ≫ C.fromSpecFunctionField)) ∧
      (∀ g : J, (Spec.map eW.hom ≫ C.normalization.fromSpecFunctionField) ≫ (aW g).hom =
        Spec.map (CommRingCat.ofHom (rhoM g⁻¹).toRingHom) ≫
          (Spec.map eW.hom ≫ C.normalization.fromSpecFunctionField)) ∧
      (∀ g : J, (aW g).hom ≫ (C.fromNormalization ≫ p) =
        (C.fromNormalization ≫ p) ≫ (aS g).hom) ∧
      IsHProjective (C.fromNormalization ≫ p) ∧ IsProper (C.fromNormalization ≫ p) ∧
      Surjective (C.fromNormalization ≫ p) ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite ((C.fromNormalization ≫ p) ∣_ U)) := by
  sorry

end AlgebraicGeometry
