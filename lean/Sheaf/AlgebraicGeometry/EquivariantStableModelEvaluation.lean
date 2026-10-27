/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import WeilConjectures.AlgebraicGeometry.StalkAut
import Sheaf.AlgebraicGeometry.HighGenusHomClosure
public import Sheaf.AlgebraicGeometry.QuasiSplitNodalFibres
public import Sheaf.FieldTheory.FieldTower
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.StablePointedGenericExtension
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Equivariant evaluation on a normal stable model

Source: de Jong, Families of curves and alterations (1997), §§3.9--3.13, p.609,
and the flat generic-field calculation in the node's proof, Steps 6--10
(blueprint: lem-sfb-equivariant-stable-model-evaluation).

The existence statement and the arbitrary-base-change assertions are separate declarations.
The tensor identification is normalized on pure tensors by the actual generic stalk maps.
Its equivariance is expressed on pure tensors, which generate the entire tensor algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Equivariant evaluation extends after a projective birational modification and normal
projective alteration, allowing a semilinear and nonfaithful group action. The fixed-field
clause is expressed elementwise, so it uses the canonical contravariant stalk actions.

Source: de Jong §§3.9--3.13, p.609
(blueprint: lem-sfb-equivariant-stable-model-evaluation).

Proof, Steps 1--5 of the node:
1. The stable predicate supplies flatness, finite presentation, reduced connected nodal
   geometric fibres. Apply lem-sfb-high-genus-hom-closure and its naturality/group-action
   clauses to obtain the projective birational Hom closure R with equivariant evaluation.
2. Normalize R in its own function field L (lem-sfb-finite-normalization-model-functoriality,
   def-fin-normalization-extension). This is finite surjective, integral, normal and finite
   type over k, and every semilinear automorphism lifts uniquely, with composition respected.
3. H-projective composition makes R projective over k. Its projective embedding supplies an
   ample invertible sheaf (lem-weil-pbc-projective-ample-invertible). Finite morphisms are
   projective bundles (lem-trf-finite-projective-bundle), hence H-projective over this base
   (lem-trf-projective-bundle-to-h-projective). Compose to obtain projectivity of S' over S
   and k; projective-proper and finite-type composition give the required geometric properties.
4. On a dense open where R is S, normality of S makes normalization the identity. Intersect
   its finitely many translates if an invariant open is desired. Thus S' to S is finite on
   a dense open. Properness and dominance imply surjectivity. Take J'=J and rho the identity;
   the function-field extension is the identity, finite separable with the stated fixed field.
5. Pull back evaluation by the fibre-product property and pull back all the sections.
   Stable-pointed-generic-extension's base-change clause preserves stability; projective
   base change preserves H-projectivity. The diagonal actions give the two equivariance
   identities, and the original permutation of labels gives the new marking identity.
-/
theorem exists_equivariant_stable_model_evaluation
    (k : Type u) [Field k] (S W Q : Scheme.{u}) (pS : S ⟶ Spec (.of k))
    [IsIntegral S] [IsHProjective pS] [LocallyOfFiniteType pS]
    (hnormal : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
      IsIntegrallyClosed (S.presheaf.stalk x))
    (f : W ⟶ S) (g : Q ⟶ S) [IsHProjective f] [IsHProjective g]
    (n : ℕ) (s : Fin n → (S ⟶ W)) (hs : ∀ i, s i ≫ f = 𝟙 S)
    (hstable : IsStablePointedCurve f s hs)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (hnoRational : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
      (a : ProjectiveLine (Spec (.of Ω)) ⟶ pullback g t),
      a ≫ pullback.snd g t = ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω) →
        ∃ q : Spec (.of Ω) ⟶ pullback g t,
          q ≫ pullback.snd g t = 𝟙 _ ∧
          a = (ProjectiveLine (Spec (.of Ω)) ↘ Spec (.of Ω)) ≫ q)
    (J : Type v) [Group J] [Finite J]
    (σk : J →* Aut (Spec (.of k))) (σS : J →* Aut S)
    (σW : J →* Aut W) (σQ : J →* Aut Q)
    (hk : ∀ a : J, pS ≫ (σk a).hom = (σS a).hom ≫ pS)
    (hf : ∀ a : J, f ≫ (σS a).hom = (σW a).hom ≫ f)
    (hg : ∀ a : J, g ≫ (σS a).hom = (σQ a).hom ≫ g)
    (hmark : ∀ a : J, ∃ π : Equiv.Perm (Fin n),
      ∀ i : Fin n, s i ≫ (σW a).hom = (σS a).hom ≫ s (π i))
    (uη : pullback f S.fromSpecFunctionField ⟶ pullback g S.fromSpecFunctionField)
    (huη : uη ≫ pullback.snd g S.fromSpecFunctionField =
      pullback.snd f S.fromSpecFunctionField)
    (hequiv : ∀ a : J,
      pullback.map f S.fromSpecFunctionField f S.fromSpecFunctionField
          (σW a).hom (Spec.map (Scheme.functionFieldAut (σS a)).hom) (σS a).hom
          (hf a) (Scheme.SpecMap_functionFieldAut_hom_fromSpecFunctionField (σS a)).symm ≫
        uη =
      uη ≫ pullback.map g S.fromSpecFunctionField g S.fromSpecFunctionField
        (σQ a).hom (Spec.map (Scheme.functionFieldAut (σS a)).hom) (σS a).hom
        (hg a) (Scheme.SpecMap_functionFieldAut_hom_fromSpecFunctionField (σS a)).symm) :
    ∃ (R : Scheme.{u}) (_ : IsIntegral R) (r : R ⟶ S)
      (σR : J →* Aut R) (hr : ∀ a : J, r ≫ (σS a).hom = (σR a).hom ≫ r),
      IsHProjective r ∧
      (∃ U : S.Opens, Dense (U : Set S) ∧ IsIso (r ∣_ U)) ∧
      ∃ (e : pullback f r ⟶ pullback g r),
        e ≫ pullback.snd g r = pullback.snd f r ∧
        (∀ a : J,
          pullback.map f r f r (σW a).hom (σR a).hom (σS a).hom (hf a) (hr a) ≫
              e ≫ pullback.fst g r = e ≫ pullback.fst g r ≫ (σQ a).hom) ∧
        (∃ (aη : Spec S.functionField ⟶ R) (haη : aη ≫ r = S.fromSpecFunctionField),
          pullback.map f S.fromSpecFunctionField f r (𝟙 W) aη (𝟙 S)
              ((Category.comp_id f).trans (Category.id_comp f).symm)
              ((Category.comp_id S.fromSpecFunctionField).trans haη.symm) ≫
            e ≫ pullback.fst g r = uη ≫ pullback.fst g S.fromSpecFunctionField) ∧
        ∃ (S' : Scheme.{u}) (_ : IsIntegral S') (r' : S' ⟶ S)
          (J' : Type v) (_ : Group J') (_ : Finite J') (ρ : J' →* J)
          (σS' : J' →* Aut S')
          (hr' : ∀ a : J', r' ≫ (σS (ρ a)).hom = (σS' a).hom ≫ r')
          (b : S' ⟶ R) (hb : b ≫ r = r'),
          Function.Surjective ρ ∧
          (∀ a : J', b ≫ (σR (ρ a)).hom = (σS' a).hom ≫ b) ∧
          (∀ x : S', IsDomain (S'.presheaf.stalk x) ∧
            IsIntegrallyClosed (S'.presheaf.stalk x)) ∧
          IsHProjective (r' ≫ pS) ∧ LocallyOfFiniteType (r' ≫ pS) ∧
          IsHProjective r' ∧ IsProper r' ∧ Surjective r' ∧
          (∃ U : S.Opens, Dense (U : Set S) ∧ IsFinite (r' ∣_ U)) ∧
          ∃ (hη : r' (genericPoint S') = genericPoint S)
            (_ : Algebra S.functionField S'.functionField),
            algebraMap S.functionField S'.functionField = (r'.functionFieldMap hη).hom ∧
            Module.Finite S.functionField S'.functionField ∧
            Algebra.IsSeparable S.functionField S'.functionField ∧
            (∀ x : S'.functionField,
              (∀ a : J', ρ a = 1 → (Scheme.functionFieldAut (σS' a)).hom x = x) ↔
                ∃ y : S.functionField, algebraMap S.functionField S'.functionField y = x) ∧
            IsStablePointedCurve (pullback.snd f r')
              (fun i : Fin n ↦ f.baseChangeSection (s i) (hs i) r')
              (fun i : Fin n ↦ Scheme.Hom.baseChangeSection_snd f (s i) (hs i) r') ∧
            IsHProjective (pullback.snd f r') ∧
            ∃ e' : pullback f r' ⟶ pullback g r',
              e' ≫ pullback.snd g r' = pullback.snd f r' ∧
              e' ≫ pullback.fst g r' =
                pullback.map f r' f r (𝟙 W) b (𝟙 S)
                    ((Category.comp_id f).trans (Category.id_comp f).symm)
                    ((Category.comp_id r').trans hb.symm) ≫ e ≫ pullback.fst g r ∧
              (∀ a : J',
                pullback.map f r' f r' (σW (ρ a)).hom (σS' a).hom (σS (ρ a)).hom
                    (hf (ρ a)) (hr' a) ≫ e' ≫ pullback.fst g r' =
                  e' ≫ pullback.fst g r' ≫ (σQ (ρ a)).hom) ∧
              (∀ a : J', ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n,
                f.baseChangeSection (s i) (hs i) r' ≫
                    pullback.map f r' f r' (σW (ρ a)).hom (σS' a).hom (σS (ρ a)).hom
                      (hf (ρ a)) (hr' a) =
                  (σS' a).hom ≫ f.baseChangeSection (s (π i)) (hs (π i)) r') := by
  sorry

/-- All dominant integral base changes are integral, with smooth geometrically integral
generic fibre. No finite-type or Noetherian condition is imposed on the new base.

Source: the flat generic-field argument, Steps 6--7 and 10, following de Jong §§3.9--3.13
(blueprint: lem-sfb-equivariant-stable-model-evaluation).

Proof: the new generic fibre is the original smooth geometrically integral generic fibre
extended to k(T), hence has the same properties. Flatness survives base change. On each
nonempty affine chart Spec B over a domain A, flatness makes B torsion-free, so B injects
into its localization over Frac A. This localization is nonzero and is a domain because
it is an affine chart in the integral generic fibre. Thus all charts are reduced and every
nonempty open meets the generic fibre. Two such opens meet there, proving irreducibility.
Use lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-flat-morphism-affine-criterion,
lem-trf-flat-module-torsionfree-domain, lem-weil-pbc-fibre-product-affine-spectra and
lem-sc-integral-function-field-affine-fraction. The same argument applies after each
further dominant integral base change; no separability assumption occurs.
-/
theorem stable_model_dominant_baseChange_integral
    {S W : Scheme.{u}} [IsIntegral S] (f : W ⟶ S) [Flat f]
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (T : Scheme.{u}) [IsIntegral T] (t : T ⟶ S) [IsDominant t] :
    IsIntegral (pullback f t) ∧
      Smooth (pullback.snd (pullback.snd f t) T.fromSpecFunctionField) ∧
      GeometricallyIntegral (pullback.snd (pullback.snd f t) T.fromSpecFunctionField) := by
  sorry

/-- The canonical finite generic-field base-change identification, including its semilinear
compatibility. The three algebra structures are constrained to be the actual generic maps;
the ring equivalence is characterized on pure tensors and is not an arbitrary field isomorphism.
Its surjectivity onto a field also states that the tensor algebra itself is a field.
The last clause supplies the diagonal group action and its pure-tensor formula,
including nonfaithful actions and actions on the ground field.

Source: the node's Steps 8--10, affine generic-field calculation after de Jong §§3.9--3.13
(blueprint: lem-sfb-equivariant-stable-model-evaluation).

Proof: choose affine B over A in W, put L=Frac A and C=B tensor_A L. Then k(W)=Frac C.
Every field extension N/L makes C tensor_L N a domain by geometric integrality. Localizing
at C minus zero identifies k(W) tensor_L N with a domain. For finite N/L it is finite
dimensional over k(W), hence a field by lem-weil-pbc-finite-dimensional-domain-is-field.
It is therefore Frac(C tensor_L N), namely k(W_T), by the affine fibre-product formula and
lem-sc-integral-function-field-affine-fraction. The maps send d tensor a to the product
of the two generic pullbacks, giving the displayed normalization. Apply the two compatible
stalk automorphisms to this formula: the result is the product of the transformed factors.
Construct the diagonal scheme action by the pullback property; uniqueness gives its group laws.
Pure tensors generate, so this is full equivariance. Reapply this argument over any
subsequent integral dominant base; finite purely inseparable extensions require no change.
-/
theorem stable_model_finite_baseChange_functionField
    {S W : Scheme.{u}} [IsIntegral S] [IsIntegral W] (f : W ⟶ S) [Flat f]
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    (T : Scheme.{u}) [IsIntegral T] (t : T ⟶ S) [IsDominant t] :
    ∃ (_ : IsIntegral (pullback f t))
      (hfη : f (genericPoint W) = genericPoint S)
      (htη : t (genericPoint T) = genericPoint S)
      (hpη : pullback.fst f t (genericPoint (pullback (C := Scheme.{u}) f t)) = genericPoint W)
      (hqη : pullback.snd f t (genericPoint (pullback (C := Scheme.{u}) f t)) = genericPoint T),
      ∀ (_ : Algebra S.functionField W.functionField)
        (_ : Algebra S.functionField T.functionField),
        algebraMap S.functionField W.functionField = (f.functionFieldMap hfη).hom →
        algebraMap S.functionField T.functionField = (t.functionFieldMap htη).hom →
        Module.Finite S.functionField T.functionField →
        IsField (W.functionField ⊗[S.functionField] T.functionField) ∧
        ∃ e : W.functionField ⊗[S.functionField] T.functionField ≃+*
            (pullback f t).functionField,
          (∀ (d : W.functionField) (a : T.functionField),
            e (d ⊗ₜ[S.functionField] a) =
              ((pullback.fst f t).functionFieldMap hpη).hom d *
                ((pullback.snd f t).functionFieldMap hqη).hom a) ∧
          (∀ (G : Type v) [Group G] [Finite G]
            (σW : G →* Aut W) (σT : G →* Aut T) (σS : G →* Aut S),
            (∀ a : G, f ≫ (σS a).hom = (σW a).hom ≫ f) →
            (∀ a : G, t ≫ (σS a).hom = (σT a).hom ≫ t) →
            ∃ σX : G →* Aut (pullback f t),
              (∀ a : G, (σX a).hom ≫ pullback.fst f t =
                pullback.fst f t ≫ (σW a).hom) ∧
              (∀ a : G, (σX a).hom ≫ pullback.snd f t =
                pullback.snd f t ≫ (σT a).hom) ∧
              ∀ (a : G) (d : W.functionField) (b : T.functionField),
                (Scheme.functionFieldAut (σX a)).hom (e (d ⊗ₜ[S.functionField] b)) =
                  e ((Scheme.functionFieldAut (σW a)).hom d ⊗ₜ[S.functionField]
                    (Scheme.functionFieldAut (σT a)).hom b)) := by
  sorry

end AlgebraicGeometry
