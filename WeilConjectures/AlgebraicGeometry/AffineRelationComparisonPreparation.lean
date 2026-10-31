/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import WeilConjectures.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover

/-!
# Preparation of the comparison for an affine equivalence relation

Source: Stacks Project, Groupoids, Tags 03BM (first two proof paragraphs), 03BK (1),(3),
03BJ and 03BL; Morphisms, Tag 02KB
(blueprint: lem-a1-affine-relation-comparison-preparation).

Scalar extension is written `D ⊗[C] A` and `D ⊗[C] B`. The canonical tensor symmetry
identifies these with the node's `A ⊗[C] D` and `B ⊗[C] D`; this makes the standard
left-factor `D`-algebra structure available without any file-local instances.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry
namespace AffineRelationComparison

/-- The canonical invariant-ring action on the arrow ring, via the source map.
Source: Stacks Project, Tag 03BK (blueprint: lem-a1-affine-relation-comparison-preparation).
The target map gives the same action because elements of `eqLocus` have equal images. -/
instance invariantArrowAlgebra {A B : CommRingCat.{u}} (σ τ : A →+* B) :
    Algebra (σ.eqLocus τ) B :=
  (σ.comp (σ.eqLocus τ).subtype).toAlgebra

/-- The source map as an algebra map over the invariant ring.
Source: Stacks Project, Tag 03BK (blueprint: lem-a1-affine-relation-comparison-preparation). -/
def source {A B : CommRingCat.{u}} (σ τ : A →+* B) : A →ₐ[σ.eqLocus τ] B :=
  { σ with commutes' := fun _ ↦ rfl }

/-- The target map as an algebra map over the invariant ring.
Source: Stacks Project, Tag 03BK (blueprint: lem-a1-affine-relation-comparison-preparation). -/
def target {A B : CommRingCat.{u}} (σ τ : A →+* B) : A →ₐ[σ.eqLocus τ] B :=
  { τ with commutes' := fun c ↦ c.property.symm }

/-- The canonical tensor comparison, sending `a ⊗ a'` to `σ(a)τ(a')`.
Source: Stacks Project, Tag 03BM (blueprint: lem-a1-affine-relation-comparison-preparation). -/
def comparison {A B : CommRingCat.{u}} (σ τ : A →+* B) :
    A ⊗[σ.eqLocus τ] A →+* B :=
  (Algebra.TensorProduct.productMap (source σ τ) (target σ τ)).toRingHom

/-- Extension of an invariant-linear arrow map to the new scalar ring, using the
canonical tensor-product map. The `D ⊗ A` convention is the symmetry of `A ⊗ D`.
Source: Stacks Project, Tag 03BK (blueprint: lem-a1-affine-relation-comparison-preparation). -/
def extend {A B : CommRingCat.{u}} (σ τ : A →+* B)
    (D : Type u) [CommRing D] [Algebra (σ.eqLocus τ) D]
    (f : A →ₐ[σ.eqLocus τ] B) :
    D ⊗[σ.eqLocus τ] A →ₐ[D] D ⊗[σ.eqLocus τ] B :=
  Algebra.TensorProduct.map (AlgHom.id D D) f

/-- The source or target after scalar extension; `true` selects the source.
Source: Stacks Project, Tag 03BK (blueprint: lem-a1-affine-relation-comparison-preparation). -/
def extendedMap {A B : CommRingCat.{u}} (σ τ : A →+* B)
    (D : Type u) [CommRing D] [Algebra (σ.eqLocus τ) D] (p : Bool) :
    D ⊗[σ.eqLocus τ] A →ₐ[D] D ⊗[σ.eqLocus τ] B :=
  extend σ τ D (if p then source σ τ else target σ τ)

/-- The original object or arrow ring included into its scalar extension.
Source: Stacks Project, Tag 03BK (blueprint: lem-a1-affine-relation-comparison-preparation). -/
noncomputable def extensionProjection {C : Type u} [CommRing C] (T D : Type u)
    [CommRing T] [CommRing D] [Algebra C T] [Algebra C D] :
    Spec (CommRingCat.of (D ⊗[C] T)) ⟶ Spec (CommRingCat.of T) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : T →ₐ[C] D ⊗[C] T))

/-- The coordinate comparison after scalar extension, specified by the tensor universal property.
Source: Stacks Project, Tag 03BM (blueprint: lem-a1-affine-relation-comparison-preparation). -/
def extendedComparison {A B : CommRingCat.{u}} (σ τ : A →+* B)
    (D : Type u) [CommRing D] [Algebra (σ.eqLocus τ) D] :
    (D ⊗[σ.eqLocus τ] A) ⊗[D] (D ⊗[σ.eqLocus τ] A) →+*
      D ⊗[σ.eqLocus τ] B :=
  (Algebra.TensorProduct.productMap (extendedMap σ τ D true)
    (extendedMap σ τ D false)).toRingHom

end AffineRelationComparison

open AffineRelationComparison

/-- All preparation data for the affine invariant comparison of a finite locally free relation.
Source: Stacks Project, Tags 03BM, 03BK (1),(3), 03BJ, 03BL and 02KB
(blueprint: lem-a1-affine-relation-comparison-preparation).

Proof plan, following the eight steps of the node:
1. On points over S, reflexivity, symmetry and transitivity give the unique identity,
   inverse and composite arrows. Their uniqueness makes these assignments natural. Yoneda
   represents them by S-morphisms. The laws hold because arrows with the same endpoints
   coincide; decomposing absolute test points by their S-structure proves the absolute laws.
2. Source and target agree on C, so q equalizes them. The affine pullback formula and the
   tensor universal property identify the comparison with a tensor a' mapped to σ(a)τ(a').
   The endpoint laws also make identity, inverse and composition morphisms over Spec C.
3. The comparison is mono by endpoint uniqueness. Generators of B over A via σ still
   generate over A tensor_C A. It is therefore finite, hence a closed immersion by the
   finite-monomorphism criterion. Its affine coordinate homomorphism is surjective.
4. Apply lem-a1-affine-groupoid-integral-invariants and
   lem-a1-affine-groupoid-orbit-fibres to the constructed absolute groupoid. These give
   monic annihilators, surjectivity of q and precisely the asserted ordinary orbit fibres.
5. Treat σ and τ separately. Finiteness, flatness and finite algebra presentation imply
   finite module presentation; finitely presented flat modules are projective. Apply
   Module.exists_standardFreeCover_of_finite_projective to obtain the finite free covers.
6. Base change the groupoid over Spec C. The canonical tensor maps give its projections;
   the operations and their equations pull back. Finite, flat and locally finitely
   presented morphisms remain so after base change. This is the groupoid clause of
   lem-a1-affine-groupoid-basechange-polynomial-norm (Stacks 03BK (1)).
7. Tensor the exact sequence 0 -> C -> A -> B, whose last arrow is σ - τ, with flat D.
   Flat tensor exactness gives injectivity of D -> A_D and identifies its image with
   the equalizer of σ_D and τ_D, compatibly with multiplication and units.
8. The pure-tensor formula identifies the new comparison with the scalar extension of φ.
   The elements f_i mapped into A_D still generate the unit ideal. Localization commutes
   with scalar extension, and tensoring each chart basis supplies a finite free basis
   on that same pulled-back chart. Repeat for both source and target.
-/
theorem affineRelation_comparison_preparation
    {S : Scheme.{u}} {A B : CommRingCat.{u}} (a : Spec A ⟶ S) (b : Spec B ⟶ S)
    (σ τ : A →+* B) (hs : (Spec.map (CommRingCat.ofHom σ)) ≫ a = b) (ht : (Spec.map
      (CommRingCat.ofHom τ)) ≫ a = b)
    [((Spec.map (CommRingCat.ofHom σ))).IsFiniteLocallyFree] [((Spec.map (CommRingCat.ofHom
      τ))).IsFiniteLocallyFree]
    (hrel : ∀ H : Over S,
      Function.Injective (fun r : H ⟶ Over.mk b ↦
        (r.left ≫ (Spec.map (CommRingCat.ofHom σ)), r.left ≫ (Spec.map (CommRingCat.ofHom τ)))) ∧
      Equivalence (fun x y : H ⟶ Over.mk a ↦ ∃ r : H ⟶ Over.mk b,
        r.left ≫ (Spec.map (CommRingCat.ofHom σ)) = x.left ∧ r.left ≫ (Spec.map (CommRingCat.ofHom
          τ)) = y.left)) :
    ∃ (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
      (c : pullback (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) ⟶ Spec B),
      IsGroupoidScheme (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) e i c ∧
      e ≫ b = a ∧ i ≫ b = b ∧ c ≫ b = pullback.fst (Spec.map (CommRingCat.ofHom σ)) (Spec.map
        (CommRingCat.ofHom τ)) ≫ b ∧
      (∀ (e' : Spec A ⟶ Spec B) (i' : Spec B ⟶ Spec B)
        (c' : pullback (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) ⟶ Spec B),
        IsGroupoidScheme (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) e' i' c'
          → e' = e ∧ i' = i ∧ c' = c) ∧
      ∃ hq : (Spec.map (CommRingCat.ofHom σ)) ≫ (Spec.map (CommRingCat.ofHom (σ.eqLocus τ).subtype))
        = (Spec.map (CommRingCat.ofHom τ)) ≫ (Spec.map (CommRingCat.ofHom (σ.eqLocus τ).subtype)),
        (pullback.lift (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) hq ≫
          (pullbackSpecIso (σ.eqLocus τ) A A).hom =
            Spec.map (CommRingCat.ofHom (comparison σ τ))) ∧
        IsFinite (pullback.lift (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ))
          hq) ∧
        Mono (pullback.lift (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) hq) ∧
        IsClosedImmersion (pullback.lift (Spec.map (CommRingCat.ofHom σ)) (Spec.map
          (CommRingCat.ofHom τ)) hq) ∧
        Function.Surjective (comparison σ τ) ∧
        (∀ x y : A, comparison σ τ (x ⊗ₜ y) = σ x * τ y) ∧
        (∀ x : A, ∃ P : Polynomial (σ.eqLocus τ),
          P.Monic ∧ P.eval₂ (σ.eqLocus τ).subtype x = 0) ∧
        Surjective (Spec.map (CommRingCat.ofHom (σ.eqLocus τ).subtype)) ∧
        (∀ x y : Spec A, (Spec.map (CommRingCat.ofHom (σ.eqLocus τ).subtype)) x = (Spec.map
          (CommRingCat.ofHom (σ.eqLocus τ).subtype)) y ↔
          ∃ r : Spec B, (Spec.map (CommRingCat.ofHom σ)) r = x ∧ (Spec.map (CommRingCat.ofHom τ)) r
            = y) ∧
        ∃ (n : Bool → ℕ) (f : (p : Bool) → Fin (n p) → A),
          (∀ p : Bool, Ideal.span (Set.range (f p)) = ⊤ ∧
            ∀ j : Fin (n p),
              Module.Finite (Localization.Away (f p j))
                (LocalizedModule.Away (f p j)
                  ((ModuleCat.restrictScalars (if p then σ else τ)).obj (ModuleCat.of B B))) ∧
              Module.Free (Localization.Away (f p j))
                (LocalizedModule.Away (f p j)
                  ((ModuleCat.restrictScalars (if p then σ else τ)).obj (ModuleCat.of B B)))) ∧
          ∀ (D : Type u) [CommRing D] [Algebra (σ.eqLocus τ) D] [Module.Flat (σ.eqLocus τ) D],
            ((Spec.map (CommRingCat.ofHom (extendedMap σ τ D true).toRingHom))).IsFiniteLocallyFree
              ∧ ((Spec.map (CommRingCat.ofHom (extendedMap σ τ D
              false).toRingHom))).IsFiniteLocallyFree ∧
            (∃ (eD : Spec (CommRingCat.of (D ⊗[σ.eqLocus τ] A)) ⟶ Spec (CommRingCat.of (D
              ⊗[σ.eqLocus τ] B)))
              (iD : Spec (CommRingCat.of (D ⊗[σ.eqLocus τ] B)) ⟶ Spec (CommRingCat.of (D ⊗[σ.eqLocus
                τ] B)))
              (cD : pullback (Spec.map (CommRingCat.ofHom (extendedMap σ τ D true).toRingHom))
                (Spec.map (CommRingCat.ofHom (extendedMap σ τ D false).toRingHom)) ⟶ Spec
                (CommRingCat.of (D ⊗[σ.eqLocus τ] B))),
              IsGroupoidScheme (Spec.map (CommRingCat.ofHom (extendedMap σ τ D true).toRingHom))
                (Spec.map (CommRingCat.ofHom (extendedMap σ τ D false).toRingHom)) eD iD cD ∧
              eD ≫ extensionProjection (C := σ.eqLocus τ) B D =
                extensionProjection (C := σ.eqLocus τ) A D ≫ e ∧
              iD ≫ extensionProjection (C := σ.eqLocus τ) B D =
                extensionProjection (C := σ.eqLocus τ) B D ≫ i ∧
              ∀ (H : Scheme.{u}) (x y : H ⟶ Spec (CommRingCat.of (D ⊗[σ.eqLocus τ] B)))
                (hxy : x ≫ (Spec.map (CommRingCat.ofHom (extendedMap σ τ D true).toRingHom)) = y ≫
                  (Spec.map (CommRingCat.ofHom (extendedMap σ τ D false).toRingHom)))
                (hxy' : (x ≫ extensionProjection (C := σ.eqLocus τ) B D) ≫ (Spec.map
                  (CommRingCat.ofHom σ)) =
                  (y ≫ extensionProjection (C := σ.eqLocus τ) B D) ≫ (Spec.map (CommRingCat.ofHom
                    τ))),
                (pullback.lift x y hxy ≫ cD) ≫ extensionProjection (C := σ.eqLocus τ) B D =
                  pullback.lift (x ≫ extensionProjection (C := σ.eqLocus τ) B D)
                    (y ≫ extensionProjection (C := σ.eqLocus τ) B D) hxy' ≫ c) ∧
            Function.Injective (algebraMap D (D ⊗[σ.eqLocus τ] A)) ∧
            (∀ z : D ⊗[σ.eqLocus τ] A,
              extendedMap σ τ D true z = extendedMap σ τ D false z ↔
                ∃ d : D, algebraMap D (D ⊗[σ.eqLocus τ] A) d = z) ∧
            (∃ hD : (Spec.map (CommRingCat.ofHom (extendedMap σ τ D true).toRingHom)) ≫ (Spec.map
              (CommRingCat.ofHom (algebraMap D (D ⊗[σ.eqLocus τ] A)))) = (Spec.map
              (CommRingCat.ofHom (extendedMap σ τ D false).toRingHom)) ≫ (Spec.map
              (CommRingCat.ofHom (algebraMap D (D ⊗[σ.eqLocus τ] A)))),
              pullback.lift (Spec.map (CommRingCat.ofHom (extendedMap σ τ D true).toRingHom))
                (Spec.map (CommRingCat.ofHom (extendedMap σ τ D false).toRingHom)) hD ≫
                (pullbackSpecIso D (D ⊗[σ.eqLocus τ] A) (D ⊗[σ.eqLocus τ] A)).hom =
                Spec.map (CommRingCat.ofHom (extendedComparison σ τ D))) ∧
            (∀ (x y : A) (d d' : D),
              extendedComparison σ τ D ((d ⊗ₜ x) ⊗ₜ (d' ⊗ₜ y)) =
                (d * d') ⊗ₜ comparison σ τ (x ⊗ₜ y)) ∧
            ∀ p : Bool,
              Ideal.span (Set.range (fun j : Fin (n p) ↦
                (Algebra.TensorProduct.includeRight : A →ₐ[σ.eqLocus τ] D ⊗[σ.eqLocus τ] A) (f p
                  j))) = ⊤ ∧
              ∀ j : Fin (n p),
                Module.Finite (Localization.Away
                  ((Algebra.TensorProduct.includeRight : A →ₐ[σ.eqLocus τ] D ⊗[σ.eqLocus τ] A) (f p
                    j)))
                  (LocalizedModule.Away
                    ((Algebra.TensorProduct.includeRight : A →ₐ[σ.eqLocus τ] D ⊗[σ.eqLocus τ] A) (f
                      p j))
                    ((ModuleCat.restrictScalars (extendedMap σ τ D p).toRingHom).obj
                      (ModuleCat.of (D ⊗[σ.eqLocus τ] B) (D ⊗[σ.eqLocus τ] B)))) ∧
                Module.Free (Localization.Away
                  ((Algebra.TensorProduct.includeRight : A →ₐ[σ.eqLocus τ] D ⊗[σ.eqLocus τ] A) (f p
                    j)))
                  (LocalizedModule.Away
                    ((Algebra.TensorProduct.includeRight : A →ₐ[σ.eqLocus τ] D ⊗[σ.eqLocus τ] A) (f
                      p j))
                    ((ModuleCat.restrictScalars (extendedMap σ τ D p).toRingHom).obj
                      (ModuleCat.of (D ⊗[σ.eqLocus τ] B) (D ⊗[σ.eqLocus τ] B)))) := by
  sorry

end AlgebraicGeometry
