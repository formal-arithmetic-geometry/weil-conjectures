/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.HenselianFiniteEtaleFieldLift
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.AlgebraicGeometry.Thickening
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Effectivity of complete local points of algebraic spaces

Source: Stacks Project, Formal Spaces, Tag 0AQH
(blueprint: lem-sfb-space-complete-local-map-effectivity).

The restriction map is constructed from quotient homomorphisms and the underlying
fppf sheaf. Its codomain consists of consecutive-compatible families, indexed by
positive powers through `n + 1`. Sheaf sections identify with S-morphisms by Yoneda.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- The affine `S`-scheme obtained from the `(n+1)`st maximal-ideal quotient.
Source: Stacks Project, Formal Spaces, Tag 0AQH
(blueprint: lem-sfb-space-complete-local-map-effectivity). -/
noncomputable def completeLocalQuotientOver {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] (f : Spec (.of A) ⟶ S) (n : ℕ) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))) ≫ f)

/-- The canonical map from a maximal-ideal quotient to the original affine scheme.
Source: Stacks Project, Formal Spaces, Tag 0AQH
(blueprint: lem-sfb-space-complete-local-map-effectivity). -/
noncomputable def completeLocalQuotientMap {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] (f : Spec (.of A) ⟶ S) (n : ℕ) :
    completeLocalQuotientOver f n ⟶ Over.mk f := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1))))) ?_
  rfl

/-- The transition map from the `(n+1)`st to the `(n+2)`nd quotient spectrum.
Source: Stacks Project, Formal Spaces, Tag 0AQH
(blueprint: lem-sfb-space-complete-local-map-effectivity). -/
noncomputable def completeLocalQuotientTransition {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] (f : Spec (.of A) ⟶ S) (n : ℕ) :
    completeLocalQuotientOver f n ⟶ completeLocalQuotientOver f (n + 1) := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (S := IsLocalRing.maximalIdeal A ^ (n + 2))
      (T := IsLocalRing.maximalIdeal A ^ (n + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))) ?_
  change Spec.map _ ≫ Spec.map _ ≫ f = Spec.map _ ≫ f
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Restriction of an algebraic-space-valued point to a maximal-ideal quotient.
Source: Stacks Project, Formal Spaces, Tag 0AQH
(blueprint: lem-sfb-space-complete-local-map-effectivity). -/
noncomputable def completeLocalQuotientRestriction {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] (f : Spec (.of A) ⟶ S) (B : AlgebraicSpace S)
    (b : B.obj.obj.obj (op (Over.mk f))) (n : ℕ) :
    B.obj.obj.obj (op (completeLocalQuotientOver f n)) :=
  B.obj.obj.map (completeLocalQuotientMap f n).op b

/-- Compatible algebraic-space-valued points of all positive maximal-ideal quotients.
Source: Stacks Project, Formal Spaces, Tag 0AQH, first equation in its proof
(blueprint: lem-sfb-space-complete-local-map-effectivity). -/
def CompleteLocalPointFamily {S : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] (f : Spec (.of A) ⟶ S) (B : AlgebraicSpace S) :=
  { b : (n : ℕ) → B.obj.obj.obj (op (completeLocalQuotientOver f n)) //
    ∀ n : ℕ, B.obj.obj.map (completeLocalQuotientTransition f n).op (b (n + 1)) = b n }

/-- Restriction to the full compatible family of positive maximal-ideal quotients.
Source: Stacks Project, Formal Spaces, Tag 0AQH, first equation in its proof
(blueprint: lem-sfb-space-complete-local-map-effectivity). -/
noncomputable def completeLocalPointRestriction {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsLocalRing A] (f : Spec (.of A) ⟶ S) (B : AlgebraicSpace S) :
    B.obj.obj.obj (op (Over.mk f)) → CompleteLocalPointFamily f B := fun b ↦
  ⟨completeLocalQuotientRestriction f B b, fun n ↦ by
    change B.obj.obj.map (completeLocalQuotientTransition f n).op
      (B.obj.obj.map (completeLocalQuotientMap f (n + 1)).op b) =
        B.obj.obj.map (completeLocalQuotientMap f n).op b
    rw [← Functor.map_comp_apply]
    apply congrArg (fun g ↦ B.obj.obj.map g b)
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl ⟩

/-- Complete local points of an algebraic space are effective, without separation or
finite-type hypotheses on the space.
Source: Stacks Project, Formal Spaces, Tag 0AQH
(blueprint: lem-sfb-space-complete-local-map-effectivity).

Proof:
1. For scheme targets, classify local-spectrum maps by their closed-point image and
   local stalk map (lem-weil-pbc-morphism-from-spec-local-ring). Compatible reductions
   have one image and one stalk map by adic completeness; locality is detected modulo
   the maximal ideal. This gives existence and uniqueness, naturally and over S.
2. For an algebraic space, represent its diagonal and apply this scheme calculation
   to the equalizer of two maps. Their compatible equal reductions produce a section
   of the equalizer, proving injectivity (def-trf-algebraic-space, lem-pc-yoneda).
3. Pull an étale surjective scheme atlas back to the residue-field point. An étale
   fibre has a finite separable point (lem-trf-space-fibre-products-etale-covers and
   lem-weil-pbc-etale-fibre-discrete-separable-points).
4. Completeness implies henselianity (lem-weil-pbc-complete-pair-henselian). Lift
   this residue extension to a finite étale algebra A′
   (lem-weil-pbc-henselian-finite-etale-field-lift). The finite complete-local product
   decomposition and the radical property show A′ is complete Noetherian local with
   maximal ideal 𝔪A′ (lem-weil-pbc-finite-over-complete-local-product and
   lem-weil-pbc-finite-algebra-local-radical).
5. Successive quotient inclusions are first-order thickenings. Étale infinitesimal
   lifting produces unique compatible atlas points over A′/𝔪ⁿA′
   (def-sbc-first-order-thickening, lem-sfb-etale-space-infinitesimal-lifting).
6. The scheme calculation algebraizes these points to Spec A′ → U, hence to B.
7. Decompose A′ ⊗[A] A′ into complete local factors. Its finite étale special fibre
   is a product of fields, so each factor has maximal ideal 𝔪Cᵢ. The two pullbacks
   agree modulo every power, hence agree by step 2 (finite-over-complete-local-product,
   finite-algebra-local-radical, etale-algebra-over-field-product,
   etale-base-change-finite-limits, etale-composition-cancellation,
   finite-affine-coproduct-spectrum, with the lem-weil-pbc prefixes).
8. The finite étale local extension is faithfully flat
   (lem-weil-pbc-flat-local-hom-faithfully-flat), hence an fppf cover. The fppf sheaf
   condition descends the point. After each quotient, its reduction equals the
   prescribed point after this cover, hence already equals it by the sheaf condition
   (def-pc-fppf-site, def-weil-pbc-sites-and-cohomology, def-trf-algebraic-space,
   def-weil-etale-morphism, lem-pc-yoneda). This proves surjectivity. -/
theorem bijective_completeLocalPointRestriction {S : Scheme.{u}} (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : Spec (.of A) ⟶ S) (B : AlgebraicSpace S) :
    Function.Bijective (completeLocalPointRestriction f B) := by
  sorry

end AlgebraicGeometry
