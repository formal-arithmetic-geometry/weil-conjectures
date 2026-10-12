/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.MeromorphicModule
public import Sheaf.RingTheory.WeaklyAssociated
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.TotalQuotientRingMinimalProduct
import Sheaf.RingTheory.WeakAssZeroDivisors

/-!
# Meromorphic modules as products at generic points

Source: Stacks Project, Divisors, Lemma 31.24.6 (Tag 0EMF)
(blueprint: lem-sc-meromorphic-weakass-generic-product).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The generic-point product descriptions of the meromorphic sheaf and of the meromorphic
module of a quasi-coherent module. The product isomorphisms are the canonical ones: composed
with `toMeromorphicModule` and the projection at a generic point, the first is the canonical
map O_X → j_{η,*} O_{X,η}, the second sends a section to the image of its germ at η.
The index subtype consists of all generic points of irreducible components, without a
global finiteness assumption. The local-ring module in
each factor is regarded as its associated sheaf on the spectrum of that local ring.
Source: Stacks Project, Divisors, Lemma 31.24.6 (Tag 0EMF)
(blueprint: lem-sc-meromorphic-weakass-generic-product).

Proof:
1. On an affine open Spec A there are finitely many minimal primes q_i by `hfinite`.
   Weak association of a prime is equivalent to weak association at its point (Tag 0566).
   By `hweak` all weakly associated primes are minimal. Apply
   `lem-sc-affine-weakass-nonzerodivisors` and
   `lem-sc-affine-totalquotient-minimal-product` to obtain Q(A) = product_i A_{q_i}.
2. A generic point in this affine open contributes A_{q_i} to its pushforward, and a
   generic point outside contributes zero. The fraction maps in step 1 agree with
   restriction, so these affine-basis identifications glue to the first isomorphism.
3. For a quasi-coherent F with affine module M, tensor the finite decomposition with M:
   Q(A) tensor_A M = product_i (A_{q_i} tensor_A M) = product_i M_{q_i}.
   These localizations are the stalks F_eta. The fraction and restriction maps are
   compatible, giving both isomorphisms in the second and third conjuncts. -/
theorem meromorphicModule_generic_product (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) :
    (∃ e : meromorphicModule X (unit X) ≅
        ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
          (pushforward (X.fromSpecStalk η.val)).obj (unit (Spec (X.presheaf.stalk η.val)))),
      ∀ η : {x : X // x ∈ genericPoints X},
        toMeromorphicModule X (unit X) ≫ e.hom ≫ Pi.π _ η =
          SheafOfModules.unitToPushforwardObjUnit (X.fromSpecStalk η.val).toRingCatSheafHom) ∧
    Nonempty ((meromorphicModule X (unit X) ⊗ F) ≅ meromorphicModule X F) ∧
    (∃ e : meromorphicModule X F ≅
        ∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
          (pushforward (X.fromSpecStalk η.val)).obj
            (tilde (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val)))),
      ∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U) (m : Γ(F, U)),
        (toMeromorphicModule X F ≫ e.hom ≫ Pi.π _ η).val.app (op U) m =
          tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
            (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
