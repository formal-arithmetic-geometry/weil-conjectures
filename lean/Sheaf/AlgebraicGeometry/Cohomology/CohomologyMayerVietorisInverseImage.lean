/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Exact.Basic
import Sheaf.Topology.ModuleMayerVietoris

/-! # Mayer--Vietoris naturality before scalar extension

Source: Stacks Project, Tags 01EB and 02KH.
(blueprint: lem-pc-cohomology-mayer-vietoris-inverse-image)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The original and pulled-back Mayer--Vietoris sequences are compatible with
`H.baseChangeLinear`, before tensoring. Neither flatness nor quasi-coherence is needed.

Source: Stacks Project, Tag 01EB, cohomology-lemma-mayer-vietoris, and Tag 02KH,
coherent-lemma-flat-base-change-cohomology, Mayer--Vietoris alternative.
(blueprint: lem-pc-cohomology-mayer-vietoris-inverse-image)

Proof: Form the Mayer--Vietoris sequences for M and its pullback using Tag 01EB.
Restriction and connecting maps commute with scalar endomorphisms of M by
naturality, giving R-linear maps in the original sequence and S-linear maps in
the pulled-back sequence. The inverse-image opens cover the pullback scheme;
the cartesian open-subscheme isomorphisms and pullback composition isomorphisms
identify their restricted cohomology with the displayed B terms. Exact inverse
image on abelian sheaves transports the Mayer--Vietoris short exact sequence of
free abelian sheaves to that for the inverse-image cover: inverse image of the
free sheaf represented by W is the free sheaf represented by its preimage,
since both represent sections of pushforward on W under the adjunction and
the free-sheaf universal property. These identifications commute with inclusions.
Applying Ext to this
short exact sequence gives the original cohomology sequence. The constant-sheaf
comparison and adjoint coefficient map used in H.baseChangeLinear induce a
morphism to the pulled-back sequence. Ext functoriality gives the restriction
and difference squares. Each connecting homomorphism is Yoneda composition with
the short exact sequence class; exact inverse image preserves that class and
Yoneda composition, giving the boundary square. The free-sheaf identifications
for the union and individual opens identify these vertical maps with precisely
H.baseChangeLinear. The initial injections and exactness of the two rows come
from their Mayer--Vietoris sequences. No tensor product or flatness is used. -/
theorem H.baseChangeLinear_mayerVietoris
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let A := fun (W : X.Opens) (n : ℕ) ↦
      HOver (W.ι ≫ f) ((pullback W.ι).obj M) n
    let B := fun (W : X.Opens) (n : ℕ) ↦
      HOver (baseChangeSnd (S := S) (W.ι ≫ f))
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M)) n
    let AX := fun n : ℕ ↦ HOver f M n
    let BX := fun n : ℕ ↦
      HOver (baseChangeSnd (S := S) f) (baseChangedModule (S := S) f M) n
    let β := fun (W : X.Opens) (n : ℕ) ↦
      H.baseChangeLinear (S := S) (W.ι ≫ f) ((pullback W.ι).obj M) n
    let βX := fun n : ℕ ↦ H.baseChangeLinear (S := S) f M n
    ∃ (r : ∀ n : ℕ, AX n →ₗ[R] A U n × A V n)
      (d : ∀ n : ℕ, A U n × A V n →ₗ[R] A (U ⊓ V) n)
      (δ : ∀ n : ℕ, A (U ⊓ V) n →ₗ[R] AX (n + 1))
      (r' : ∀ n : ℕ, BX n →ₗ[S] B U n × B V n)
      (d' : ∀ n : ℕ, B U n × B V n →ₗ[S] B (U ⊓ V) n)
      (δ' : ∀ n : ℕ, B (U ⊓ V) n →ₗ[S] BX (n + 1)),
      Function.Injective (r 0) ∧ Function.Injective (r' 0) ∧
      (∀ n : ℕ, Function.Exact (r n) (d n) ∧
        Function.Exact (d n) (δ n) ∧ Function.Exact (δ n) (r (n + 1))) ∧
      (∀ n : ℕ, Function.Exact (r' n) (d' n) ∧
        Function.Exact (d' n) (δ' n) ∧ Function.Exact (δ' n) (r' (n + 1))) ∧
      (∀ (n : ℕ) (x : AX n), r' n (βX n x) =
        (β U n (r n x).1, β V n (r n x).2)) ∧
      (∀ (n : ℕ) (x : A U n × A V n),
        d' n (β U n x.1, β V n x.2) = β (U ⊓ V) n (d n x)) ∧
      (∀ (n : ℕ) (x : A (U ⊓ V) n),
        δ' n (β (U ⊓ V) n x) = βX (n + 1) (δ n x)) := by sorry

end AlgebraicGeometry.Scheme.Modules
