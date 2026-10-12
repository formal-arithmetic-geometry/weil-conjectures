/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Exact.Basic
import Sheaf.Topology.ModuleMayerVietoris

/-! # The flat base-change Mayer--Vietoris comparison diagram

Source: Stacks Project, Tags 02KH and 01EB, the Mayer--Vietoris proof of flat
base change (blueprint: lem-pc-flat-cohomology-mayer-vietoris).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical flat base-change comparisons form a morphism of exact
Mayer--Vietoris sequences. This assertion assumes no local comparison is bijective.
The upper terms are tensor products of the original cohomology, with the binary
sum identified with the product of the two tensor products. The lower terms use
base changes of the individual opens, transported by the cartesian open-subscheme
isomorphisms and the iterated module-pullback isomorphisms.

Source: Stacks Project, Tag 02KH (coherent-lemma-flat-base-change-cohomology),
Mayer--Vietoris alternative, and Tag 01EB (cohomology-lemma-mayer-vietoris).
(blueprint: lem-pc-flat-cohomology-mayer-vietoris)

Proof: Apply the ringed-space module Mayer--Vietoris sequence to M and the cover
X = U union V. Its maps are R-linear: restriction commutes with multiplication by
a global scalar, and naturality in the module gives the same assertion for the
boundary maps. Tensor this exact sequence with S. Flatness preserves its exactness
and the initial injection; use the canonical tensor/product isomorphism for the
binary sum to obtain r, d and delta below. Apply Mayer--Vietoris to the pullback of
M and the inverse images of U and V in X_S. Preimage preserves union and
intersection, so these opens cover X_S and their intersection is the inverse image
of U intersect V. Base change of each open identifies it with that inverse image;
functoriality of module pullback identifies the corresponding restricted modules.
Transport the lower sequence by these isomorphisms to obtain r', d' and delta'.
For the commuting squares, the inverse-image functor on abelian sheaves is exact.
The sheaf Mayer--Vietoris short exact sequence (the free abelian sheaves on the
intersection, the two opens and their union) pulls back to the corresponding
sequence on the inverse-image cover. Functoriality of Ext, the constant-sheaf
comparison and the adjoint coefficient map defining H.baseChangeLinear therefore
give a morphism of the long exact sequences. The restriction squares follow from
functoriality of Ext; the boundary square follows because Ext boundaries are
Yoneda composition with the short exact sequence class, and exact inverse image
preserves this class and Yoneda composition. Thus the three squares commute before
extending scalars. Since all horizontal maps are linear, tensor extension gives
the displayed squares: on a pure tensor s tensor x both composites equal s times
the common value before scalar extension, and pure tensors generate. No conclusion
about bijectivity of a comparison is used in this construction. -/
theorem H.baseChange_mayerVietoris
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let A := fun (W : X.Opens) (n : ℕ) ↦
      TensorProduct R S (HOver (W.ι ≫ f) ((pullback W.ι).obj M) n)
    let B := fun (W : X.Opens) (n : ℕ) ↦
      HOver (baseChangeSnd (S := S) (W.ι ≫ f))
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M)) n
    let AX := fun n : ℕ ↦ TensorProduct R S (HOver f M n)
    let BX := fun n : ℕ ↦
      HOver (baseChangeSnd (S := S) f) (baseChangedModule (S := S) f M) n
    let β := fun (W : X.Opens) (n : ℕ) ↦
      H.baseChange (S := S) (W.ι ≫ f) ((pullback W.ι).obj M) n
    let βX := fun n : ℕ ↦ H.baseChange (S := S) f M n
    ∃ (r : ∀ n : ℕ, AX n →ₗ[S] A U n × A V n)
      (d : ∀ n : ℕ, A U n × A V n →ₗ[S] A (U ⊓ V) n)
      (δ : ∀ n : ℕ, A (U ⊓ V) n →ₗ[S] AX (n + 1))
      (r' : ∀ n : ℕ, BX n →ₗ[S] B U n × B V n)
      (d' : ∀ n : ℕ, B U n × B V n →ₗ[S] B (U ⊓ V) n)
      (δ' : ∀ n : ℕ, B (U ⊓ V) n →ₗ[S] BX (n + 1)),
      Function.Injective (r 0) ∧ Function.Injective (r' 0) ∧
      (∀ n : ℕ, Function.Exact (r n) (d n) ∧
        Function.Exact (d n) (δ n) ∧ Function.Exact (δ n) (r (n + 1))) ∧
      (∀ n : ℕ, Function.Exact (r' n) (d' n) ∧
        Function.Exact (d' n) (δ' n) ∧ Function.Exact (δ' n) (r' (n + 1))) ∧
      (∀ n : ℕ, (r' n).comp (βX n) = ((β U n).prodMap (β V n)).comp (r n)) ∧
      (∀ n : ℕ, (d' n).comp ((β U n).prodMap (β V n)) =
        (β (U ⊓ V) n).comp (d n)) ∧
      (∀ n : ℕ, (δ' n).comp (β (U ⊓ V) n) = (βX (n + 1)).comp (δ n)) := by sorry

end AlgebraicGeometry.Scheme.Modules
