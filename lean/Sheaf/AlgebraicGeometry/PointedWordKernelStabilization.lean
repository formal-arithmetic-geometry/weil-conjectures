/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.ConnectedPointGeometricallyConnected
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleProduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Stabilization of pointed word-map kernels

Source: Milne, Algebraic Groups (2017), Section 2h, pp.54–56, and Proposition 6.20(a),
p.130 (blueprint: lem-sfb-pointed-word-kernel-stabilization).

The auxiliary definitions spell out the canonical product word map and its coordinate-ring
kernel. The power with `n` blocks of size `r` is the finite fibre product `(G^r)^n = G^(rn)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The ordered product of `n` copies of a morphism to a group scheme, on the `n`-fold
fibre product of its source over the base. No homomorphism condition is imposed.
Source: Milne, Section 2h, p.54 (blueprint: lem-sfb-pointed-word-kernel-stabilization). -/
noncomputable def pointedProductWord {S : Scheme.{u}} {X J : Over S} [GrpObj J]
    (φ : X ⟶ J) (n : ℕ) : (∏ᶜ fun _ : Fin n ↦ X) ⟶ J :=
  (List.ofFn fun i : Fin n ↦ Pi.π (fun _ : Fin n ↦ X) i ≫ φ).prod

/-- The ideal of functions killed by the pointed product word map.
Source: Milne, Section 2h, p.54 and Proposition 6.20(a), p.130
(blueprint: lem-sfb-pointed-word-kernel-stabilization). -/
noncomputable def pointedProductWordKernel {S : Scheme.{u}} {X J : Over S} [GrpObj J]
    (φ : X ⟶ J) (n : ℕ) : Ideal Γ(J.left, ⊤) :=
  RingHom.ker (pointedProductWord φ n).left.appTop.hom

/-- Every positive power of a smooth connected affine group over an algebraically closed
field is geometrically integral. The kernels of the pointed word maps from its powers
stabilize at a prime ideal, and the stabilized quotient is integral and receives the
word map with dense image and injective pullback on coordinate rings.

Source: Milne, Section 2h, pp.54–56 and Proposition 6.20(a), p.130
(blueprint: lem-sfb-pointed-word-kernel-stabilization).

Proof:
1. The identity has residue field `k`. Apply
   lem-trf-connected-point-geometrically-connected, then
   lem-trf-smooth-connected-fibre-normal-integrality, to get geometric integrality of `G`.
2. Induct on positive powers. Affineness follows from
   lem-weil-pbc-fibre-product-affine-spectra; smoothness from clause (2) of
   lem-pc-proper-base-change and lem-trf-smooth-composition; geometric irreducibility from
   lem-sc-geometrically-irreducible-product. Apply sbc-lem-smooth-geometrically-reduced;
   reducedness and irreducibility give integrality over every field extension.
3. Appending the identity block gives `w_(n+1) ∘ s_n = w_n`. Thus the kernels descend.
   The source coordinate rings are nonzero domains, so all the kernels are proper prime.
4. Apply lem-kun-dimension-finite-type, with def-kun-dimension and
   def-kun-topological-krull-dimension, to bound strict chains of irreducible closed subsets
   of `J`. Strict prime drops give strict increases of their zero loci, so they are bounded.
5. If no tail were constant, repeatedly choosing a later strict drop would exceed this
   bound. Hence some positive `N` gives a constant tail and a prime stabilized kernel.
6. Descent shows that the intersection of all positive kernels equals that kernel.
   Its quotient is a domain, hence its spectrum is integral (def-pc-integral-scheme and
   def-pc-reduced-scheme). The quotient universal property
   (def-weil-pbc-algebra-hom-quotient) gives the factorization and injective pullback.
7. The injective quotient map on coordinate rings carries the zero prime of the domain
   source ring to the zero prime of the quotient. The latter is a generic point, proving
   density, by def-weil-affine-spectrum.
-/
theorem pointedProductWordKernel_stabilization
    (k : Type u) [Field k] [IsAlgClosed k]
    (G J : Over (Spec (.of k))) [GrpObj G] [GrpObj J]
    [IsAffine G.left] [IsAffine J.left] [Smooth G.hom] [ConnectedSpace G.left]
    [LocallyOfFiniteType J.hom] (r : ℕ) (hr : 1 ≤ r)
    (φ : (∏ᶜ fun _ : Fin r ↦ G) ⟶ J)
    (hφ : Pi.lift (fun _ : Fin r ↦ (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G)) ≫ φ = 1) :
    (∀ m : ℕ, 1 ≤ m → GeometricallyIntegral (∏ᶜ fun _ : Fin m ↦ G).hom) ∧
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ n : ℕ, N ≤ n → pointedProductWordKernel φ n = pointedProductWordKernel φ N) ∧
      (pointedProductWordKernel φ N).IsPrime ∧
      (⨅ n : {n : ℕ // 1 ≤ n}, pointedProductWordKernel φ n.val) =
        pointedProductWordKernel φ N ∧
      IsIntegral (Spec (.of (Γ(J.left, ⊤) ⧸ pointedProductWordKernel φ N))) ∧
      ∃ v : (∏ᶜ fun _ : Fin N ↦ (∏ᶜ fun _ : Fin r ↦ G)).left ⟶
          Spec (.of (Γ(J.left, ⊤) ⧸ pointedProductWordKernel φ N)),
        v ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (pointedProductWordKernel φ N))) ≫ J.left.isoSpec.inv =
            (pointedProductWord φ N).left ∧
        DenseRange v.base ∧ Function.Injective v.appTop := by
  sorry

end AlgebraicGeometry
