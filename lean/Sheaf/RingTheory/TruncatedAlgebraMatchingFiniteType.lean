/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType

/-!
# Finite type of truncated algebra matching objects

Source: Stacks Project, Cotangent Complex, Tag 08PW (`lemma-polynomial`),
and More on Algebra, Tag 08NI (`lemma-formal-consequence`)
(blueprint: lem-sfb-truncated-algebra-matching-finite-type).

The matching algebra is constructed as compatible proper-face families over a
common element of the augmentation algebra. Intersections of algebra equalizers
supply its actual componentwise operations, without choosing an unknown object.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace Algebra

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The ambient algebra for proper-face families in degree `k`: a common augmentation
value and a value on every simplex of dimension less than `k` in the truncation.
Source: Stacks Project, Tag 08PW, compatible families on skeleta
(blueprint: lem-sfb-truncated-algebra-matching-finite-type). -/
abbrev truncatedMatchingAmbient
    (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n)
    (B : CommAlgCat.{v} A) (k : ℕ) :=
  B × ((r : {r : SimplexCategory.Truncated n // r.obj.len < k}) →
    (r.val.obj ⟶ SimplexCategory.mk k) → P.obj (op r.val))

/-- Evaluation at a proper simplex, as an algebra homomorphism on the ambient product.
Source: Stacks Project, Tag 08PW, restriction of compatible families
(blueprint: lem-sfb-truncated-algebra-matching-finite-type). -/
def truncatedMatchingEval
    (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n)
    (B : CommAlgCat.{v} A) (k : ℕ)
    (r : {r : SimplexCategory.Truncated n // r.obj.len < k})
    (θ : r.val.obj ⟶ SimplexCategory.mk k) :
    truncatedMatchingAmbient P B k →ₐ[A] P.obj (op r.val) :=
  (Pi.evalAlgHom A (fun _ : r.val.obj ⟶ SimplexCategory.mk k ↦
    P.obj (op r.val)) θ).comp
    ((Pi.evalAlgHom A (fun s : {s : SimplexCategory.Truncated n // s.obj.len < k} ↦
      (s.val.obj ⟶ SimplexCategory.mk k) → P.obj (op s.val)) r).comp (AlgHom.snd A B _))

/-- The relative matching algebra in degree `k`, in its compatible-family presentation.
The first intersection imposes the common augmentation value; the second imposes
`x_(α ≫ θ) = P(α)(x_θ)` for every map of proper simplices. All operations are inherited
from the ambient product. In degree zero this is canonically `B`; in degree one it
is `P₀ ×_B P₀`. In higher degrees restriction to the facets gives exactly the tuple
condition `d_i p_j = d_(j-1) p_i` for `i < j`: intersecting facets determine lower
injective faces, and degeneracies determine all noninjective simplices.
Source: Stacks Project, Tag 08PW, compatible families on skeleta
(blueprint: lem-sfb-truncated-algebra-matching-finite-type). -/
def truncatedMatchingAlgebra
    (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n)
    (B : CommAlgCat.{v} A)
    (ε : P ⟶ (Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj B) (k : ℕ) :
    Subalgebra A (truncatedMatchingAmbient P B k) :=
  (⨅ (r : {r : SimplexCategory.Truncated n // r.obj.len < k})
      (θ : r.val.obj ⟶ SimplexCategory.mk k),
    AlgHom.equalizer
      ((ε.app (op r.val)).hom.comp (truncatedMatchingEval P B k r θ))
      (AlgHom.fst A B _)) ⊓
  (⨅ (r : {r : SimplexCategory.Truncated n // r.obj.len < k})
      (s : {s : SimplexCategory.Truncated n // s.obj.len < k})
      (α : r.val ⟶ s.val) (θ : s.val.obj ⟶ SimplexCategory.mk k),
    AlgHom.equalizer (truncatedMatchingEval P B k r (α.hom ≫ θ))
      ((P.map α.op).hom.comp (truncatedMatchingEval P B k s θ)))

/-- Surjectivity of the canonical matching map in a degree belonging to the truncation.
Its graph sends `p` to its augmentation and to `P(θ)(p)` on every proper simplex.
Thus this is precisely surjectivity of the augmentation in degree zero, and of
`p ↦ (d₀ p, …, d_k p)` in positive degree. No extra map is supplied as a hypothesis.
Source: Stacks Project, Tag 08PW, surjective boundary matching maps
(blueprint: lem-sfb-truncated-algebra-matching-finite-type). -/
def TruncatedMatchingSurjective
    (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n)
    (B : CommAlgCat.{v} A)
    (ε : P ⟶ (Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj B)
    (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ x : truncatedMatchingAlgebra P B ε k,
    ∃ p : P.obj (op ⟨SimplexCategory.mk k, hk⟩),
      (ε.app (op ⟨SimplexCategory.mk k, hk⟩)).hom p = x.val.1 ∧
      ∀ (r : {r : SimplexCategory.Truncated n // r.obj.len < k})
        (θ : r.val.obj ⟶ SimplexCategory.mk k),
        (P.map (CategoryTheory.ObjectProperty.homMk θ).op).hom p = x.val.2 r θ

/-- The next relative matching algebra is finite type when all terms and lower matching
maps of a finite truncation have the stated finiteness and surjectivity properties.

Source: Stacks Project, Cotangent Complex, Tag 08PW (`lemma-polynomial`),
with the finite-type input More on Algebra, Tag 08NI (`lemma-formal-consequence`)
(blueprint: lem-sfb-truncated-algebra-matching-finite-type).

Proof:
1. For `-1 ≤ j ≤ n` and `j ≤ m ≤ n+1`, form `C_(j,m)` from a common element
   of `B` and compatible values on every simplex of dimension at most `j` in
   `[m]`. Set `C_(-1,m) = B`. Evaluation at the identity identifies `C_(j,j)`
   with `P_j`, by the functor identities.
2. Restriction to the facets identifies `C_(k-1,k)` with the matching algebra.
   Facet intersection identities give precisely the displayed pairwise face
   equations. Every map factors uniquely into a surjection followed by an
   injection, so degeneracies force all remaining values. For `k=1` the common
   element of `B` gives the fibre-product condition. For `k≥2`, the edges force
   all vertex augmentations to agree, so the common element is already determined.
3. Restriction from `C_(k-1,m)` to any injective `k`-face is surjective. For `k=0`
   it is the identity of `B`. Otherwise an increasing injection `E : [k] → [m]`
   has the monotone retraction `ρ(t) = max ({0} ∪ {j | E(j) ≤ t})`. Precomposing
   a compatible family with `ρ` gives an algebra section of restriction.
4. There is a cartesian description of `C_(k,m)` as the pullback of
   `∏_E P_k → ∏_E C_(k-1,k)` along `C_(k-1,m) → ∏_E C_(k-1,k)`, where `E`
   ranges over the finitely many injective `k`-faces. A lower family and values
   on these faces with the prescribed boundaries determine the entire family;
   different injective faces meet only in lower dimensions.
5. Induct on `k`, starting with the finite type algebra `B`. The diagonal case
   is `P_k`, finite type by hypothesis. For `m>k`, apply
   `lem-sfb-finite-type-surjective-product-pullback` to the cartesian description:
   the lower family algebras are finite type by induction, the `P_k` are finite
   type by hypothesis, the matching maps are surjective by hypothesis, and the
   restriction maps are surjective by step 3. The base ring is Noetherian.
6. Take `k=n` and `m=n+1`. This family algebra is the required matching algebra.
   For `n=0` the argument is exactly finite type of `P₀ ×_B P₀`. -/
theorem truncatedMatchingAlgebra_finiteType
    (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ)
    (B : CommAlgCat.{v} A) (_hB : RingHom.FiniteType (algebraMap A B))
    (P : SimplicialObject.Truncated (CommAlgCat.{v} A) n)
    (ε : P ⟶ (Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj B)
    (_hP : ∀ r : SimplexCategory.Truncated n,
      RingHom.FiniteType (algebraMap A (P.obj (op r))))
    (_hμ : ∀ (k : ℕ) (hk : k ≤ n), TruncatedMatchingSurjective P B ε k hk) :
    RingHom.FiniteType (algebraMap A (truncatedMatchingAlgebra P B ε (n + 1))) := by
  sorry

end Algebra
