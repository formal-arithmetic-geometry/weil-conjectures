/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale

/-! # Étale descent of affine pinching squares

Source: Stacks Project, More on Morphisms, Tags 0ET0 and 0BMP; Descent, Tag 023Q.
The exact-sequence and flat-base-change formulation is the agent refinement in
(blueprint: lem-sfb-etale-affine-pinching-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The canonical flat-base-change comparison sends `h` to the matching pair
`(h ⊗ 1, h ⊗ 1)`. The target is Mathlib's explicit ring of matching pairs,
with componentwise ring operations; the definition requires no flatness.

Source: Stacks Project, Tag 0ET0, and the tensor calculation in step 2 of
(blueprint: lem-sfb-etale-affine-pinching-descent). -/
def pinchingTensorComparison
    {P E T D : Type u} [CommRing P] [CommRing E] [CommRing T] [CommRing D]
    [Algebra P E] [Algebra P T] [Algebra P D]
    (α : E →ₐ[P] D) (β : T →ₐ[P] D)
    (H : Type (max u w)) [CommRing H] [Algebra P H] :
    H →+* (CommRingCat.pullbackCone
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id P H) α).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id P H) β).toRingHom)).pt :=
  ((Algebra.TensorProduct.includeLeftRingHom (R := P) (A := H) (B := E)).prod
    (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := H) (B := T))).codRestrict
      (RingHom.eqLocus
        ((Algebra.TensorProduct.map (AlgHom.id P H) α).toRingHom.comp
          (RingHom.fst (H ⊗[P] E) (H ⊗[P] T)))
        ((Algebra.TensorProduct.map (AlgHom.id P H) β).toRingHom.comp
          (RingHom.snd (H ⊗[P] E) (H ⊗[P] T))))
      (fun h ↦ by simp)

/-- Affine étale charts with the canonical short exact difference sequence give
pushouts in schemes, also on every open and after every flat base change.
The final clause says the canonical tensor comparison is a ring isomorphism,
expressed as bijectivity of that specified ring homomorphism.

`hC` and `hN` identify the specified spectra with the actual inverse images.
`hB` identifies `Spec D` with their fibre product, hence with the inverse image
of `B = C ×[X] N`. Its maps are exactly `Spec α` and `Spec β`.

Source: Stacks Project, Tags 0ET0 (`lemma-basic-example-pushout`), 0BMP
(`lemma-pushout-fpqc-local`), and 023Q; agent exact-sequence criterion and
flat-base-change refinement (blueprint: lem-sfb-etale-affine-pinching-descent).

Proof plan:
1. Exactness makes P → E ×[D] T injective and surjective onto matching pairs,
   hence a ring isomorphism, without assuming that Spec preserves ring limits.
2. For flat H, apply `lem-weil-pbc-flat-tensor-exact` to the injection and
   kernel, `lem-weil-pbc-tensor-right-exact` to the last surjection, and
   `lem-weil-pbc-algebra-tensor-product-distributes-product` to E ⊕ T.
   The resulting kernel is exactly the matching-pairs ring of the tensor maps,
   and its comparison sends h to (h ⊗ 1, h ⊗ 1). Tensoring α stays surjective
   since every tensor is a finite sum of pure tensors and α is surjective.
3. Use `lem-weil-pbc-fibre-product-affine-spectra` to identify all base-changed
   affine pieces with these tensors. The affine closed-pinching theorem
   `lem-sfb-affine-closed-pinching-pushout` then gives their pushout for maps
   into any scheme, in particular over every affine flat chart.
4. Open immersions are flat on local rings. Restricting a flat morphism to
   an open preserves flatness. Compositions are flat by
   `lem-weil-pbc-flat-ring-map-comp`; base changes are flat by
   `lem-weil-pbc-flat-morphism-base-change`. The affine criterion
   `lem-weil-pbc-flat-morphism-affine-criterion` makes every affine open of
   a flat scheme over Spec P into a flat P-algebra.
5. Cover any flat Y over a chart by affine opens using
   `lem-weil-pbc-affine-opens-basis`. Step 3 gives unique extensions there.
   Cover each pairwise intersection by affine opens and apply uniqueness
   again. `lem-weil-pbc-scheme-morphism-gluing` glues these extensions and
   proves their uniqueness, with no quasi-separatedness assumption on Y.
6. The given étale cover is fpqc by `lem-weil-pbc-fpqc-finer-than-etale`.
   For a flat X' → X pull it back, using `lem-weil-pbc-fpqc-covering-axioms`.
   Its members and their pairwise overlaps are flat over the original charts
   by step 4, so step 5 gives pushouts on both. The fibre-product universal
   property identifies their prescribed C, N, B pieces in either order.
7. Given compatible maps from C_X' and N_X' into any scheme Z, obtain maps
   from each cover member by step 5. Their restrictions to overlaps agree
   by the pushout uniqueness there. `lem-weil-pbc-fpqc-representable-descent`
   glues them uniquely. Base change the cover to C_X' and N_X' and use the
   uniqueness part of descent to verify the prescribed restrictions.
8. Specialize to the identity to get the original pushout, and to every open
   inclusion to get open restriction. Step 2 gives the tensor assertion.
   Empty schemes, zero rings and empty covers obey the same kernel and gluing
   calculations. The cover index has unrestricted set cardinality.
-/
theorem isPushout_of_etale_affine_pinching_exact
    {X C N : Scheme.{u}} (ν : C ⟶ X) (i : N ⟶ X)
    [IsFinite ν] [IsClosedImmersion i]
    {A : Type v} (P E T D : A → Type u)
    [∀ a, CommRing (P a)] [∀ a, CommRing (E a)]
    [∀ a, CommRing (T a)] [∀ a, CommRing (D a)]
    [∀ a, Algebra (P a) (E a)] [∀ a, Algebra (P a) (T a)]
    [∀ a, Algebra (P a) (D a)]
    (α : ∀ a, E a →ₐ[P a] D a) (β : ∀ a, T a →ₐ[P a] D a)
    (q : ∀ a, Spec (CommRingCat.of (P a)) ⟶ X)
    [∀ a, Etale (q a)]
    (hcover : ∀ x : X, ∃ a, ∃ y : Spec (CommRingCat.of (P a)), q a y = x)
    (c : ∀ a, Spec (CommRingCat.of (E a)) ⟶ C)
    (n : ∀ a, Spec (CommRingCat.of (T a)) ⟶ N)
    (hC : ∀ a, IsPullback (c a)
      (Spec.map (CommRingCat.ofHom (algebraMap (P a) (E a)))) ν (q a))
    (hN : ∀ a, IsPullback (n a)
      (Spec.map (CommRingCat.ofHom (algebraMap (P a) (T a)))) i (q a))
    (hB : ∀ a, IsPullback
      (Spec.map (CommRingCat.ofHom (α a).toRingHom))
      (Spec.map (CommRingCat.ofHom (β a).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (P a) (E a))))
      (Spec.map (CommRingCat.ofHom (algebraMap (P a) (T a)))))
    (hinj : ∀ a, Function.Injective
      (fun p : P a ↦ (algebraMap (P a) (E a) p, algebraMap (P a) (T a) p)))
    (hexact : ∀ a, Function.Exact
      (fun p : P a ↦ (algebraMap (P a) (E a) p, algebraMap (P a) (T a) p))
      (fun z : E a × T a ↦ α a z.1 - β a z.2))
    (hsurj : ∀ a, Function.Surjective (fun z : E a × T a ↦ α a z.1 - β a z.2))
    (hα : ∀ a, Function.Surjective (α a)) :
    IsPushout (pullback.fst ν i) (pullback.snd ν i) ν i ∧
    (∀ V : X.Opens,
      IsPushout
        (pullback.fst (pullback.snd ν V.ι) (pullback.snd i V.ι))
        (pullback.snd (pullback.snd ν V.ι) (pullback.snd i V.ι))
        (pullback.snd ν V.ι) (pullback.snd i V.ι)) ∧
    (∀ (X' : Scheme.{u}) (f : X' ⟶ X), Flat f →
      IsPushout
        (pullback.fst (pullback.snd ν f) (pullback.snd i f))
        (pullback.snd (pullback.snd ν f) (pullback.snd i f))
        (pullback.snd ν f) (pullback.snd i f)) ∧
    (∀ (a : A) (H : Type (max u w)) [CommRing H] [Algebra (P a) H],
      Module.Flat (P a) H → Function.Bijective (pinchingTensorComparison (α a) (β a) H)) := by
  sorry

end AlgebraicGeometry
