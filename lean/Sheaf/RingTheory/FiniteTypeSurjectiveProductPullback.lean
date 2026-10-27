module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite type for a coordinatewise surjective product pullback

Source: Stacks Project, More on Algebra, Tag 08NI (`lemma-formal-consequence`),
using Tag 00IT (`lemma-fibre-product-finite-type`).
(blueprint: lem-sfb-finite-type-surjective-product-pullback)
-/

@[expose] public section

set_option autoImplicit false

universe uR uI uQ uC uD

namespace AlgHom

/-- The subalgebra of pairs `(q, c)` satisfying `ψ i q = φ i (c i)` for every `i`.
It is Mathlib's equalizer of the two maps to `Π i, D i`, so its algebra operations
are the componentwise operations inherited from `Q × Π i, C i`.

Source: Stacks Project, Tag 08NI (`lemma-formal-consequence`), the cartesian ring.
(blueprint: lem-sfb-finite-type-surjective-product-pullback) -/
def productPullbackSubalgebra
    (R : Type uR) [CommRing R] (I : Type uI) (Q : Type uQ) [CommRing Q]
    [Algebra R Q] (C : I → Type uC) (D : I → Type uD)
    [∀ i : I, CommRing (C i)] [∀ i : I, CommRing (D i)]
    [∀ i : I, Algebra R (C i)] [∀ i : I, Algebra R (D i)]
    (φ : ∀ i : I, C i →ₐ[R] D i) (ψ : ∀ i : I, Q →ₐ[R] D i) :
    Subalgebra R (Q × ∀ i : I, C i) :=
  equalizer ((pi ψ).comp (fst R Q (∀ i : I, C i)))
    ((pi (fun i : I ↦ (φ i).comp (Pi.evalAlgHom R C i))).comp
      (snd R Q (∀ i : I, C i)))

/-- The coordinatewise surjective product pullback of finite type algebras over a
Noetherian ring is finite type. For an empty index type the product has one element,
and the pullback is isomorphic to `Q` as an `R`-algebra.

Source: Stacks Project, Tag 08NI (`lemma-formal-consequence`), with the two-surjection
case of Tag 00IT (`lemma-fibre-product-finite-type`).
(blueprint: lem-sfb-finite-type-surjective-product-pullback)

Proof:
1. Induct on the size of `I`, uniformly in all the algebra data. For the empty set,
   `q ↦ (q, ())` and the first projection are inverse algebra maps. The empty product
   has one element, and generators for `Q` therefore generate the pullback. For any
   subset `J`, its pullback projects surjectively to `Q`: lift each `ψ j q` along `φ j`.
2. Write `I = J ⨿ {i}`. By induction `A = T_J` is finite type. The composite
   `α : A → Q → D i` is surjective. Regrouping coordinates identifies `T` with
   `P = A ×_{D i} C i`; regrouping and deleting the last coordinate are inverse
   algebra maps, preserving all componentwise operations and scalars.
3. The algebra `B = A × C i` is finite type: if `a_u` and `c_v` are generators,
   take `(1,0)`, `(0,1)`, `(a_u,0)`, and `(0,c_v)`. Multiplication by the first
   two idempotents turns polynomial expressions into either component separately.
4. Both projections `P → A` and `P → C i` are surjective, by lifting along `φ i`
   and `α`, respectively. For `(a,c)` choose `(a,c')` and `(a',c)` in `P`. Then
   `(a,c) = (a,c') (1,0) + (a',c) (0,1)`, so `B` is a finite `P`-module, using
   `Module.Finite` (def-weil-finitely-generated-module).
5. Apply `fg_of_fg_of_fg` (lem-sfb-artin-tate-subalgebra-finite-type) to
   `R → P → B`. The Noetherian base, finite type of `B`, module finiteness over `P`,
   and injective subalgebra inclusion give finite type of `P`. The coordinate
   isomorphism in step 2 transports generators to `T`, completing the induction. -/
theorem finiteType_productPullbackSubalgebra
    (R : Type uR) [CommRing R] [IsNoetherianRing R]
    (I : Type uI) [_root_.Finite I] (Q : Type uQ) [CommRing Q] [Algebra R Q]
    [Algebra.FiniteType R Q] (C : I → Type uC) (D : I → Type uD)
    [∀ i : I, CommRing (C i)] [∀ i : I, CommRing (D i)]
    [∀ i : I, Algebra R (C i)] [∀ i : I, Algebra R (D i)]
    [∀ i : I, Algebra.FiniteType R (C i)] [∀ i : I, Algebra.FiniteType R (D i)]
    (φ : ∀ i : I, C i →ₐ[R] D i) (ψ : ∀ i : I, Q →ₐ[R] D i)
    (hφ : ∀ i : I, Function.Surjective (φ i))
    (hψ : ∀ i : I, Function.Surjective (ψ i)) :
    Algebra.FiniteType R (productPullbackSubalgebra R I Q C D φ ψ) ∧
      (IsEmpty I → Subsingleton (∀ i : I, C i) ∧
        Nonempty (productPullbackSubalgebra R I Q C D φ ψ ≃ₐ[R] Q)) := by
  sorry

end AlgHom
