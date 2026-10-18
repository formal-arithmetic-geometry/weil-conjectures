/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Well-definedness and local descriptions of absolute Frobenius

Source: Stacks Project, Varieties, Section 33.36 (Tag 0CC6), the paragraph after
Definition 33.36.1 (Tag 03SM). The open, stalk, affine and iterate descriptions expand this
construction using Sheaves, Tags 0078/007G, and Schemes, Tags 01HE/01I1
(blueprint: lem-weil-absolute-frobenius-well-defined).

We use the published constructions `iterateFrobeniusOfPrime` and `Scheme.iterateFrobenius`.
They allow the zero ring of sections of an empty open. All clauses are stated for every
iterate; setting `n = 1` gives the ordinary Frobenius and `n = 0` gives the identity.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- Absolute Frobenius is well-defined on schemes and has the expected prime-ideal,
local-ring, section, stalk, restriction and affine descriptions, also for all iterates.
The scheme construction is already a morphism of locally ringed spaces: its `c` field is
the restriction-compatible map of structure sheaves and its stalk maps are local.

Source: Stacks Project, Varieties, Tag 03SM and the following paragraph; Sheaves,
Tags 0078/007G; Schemes, Tags 01HE/01I1
(blueprint: lem-weil-absolute-frobenius-well-defined).

Proof for stage 3, following the nine steps of the node:
1. For a prime ideal `P`, closure under multiplication gives `a ∈ P → a ^ p ∈ P`.
   Conversely, primality and induction on a positive exponent give `a ^ p ∈ P → a ∈ P`.
   This applies to `iterateFrobeniusOfPrime` from def-weil-ring-frobenius.
2. The map on `Spec` is prime-ideal inverse image (def-weil-affine-spectrum), so step 1
   makes its continuous map the identity. The spectrum of the zero ring is empty.
3. On a local ring, a unit `a ^ p` makes `a` a unit. Thus Frobenius reflects units and is
   local, equivalently preserves the maximal ideal (def-weil-locally-ringed-space-morphism).
4. The hypothesis def-weil-scheme-characteristic-p annihilates `p` on every open. The
   ring endomorphisms on sections commute with restrictions because ring maps preserve
   powers. Their natural transformation is the structure-sheaf map `c`.
5. Represent a germ by `(U,s)`. Restriction compatibility makes `[U,s] ↦ [U,s ^ p]`
   well-defined; germ operations give `[U,s ^ p] = [U,s] ^ p`. The stalk is local, so
   step 3 makes its Frobenius local. No reducedness or perfection is used.
6. Combine the continuous identity map with the natural sheaf map and local stalk maps.
   This is a locally ringed-space morphism and hence a scheme endomorphism, by
   def-weil-locally-ringed-space-morphism and def-pc-scheme. It is the published
   `Scheme.iterateFrobenius` at `n = 1`.
7. On `Spec A`, the global-sections map is `a ↦ a ^ p`. The affine-spectrum
   correspondence (def-weil-affine-spectrum, Tag 01I1) identifies the morphism with
   `Spec.map` of this ring map.
8. The structure sheaf on an open subscheme is the restricted structure sheaf
   (def-weil-open-immersion). Its power maps are the same sectionwise maps. This proves
   the restriction equality. A ring isomorphism preserves powers, giving the formula
   for any affine chart, not merely a chosen presentation.
9. Induct on `n`, starting at the identity. Prime inverse images compose, local maps
   compose, and powers compose by `(a ^ (p ^ n)) ^ p = a ^ (p ^ (n + 1))`. Apply the
   same calculation to sections and germs. Restricting these maps uses the same powers,
   while contravariant functoriality of `Spec` gives the affine iterate formula. This
   includes `n = 0`, empty opens, the empty scheme, and the zero ring. The scheme
   construction at `n` is the `n`-fold composite (`n`-th power in `End X`) of the one at
   `n = 1`: both have identity base and the same section maps. -/
theorem absoluteFrobenius_well_defined (p : ℕ) (hp : p.Prime) :
    (∀ (A : Type v) [CommRing A] (hA : (p : A) = 0) (n : ℕ),
      (∀ (P : Ideal A), P.IsPrime →
        Ideal.comap (iterateFrobeniusOfPrime A hp hA n) P = P) ∧
      (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime A hp hA n))).base = 𝟙 _ ∧
      (∀ [IsLocalRing A], IsLocalHom (iterateFrobeniusOfPrime A hp hA n)) ∧
      (∀ a : A, ((iterateFrobeniusOfPrime A hp hA 1)^[n]) a = a ^ p ^ n) ∧
      (∃ hSpec : (p : Γ(Spec (CommRingCat.of A), ⊤)) = 0,
        (Spec (CommRingCat.of A)).iterateFrobenius hp hSpec n =
          Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime A hp hA n)))) ∧
    (∀ (X : Scheme.{u}) (hX : X.IsCharacteristic p) (n : ℕ),
      HPow.hPow (α := End X) (X.iterateFrobenius hp (hX.2 ⊤) 1) n =
        X.iterateFrobenius hp (hX.2 ⊤) n ∧
      (X.iterateFrobenius hp (hX.2 ⊤) n).base = 𝟙 _ ∧
      (∀ (U : X.Opens) (s : Γ(X, U)),
        (X.iterateFrobenius hp (hX.2 ⊤) n).app U s = s ^ p ^ n) ∧
      (∀ (x : X) (s : X.presheaf.stalk x),
        (X.iterateFrobenius hp (hX.2 ⊤) n).stalkMap x s = s ^ p ^ n) ∧
      (∀ U : X.Opens, ∃ hU : (p : Γ(U.toScheme, ⊤)) = 0,
        (X.iterateFrobenius hp (hX.2 ⊤) n).resLE U U le_rfl =
          U.toScheme.iterateFrobenius hp hU n) ∧
      (∀ (U : X.Opens) (A : Type u) [CommRing A]
          (e : U.toScheme ≅ Spec (CommRingCat.of A)),
        ∃ hA : (p : A) = 0,
          (X.iterateFrobenius hp (hX.2 ⊤) n).resLE U U le_rfl ≫ e.hom =
            e.hom ≫ Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime A hp hA n)))) := by
  sorry

end AlgebraicGeometry
