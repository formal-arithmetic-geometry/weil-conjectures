/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.GenericSmoothDomain

/-!
# Ascent of a nonempty regular open for separable fraction fields

Source: Stacks Project, More on Algebra, Tag 07PB, lemma-J-0-goes-up, with J-0 expanded
using Tag 07P7, definition-J; separability is Algebra, Tag 030O
(blueprint: lem-exc-j0-separable-finite-type-ascent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A nonempty regular open ascends along an injective finite type map of domains over a
Noetherian base when the induced fraction-field extension is separable in the sense of
Stacks Tag 030O. The algebra structure in `hsep` is the canonical map on fraction fields,
not an independently chosen field embedding.

Source: Stacks Project, More on Algebra, Tag 07PB, lemma-J-0-goes-up; Tag 07P7,
definition-J (blueprint: lem-exc-j0-separable-finite-type-ascent).

Proof (the six steps of the node):
1. Choose a point p in the given regular open U. Write its closed complement as V(I),
   choose f in I outside p, and obtain a nonzero f with D(f) contained in U
   (`def-weil-affine-spectrum`). Put A = R_f and B = S_image(f).
2. A is Noetherian by `lem-weil-pbc-localization-noetherian`. Its spectrum is D(f) by
   `lem-weil-pbc-principal-localization-open-immersion`. At every prime P of A, its local
   ring identifies with R_p for the contracted prime p in D(f): the fraction maps send
   (r/f^i)/(s/f^j) to r*f^j/(s*f^i) and r/s to (r/1)/(s/1). The denominators avoid the
   corresponding primes, and cross multiplication verifies well-definedness and inverse
   identities (`def-weil-pbc-localization-at-prime`). These local rings are regular by U,
   so A is regular (`def-weil-regular-scheme`).
3. A to B is injective because both embed in Frac(S). The images of finite algebra
   generators of S generate B over A: express a numerator as a polynomial and divide
   each coefficient by the same power of f (`def-weil-pbc-finite-type-algebra`). Their
   fraction fields and induced embedding are unchanged, hence still separable.
4. Apply `lem-exc-generic-smooth-domain` to A to B, obtaining a nonzero h in B such that
   T = B_h is smooth over A. Step 3 supplies all its hypotheses.
5. Apply `lem-weil-pbc-regular-ring-smooth-ascent` to the regular ring A and its smooth
   algebra T. Then T is regular, including all its prime local rings.
6. Write h = s/image(f)^n, with s nonzero, and put a = image(f)*s, which is nonzero.
   The rings T and S_a are canonically isomorphic: in T both image(f) and s are units;
   in S_a their inverses are s/a and image(f)/a. The fraction maps fixing S are inverse.
   Thus Spec(T) identifies with D(a) by
   `lem-weil-pbc-principal-localization-open-immersion`. This open is nonempty because
   it contains the zero prime of S. For q in D(a), the maps
   (x/a^i)/(y/a^j) to x*a^j/(y*a^i) and x/y to (x/1)/(y/1) identify the corresponding
   local ring with S_q. The denominators avoid the primes, and cross multiplication
   verifies the inverse identities (`def-weil-pbc-localization-at-prime`). Regularity
   from step 5 therefore gives the required open of regular local rings.
-/
theorem exists_nonempty_open_regular_of_separable_fractionRing
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra R S] [FiniteType R S]
    (hinj : Function.Injective (algebraMap R S))
    (hsep : @IsSeparableExtension (FractionRing R) (FractionRing S) _ _
      (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra)
    (hregular : ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsRegularLocalRing (Localization.AtPrime p.asIdeal)) :
    ∃ V : Set (PrimeSpectrum S), IsOpen V ∧ V.Nonempty ∧
      ∀ q ∈ V, IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  sorry

end Algebra
