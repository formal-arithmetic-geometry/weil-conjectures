/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization

/-!
# Existence of a local morphism with prescribed affine numerator pullback

Source: ILO, Travaux de Gabber, Exposé VIII, Lemma 3.1.8(i), printed p.99,
with the localization and structure-sheaf conventions of 3.1.2--3.1.6, pp.98--99.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Monoscheme

/-- A homomorphism into global sections extends to a local morphism to the ordinary
monoid spectrum. This asserts existence only; it does not assert rigidity or naturality.

Source: ILO VIII, proof of Lemma 3.1.8(i), p.99, with 3.1.2--3.1.6, pp.98--99
(blueprint: lem-trf-affine-monoscheme-hom-existence).

Proof: For each point t, let q(t) consist of the p whose image has nonunit germ at t.
A product in a commutative monoid is a unit exactly when both factors are units, so
q(t) is a proper prime ideal; the empty ideal is allowed. The unit-germ locus V(a)
is open: represent an inverse germ locally, then shrink until the inverse equation
holds. Hence q is continuous, since the inverse image of D(a) is V(a).
On V(a), local inverses of the image of a agree on overlaps by uniqueness of inverses,
and glue by the sheaf axiom, including when V(a) is empty. Send p/a^n to the restriction
of the image of p times the nth power of that inverse. Injectivity of P into its group
completion makes this well-defined: equality p/a^n = p'/a^n' implies p*a^n' = p'*a^n
in P, and multiplication by the inverse images of the denominator powers gives
equality in the target, without cancelling in that target. The same
inverse uniqueness proves compatibility with every inclusion between principal opens.
The pushforward of the source sheaf is a sheaf; extend the maps from the principal-open
basis by lem-weil-pbc-sheaf-morphism-on-basis. At q(t), the smallest-neighborhood and
unit criterion of lem-trf-monoid-prime-minimal-neighborhood identify the stalk with the
face localization. The stalk map takes p/c to the image germ of p times the inverse
image germ of c. Such a fraction is a unit precisely when p is outside q(t), which by
construction is precisely when its image is a unit. Thus the sheafed-space morphism is
local. At D(1), the whole spectrum, the formula pulls each numerator p back to the
prescribed global section. This proves the claimed existence. -/
theorem exists_local_affine_hom (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P)
    (T : SheafedSpace CommMonCat.{u}) (φ : P →* T.presheaf.obj (op ⊤)) :
    ∃ f : T ⟶ affine P, FineFan.IsLocalMorphism f ∧
      (SheafedSpace.Γ.map f.op).hom.comp (affineSection P) = φ := by
  sorry

end AlgebraicGeometry.Monoscheme
