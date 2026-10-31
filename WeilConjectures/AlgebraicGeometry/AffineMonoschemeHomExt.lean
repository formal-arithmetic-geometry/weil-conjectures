/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MonoschemeToricRealization

/-!
# Rigidity of local morphisms to an ordinary affine monoid spectrum

Source: ILO, Travaux de Gabber, Exposé VIII, Lemma 3.1.8(i), printed p.99,
with 3.1.2--3.1.6, pp.98--99.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Monoscheme

/-- Local morphisms to the ordinary affine spectrum agree if their pullbacks agree on
canonical global numerators. There is no assertion that a morphism exists for arbitrary
section data. The source stalks may contain nontrivial units and need not be integral.

Source: ILO VIII, uniqueness in Lemma 3.1.8(i), p.99, with 3.1.2--3.1.6, pp.98--99
(blueprint: lem-trf-affine-monoscheme-hom-ext).

Proof: Fix t in the source. The minimal-neighborhood lemma identifies the stalk at a
prime q with P localized at its complementary face, and a numerator p is a unit there
exactly when p is outside q. Pullback commutes with taking germs of global sections.
Locality therefore implies that p is outside the image prime of either morphism if
and only if its common pulled-back section has a unit germ at t. Thus the image primes
are equal for every t, and the continuous maps are equal.
Identify these continuous maps. Over D(a), pullback of a numerator p is the restriction
of its global pullback, by naturality of the sheaf map. The image of the inverse of a
is forced, since a monoid homomorphism preserves inverses of units. Every section on
D(a) is a fraction in P[a^-1], so the two section homomorphisms agree on D(a).
Clause (a) of lem-weil-pbc-sheaf-morphism-on-basis says that morphisms into the pushforward
source sheaf which agree on this principal-open basis agree everywhere. Consequently
the two sheaf maps, and hence the two sheafed-space morphisms, coincide. For an empty
source, equality on the base is vacuous and the same basis argument still applies.
No step cancels in a source stalk or identifies units with the identity. -/
theorem local_affine_hom_ext (P : Type u) [CommMonoid P] (hP : FineFan.IsFine P)
    (T : SheafedSpace CommMonCat.{u}) (f g : T ⟶ affine P)
    (hf : FineFan.IsLocalMorphism f) (hg : FineFan.IsLocalMorphism g)
    (h : (SheafedSpace.Γ.map f.op).hom.comp (affineSection P) =
      (SheafedSpace.Γ.map g.op).hom.comp (affineSection P)) : f = g := by
  sorry

end AlgebraicGeometry.Monoscheme
