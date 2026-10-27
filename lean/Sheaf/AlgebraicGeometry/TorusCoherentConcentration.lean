/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.TorusCoherentLocalizationData
public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EquivariantRegularSelfIntersection

/-! # Integral torus concentration for coherent classes

Source: the agent-supplied concentration prerequisite for Milne, Algebraic Groups,
Section 22d, proof of Theorem 22.50, p.480.
(blueprint: lem-sfb-torus-coherent-concentration)

Milne cites a numerical fixed-point theorem; concentration itself is a supporting
statement here, not a theorem attributed to that page. The integral groups and
ordinary closed pushforward are used, with no rationalization or dense cyclic point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.EquivariantCoherent

/-- Closed pushforward from the represented fixed subscheme is an isomorphism after
inverting all nonzero-character Euler factors. This includes every characteristic,
the empty fixed scheme, and rank zero.

Source: the agent-supplied concentration prerequisite for Milne, Algebraic Groups,
Section 22d, proof of Theorem 22.50, p.480
(blueprint: lem-sfb-torus-coherent-concentration).

Proof:
1. Projective implies proper (lem-pc-projective-proper), hence separated and finite
   type (def-weil-proper-morphism). The represented fixed scheme W and its open
   complement U are invariant. Apply lem-sfb-equivariant-coherent-localization-sequence
   to obtain ker(j*) = im(i*). The character map to R(T), defined by the one-dimensional
   coaction v to v tensor chi, preserves tensor multiplication. Thus these maps are
   linear for exactly the character twists specified here.
2. Given b/s in localized G-zero(Y), apply
   lem-sfb-torus-nonfixed-complement-annihilation to j*(b). Some t in Sigma kills
   this restriction, so exactness supplies a with i*(a) = tb. Then a/(ts) maps to b/s.
   This proves surjectivity, including the case of empty W, using only integral
   localization fractions.
3. By lem-sfb-torus-fixed-euler-unit, i is regular near W with uniformly bounded
   regular-sequence lengths, and the alternating conormal exterior tensor operator
   L is invertible after localization. This uses its geometric hypotheses on the
   smooth projective Y, without applying an affine theorem to Y itself.
4. Apply lem-sfb-equivariant-regular-self-intersection. Its Gysin map and identity
   i! i* = L are R(T)-linear and hence character-ring linear. They extend to the
   localization. If i*(beta) = 0, then L(beta) = 0; invertibility gives beta = 0.
   This proves injectivity and therefore the asserted localized module isomorphism.
5. In rank zero the fixed functor is all of Y, the character group is zero, and
   Sigma is {1}; the map is the identity. The coherent Grothendieck group of the
   empty scheme is zero, so empty Y or W is included. Every relation and operator
   is integral, with no division depending on the characteristic and no choice of
   a torus point having dense cyclic subgroup. -/
theorem torus_coherent_concentration (F : Type u) [Field F] [IsAlgClosed F]
    (T : Grp (Over (Spec (.of F))))
    [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]
    (r : ℕ) (split : T ≅ MultiplicativeType.splitTorus F r)
    (Y : Over (Spec (.of F))) [ModObj T.X Y] [Smooth Y.hom] [IsProjective Y.hom]
    (W : Over (Spec (.of F))) [ModObj T.X W]
    (i : W ⟶ Y) [IsClosedImmersion i.left] [IsModHom T.X i]
    (hfixed : ∀ (A : CommAlgCat.{u} F)
      (y : (algSpec (.of F)).obj (op A) ⟶ Y),
      (∃ w : (algSpec (.of F)).obj (op A) ⟶ W, w ≫ i = y) ↔
        ∀ (B : CommAlgCat.{u} F) (f : A ⟶ B)
          (t : (algSpec (.of F)).obj (op B) ⟶ T.X),
          t • ((algSpec (.of F)).map f.op ≫ y) = (algSpec (.of F)).map f.op ≫ y) :
    ∃ (DY : ActionGroupoidModel T.X Y) (DW : ActionGroupoidModel T.X W)
      (mY : TorusLocalization.CharacterAction DY) (mW : TorusLocalization.CharacterAction DW),
      TorusLocalization.IsLocalizedClosedPushforwardIso DY DW i mY mW := by
  sorry

end AlgebraicGeometry.EquivariantCoherent
