/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.Frobenius

/-! # Scalar-p isogenies and relative Frobenius

Source: Milne, Algebraic Groups (2017), 2.25--2.29 and 23.25--23.26
(blueprint: lem-sfb-scalar-p-isogeny-relative-frobenius).

The twist is the actual pullback along Spec of the field Frobenius, with its
base-changed group law. The factorization is specified by the absolute-Frobenius
characterization of its composite with the projection back to G. Since the map
also lies over the identity of Spec F, the pullback universal property identifies
it uniquely with relative Frobenius. On coordinates this is b ⊗ c ↦ c b^p.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- An isogeny scalar p on maximal-torus characters is relative Frobenius followed
by a group-scheme isomorphism. The conclusion writes the factorization equivalently
as: f followed by h inverse is the unique map to the Frobenius pullback whose
projection to G is absolute Frobenius. Its other projection is already the structure
map, because f and h are morphisms over F.

Source: Milne, Algebraic Groups (2017), 2.25--2.29 and 23.25--23.26
(blueprint: lem-sfb-scalar-p-isogeny-relative-frobenius).

Proof plan:
1. Apply lem-sfb-reductive-frobenius-twist. The actual Frobenius twist is split
   reductive, the base-changed torus is maximal, and base change identifies its full
   root datum with that of G. Relative Frobenius is an isogeny inducing p times
   this identification on characters.
2. Apply lem-sfb-root-datum-isogeny-realization to this identification, choosing
   every root exponent equal to one. Both root and coroot equations hold, and
   the isomorphism criterion gives g : G^(p) ≅ G inducing that identification.
3. Both g after relative Frobenius and f are isogenies preserving T and induce
   multiplication by p on every character. By lem-sfb-isogeny-torus-conjugacy
   they differ by conjugation by a point t in T(F).
4. Compose g with that inner automorphism to obtain h. Its inverse is g inverse
   after conjugation by t inverse. Thus f followed by h inverse is the relative
   Frobenius, whose projection is absolute Frobenius as asserted. Empty root
   systems and rank-zero tori require no change to the argument. -/
theorem scalarPIsogeny_relativeFrobenius {F : Type u} [Field F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (G T : Grp (Over (Spec (.of F)))) (i : T ⟶ G)
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (f : G ⟶ G) [Surjective f.hom.hom.left]
    [IsFinite (GrpObj.ker f.hom.hom).hom]
    (fT : T ⟶ T) (hfT : fT ≫ i = i ≫ f)
    (hscalar : ∀ χ : T.X ⟶ StandardGroupSchemes.multiplicative F,
      IsMonHom χ → fT.hom.hom ≫ χ = χ ^ p) :
    ∃ h : ((Over.pullback (Spec.map (CommRingCat.ofHom (frobenius F p)))).mapGrp.obj G) ≅ G,
      ((f ≫ h.inv).hom.hom.left ≫
        pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (frobenius F p)))).IsFrobenius p := by
  sorry

end AlgebraicGeometry
