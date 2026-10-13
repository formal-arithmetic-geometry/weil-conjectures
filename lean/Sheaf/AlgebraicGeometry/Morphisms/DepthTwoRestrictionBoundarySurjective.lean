/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-! # Existence of boundary germ extensions in depth two

Source: Stacks Project, Tags 0AV8 and 0AVN, as used in Tag 0E9I.
(blueprint: lem-sbc-depth-two-restriction-boundary-surjective)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Boundary germs of the direct image lift across a depth-two boundary.

Source: Stacks Project, proof of Tag 0E9I, with Tags 0AV8, 0AVN and 05AM.
(blueprint: lem-sbc-depth-two-restriction-boundary-surjective)

Proof: Work on a Noetherian affine neighbourhood of y. The source is the sheaf of
its finite section module M; hence it is coherent. The open immersion restricted
to this neighbourhood is quasi-compact and quasi-separated, so its direct image
is quasi-coherent; write P for its section module. By the injectivity hypothesis
we regard M as a submodule of P. Away from U, P has no associated prime by 0AVN
(and Ass is contained in WeakAss by 05AM). The map is already an isomorphism
on U. For any finite submodule P' of P containing M, the same assertions hold:
its associated primes are among those of P, and its localization on U equals M.
In the exact sequence 0 -> M -> P' -> Q -> 0, at boundary points the depth lemma
and depth(M) >= 2, depth(P') >= 1 give depth(Q) >= 1 whenever Q is nonzero.
On U the quotient is zero. Thus Q has no associated primes and is zero.
Every element of P lies in such a finite P' (adjoin it to generators of M), so
M -> P is surjective. Localize to y to obtain the asserted lift of every germ.
This is the surjectivity argument of 0AV8 applied to the direct image; injectivity
is a separate hypothesis here. The zero module is allowed. For an empty boundary
there is no y; for U empty the target is zero and the assertion is automatic. -/
theorem surjective_restrictAdjunction_unit_stalk_of_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) 
    (hinj : ∀ V : L.Opens,
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app V))
    (y : L) (hy : y ∉ U) :
    Function.Surjective ((stalkFunctor Ab.{u} y).map
      ((Modules.toPresheaf L).map ((Modules.restrictAdjunction U.ι).unit.app N))) := by sorry

end AlgebraicGeometry.Scheme
