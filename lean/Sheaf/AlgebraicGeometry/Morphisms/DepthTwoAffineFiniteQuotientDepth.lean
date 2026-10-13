/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-! # Positive depth of finite quotients of restriction sections

Source: Stacks Project, Tags 0AV8, 0AVN, 05AM, 00LL and 00LX.
(blueprint: lem-sbc-depth-two-affine-finite-quotient-depth)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Every finite intermediate extension has a quotient of positive local depth.

Source: Stacks Project, surjectivity argument of Tag 0AV8, as used in 0E9I;
Tags 0AVN, 05AM, 00LL and 00LX.
(blueprint: lem-sbc-depth-two-affine-finite-quotient-depth)

Proof: On the Noetherian affine V, quasi-coherence identifies N with the sheaf
of M = N(V). The open immersion U intersect V into V is quasi-compact and
quasi-separated, hence its direct image is quasi-coherent with section module P.
The injective unit embeds M in P and is an isomorphism over U intersect V.
For each prime p of R, the affine stalk comparison identifies R_p with the
local ring at the corresponding point and M_p with the stalk of N. These
comparisons transport the assumed depth bound and the unit map.
Tag 0AVN excludes weakly associated points of P on the complement, hence also
associated points by 05AM. Associated primes of a submodule S of P are among
those of P. Since S contains M, its restriction over U intersect V equals M.
Thus Q = S/M vanishes there. At a boundary prime, if S localized is nonzero,
its maximal ideal is not associated, so 00LL gives depth at least one. If M
localized is nonzero, 00LX and depth(M) at least two give depth(Q) at least one
when Q is nonzero. If M localized is zero, Q equals S localized and has the
same positive depth. If S localized is zero, Q is zero. The zero quotient has
infinite depth by the definition. Finiteness of S and its quotient gives finite
localizations. These cases cover every prime, including the empty open U and
zero source module. No vanishing or surjectivity conclusion is assumed here. -/
theorem depth_one_affine_finite_quotient_of_depth_two
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
    (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG)
    (hMS : LinearMap.range
      (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom ≤ S)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime] :
    ∃ hfinite : Module.Finite (Localization.AtPrime p)
      (LocalizedModule.AtPrime p
        (S ⧸ (LinearMap.range
          (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
            S.subtype)),
      letI := hfinite
      (1 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
        (LocalizedModule.AtPrime p
          (S ⧸ (LinearMap.range
            (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
              S.subtype)) := by sorry

end AlgebraicGeometry.Scheme
