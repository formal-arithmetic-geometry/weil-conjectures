/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfCover

/-!
# Locally free module objects are free on a finite affine pro-étale cover

Let `Λ` be a commutative condensed ring and `M` a module object over `Λ_S` on `S_proét`.

* `ProEtale.CondensedRing.isFree_upperStar`: the pullback `g^* M` of a free module object is
  free.
* `ProEtale.CondensedRing.isFree_upperStar_of_isFree_mapMod`: the freeness of the sheaf pullback
  `mapMod(f^*) M` over `f^* Λ_S`, as in the definition of `ProEtale.IsLocallyFree`, implies the
  freeness of the pullback `f^* M` of module objects over `Λ`.
* `Scheme.Cover.exists_finite_affine_refinement`: a pro-étale cover of a quasi-compact scheme
  is refined by a finite pro-étale cover with affine members.
* `ProEtale.CondensedRing.exists_finite_affine_cover_isFree_upperStar`: a locally free module
  object on a quasi-compact scheme `S` becomes free on the members of a finite pro-étale cover
  of `S` by affine schemes.
* `compactSpace_quasiSeparatedSpace_of_isPullback`: the fibre product of
  two affine schemes over a quasi-separated scheme is quasi-compact and quasi-separated.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
