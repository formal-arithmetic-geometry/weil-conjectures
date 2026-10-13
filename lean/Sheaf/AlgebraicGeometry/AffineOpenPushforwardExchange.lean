/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Ordinary exchange is invertible on a quasi-coherent affine-open direct image.
Source: Stacks Project, Tag 02KG; the affine-intersection argument of
`lem-pc-affine-alternating-cech-pinned-mate`.
(blueprint: lem-pc-s3-affine-open-pushforward-exchange).
Proof: Write j for W.ι and form its pullback j' along p = pullback.fst f g.
Since X is separated over the affine scheme Spec A, X is separated and j is affine.
The composite j ≫ f is affine because both its source and target are affine.
The restriction G|W is quasi-coherent. The square for j and p and the outer square
for j ≫ f and g are cartesian, so affinePushforward_baseChange makes their exchange
maps invertible. Vertical pasting of ordinary exchange, proved by transposing under
the tensor-pullback adjunction for g, expresses the outer map (up to pushforward
composition isomorphisms) as the exchange for f on j_*G|W followed by f'_* of
exchange for j. Pushforward preserves the latter isomorphism. Cancel it and the
composition isomorphisms to obtain the assertion. This uses no derived category,
complex, finite-product identification, or localization. -/
theorem affineOpen_pushforward_exchange
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (W : X.Opens) (hW : IsAffineOpen W) :
    IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.snd f g) g
      (pullback.fst f g) pullback.condition
      ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι))) := by sorry

end AlgebraicGeometry
