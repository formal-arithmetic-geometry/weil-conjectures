/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-! # Finite direct image of module-valued curve assertions

Source: Stacks Project, Lemma 0A5D, finite pushforward statements.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
/-- Finite direct image transfers the eight module-valued curve assertions.
Source: Stacks Project, Lemma 0A5D, proof of finite pushforward statements.
(blueprint: b3-finite-pushforward-module-assertions)

Proof: Finite direct image is exact, and the cohomology edge map identifies the
cohomology of F with that of its direct image. The finite geometric-stalk formula
expresses each direct-image stalk as the finite product of source stalks; each
source stalk is a direct factor. Thus primary torsion, invertible torsion orders,
imply the respective source torsion conditions. For constructibility use the
epimorphic counit f^* f_* F → F and constructibility of
quotients of constructible sheaves. This holds for arbitrary coefficient rings.
The edge isomorphism transfers C1. A finite scheme over an affine is affine, giving
C2; the stalk conditions give C3 and C4. A finite scheme over a proper scheme is
proper, giving C5. For C6 and C7 form the cartesian square over the field extension.
Finite base change identifies the inverse image of the direct image with the
direct image on the base changed source, and the edge maps commute with pullback.
The resulting square has horizontal isomorphisms and a bijective source vertical
map by H, so the target vertical map is bijective. Use the stalk condition for C6
and properness for C7. For C8 repeat the square with any open immersion into Y;
its inverse image is open in X. Transport a class through the edge isomorphism,
lift by H.C8 on X, then transport back. Commutativity and injectivity of the edge
isomorphism verify the lift. Empty finite fibres give zero factors throughout. -/
theorem IsCurve.Assertions.of_finite_pushforward_module {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    [IsCurve g] [IsFinite f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (H : IsCurve.Assertions Λ (f ≫ g) F) :
    IsCurve.Assertions Λ g ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  sorry
end AlgebraicGeometry
