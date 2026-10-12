/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Closed support of a proper coherent pushforward

Source: Stacks Project, Theorem 088E, support of H paragraph, and Proposition 02O5.
The assertion isolates closedness and containment; properness over a further base
is proved separately in `ChowAlgebraizationSupport`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The support of a pushforward is closed and is contained in the image of the support.
Source: Stacks Project, Tag 088E, support paragraph (the closedness and stalk argument).
(blueprint: new-chow-pushforward-support-closed)

Proof: A proper morphism to the Noetherian Z is of finite type, hence Y is
Noetherian too. Tag 02O5 implies that q_*F is coherent. On a Noetherian scheme,
a coherent module is quasi-coherent of finite type (Tag 01XZ), so its support is
closed (Tag 056J). Give that support its closed-set structure D.
Because q is proper it is a closed map; thus q(C) is closed. For x outside q(C),
the open neighbourhood V = Z \ q(C) has inverse image disjoint from C. Every
stalk of F on q^{-1}(V) is zero by hC. Given two sections over any open inside
q^{-1}(V), equality of their germs supplies a neighbourhood of each point on
which they agree. Sheaf separatedness then makes the sections equal, including
on the empty open. Therefore q_*F has only one section over every open inside V.
Every germ at x is represented on an open neighbourhood; intersect that open
with V to conclude that the stalk of q_*F at x is zero. Taking the contrapositive
gives D ⊆ q(C). The construction also covers F = 0 and empty Y or Z.
-/
theorem pushforward_support_closed_subset
    {Z Y : Scheme.{u}} [IsNoetherian Z]
    (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y)
    (C : TopologicalSpace.Closeds Y)
    (hC : (C : Set Y) = {x : Y | ¬ Subsingleton (F.obj.presheaf.stalk x)}) :
    ∃ D : TopologicalSpace.Closeds Z,
      (D : Set Z) =
        {x : Z | ¬ Subsingleton (((Scheme.Modules.pushforward q).obj F.obj).presheaf.stalk x)} ∧
      (D : Set Z) ⊆ q '' (C : Set Y) := by
  sorry

end AlgebraicGeometry
