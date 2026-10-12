/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-! # Propagation of generic vanishing into a local system -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Generic vanishing of a map into a local system propagates to every geometric stalk.
Source: Stacks Project, Tag 09BG (3), and the etale-local constant-section argument
in Tag 09BH (3) (https://stacks.math.columbia.edu/tag/09BG and
https://stacks.math.columbia.edu/tag/09BH).
(blueprint: lem-weil-pbc-generic-all-stalks).

Proof: Fix a geometric point s and an element a of the stalk of F there. Suppose
its image b in the stalk of G is nonzero. Lift s to a member V of an etale cover
trivializing G. Such a lift exists because the cover is surjective and a nonempty
etale fibre over a separably closed field has a rational point. Pullback identifies
the stalks at the lifted point with those at s. Write the target on V as the
constant sheaf associated to a module M. Its stalk is canonically M, so b corresponds
to an element m different from zero.

Represent a on a pointed etale neighbourhood W of the lifted point. Equality of
its image germ with the germ of the constant section m is witnessed on a further
pointed neighbourhood, by the filtered-colimit description of stalks. Replace W by
this refinement; its image section in the constant target is now constantly m.
The composite W to X is etale, so its image is open. W is nonempty because it has
the chosen geometric point. The generic point eta lies in every nonempty open of X,
so there is a point w of W over eta. Compose the geometric point obtained from an
algebraic closure of the residue field at w with W to X. This gives a geometric
point t of X over eta, in the same universe as X.

At this new pointed neighbourhood, the image of the representing section has germ m,
which is nonzero by the constant-sheaf stalk formula and compatibility of stalks
with pullback. But hφ makes the map at t zero, a contradiction. Thus every a maps
to zero at every s, and extensionality of module homomorphisms proves the conclusion.
This is automatic for a zero source, target, or coefficient ring. The hypotheses
exclude the empty scheme. The argument uses neither finite generation nor any
Noetherian hypothesis. -/
theorem all_sheafFiber_map_eq_zero_of_generic
    {X : Scheme.{u}} [IrreducibleSpace X] {Λ : Type (u + 1)} [CommRing Λ]
    (η : X) (hη : IsGenericPoint η Set.univ)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    [IsLocallyConstantSheaf G] (φ : F ⟶ G)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s (IsLocalRing.closedPoint Ω) = η →
        (pointSmallEtale s).sheafFiber.map φ = 0) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      (pointSmallEtale s).sheafFiber.map φ = 0 := by sorry

end AlgebraicGeometry.Scheme
