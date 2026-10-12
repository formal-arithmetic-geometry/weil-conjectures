/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-! # Generic generation in a submodule of a finite constant module sheaf -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Generic generators of a submodule of a finite constant sheaf extend to a finite
locally constant subsystem on an open neighbourhood of the generic point.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent
on the irreducible constant base, before the final equality of sheaves.
(blueprint: lem-weil-pbc-noetherian-constant-subsheaf-generic).

Proof: Write G as the constant sheaf with value M. Its geometric stalk at the generic
point is M, so M is a finitely generated module by finiteness of G. Exactness of geometric
stalks identifies the generic stalk of F with a submodule N of M. Since the coefficient
ring is Noetherian, N has finitely many generators. Represent them on one common pointed
étale neighbourhood and refine until their images are their constant sections in M.
On the fibre product the two lifts coincide, because their images in G coincide and
F embeds into G. Sheaf descent therefore makes them sections over the open image of
that neighbourhood. Every relation between the generators vanishes in F because it
vanishes in M. Hence they define a morphism from the constant N sheaf to F there.
Its composite into constant M is the constant inclusion N into M, which is mono:
constant presheaves and sheafification preserve monomorphisms. Thus the morphism into F
is mono. The constant N sheaf is finite locally constant since N is finitely generated.
Its map on the chosen generic stalk is surjective by construction. The stalks at
separably closed extensions of the generic residue field are identified by compatible
separable closures. Those identifications commute with the maps into constant M, so
surjectivity holds at every geometric point above the generic point. For N = 0 use the
zero constant sheaf and the empty list of generators. No equality with F away from the
generic point is asserted; neither X nor the underlying set of M must be Noetherian. -/
theorem exists_open_generic_generating_subsheaf_of_mono_constant
    {X : Scheme.{u}} [IrreducibleSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsFiniteSheaf G]
    (hG : G.IsConstant X.smallEtaleTopology)
    (η : X) (hη : IsGenericPoint η Set.univ) :
    ∃ (U : X.Opens) (_hU : η ∈ U),
      ∃ (H : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (ψ : H ⟶ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F),
        Mono ψ ∧ IsFiniteLocallyConstantSheaf H ∧
        ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.toScheme),
          s (IsLocalRing.closedPoint Ω) = (⟨η, _hU⟩ : U.toScheme) →
          Epi ((pointSmallEtale s).sheafFiber.map ψ) := by sorry

end AlgebraicGeometry.Scheme
