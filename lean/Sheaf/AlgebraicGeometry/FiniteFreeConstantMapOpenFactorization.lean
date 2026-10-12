/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Extending a stalk factorization of a finite constant map

Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A stalk factorization from a finite free constant module extends to an open.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent.
(blueprint: lem-weil-pbc-finite-free-constant-map-open-factorization).

Proof: For each standard basis vector, represent its image under l by a section of F
on a pointed etale neighbourhood. Refine finitely many times so that all representatives
are on one neighbourhood V and their images under phi equal the corresponding images
under alpha. Equality of germs is witnessed after refinement. The open image U of V
contains x. On V times_U V the two pulled back representatives have equal images in G,
since both images come from alpha. Monicity makes them equal in F. Descent for the
surjective etale cover V to U gives one section of F on U for each basis vector.
The universal property of the free module gives a linear map from Λ^(Fin n) into
these global sections. The constant-sheaf/global-sections adjunction and the constant
pullback comparison give the desired map. Equality of its composite with phi and alpha
is checked on the standard basis. For n=0 both maps from the zero constant sheaf are
zero, and U=X suffices. No relations have to be checked in this free-module statement. -/
theorem exists_open_factorization_of_finite_free_constant_map
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] (n : ℕ)
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin n → Λ)) ⟶ G)
    (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)
    (hl : l ≫ (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map φ =
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map α) :
    ∃ (U : X.Opens) (_hU : x ∈ U)
      (ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F),
      ψ ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map α := by sorry

end AlgebraicGeometry.Scheme
