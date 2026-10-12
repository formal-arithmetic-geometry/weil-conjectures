/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Finite free stalk lifts on an étale neighbourhood
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), finite generator lifting.
(blueprint: lem-weil-pbc-finite-free-constant-map-etale-factorization). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The finite free étale-local lifting step used by the open factorization theorem.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), finite generator lifting.
(blueprint: lem-weil-pbc-finite-free-constant-map-etale-factorization).

Proof: If n = 0, take the identity etale neighbourhood and the unique zero map.
For n > 0, write the standard basis of Λ^(Fin n).  The definition of the geometric
stalk is a filtered colimit over pointed etale neighbourhoods, so each image under l
is represented by a section of F on one such neighbourhood.  Cofilteredness of pointed
etale neighbourhoods gives one common refinement for the finitely many representatives.
The equality hl says that the two resulting germs in G agree.  Equality in the same
filtered colimit therefore gives a further common refinement on which the equalities
hold as sections.  The finite free universal property assembles these sections into a
Λ-linear map from Λ^(Fin n) to sections of F on that neighbourhood.  The
constant-sheaf/global-sections adjunction, together with the pullback comparison for
the constant sheaf, turns this linear map into β.  Checking on the standard basis gives
β ≫ upperStar(V.hom).map φ = upperStar(V.hom).map α.  The chosen pointed neighbourhood
contains x, so x lies in the range of V.hom.  This argument uses no monicity of φ and
works for the zero ring as well. -/
theorem exists_etale_factorization_of_finite_free_constant_map
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) (n : ℕ)
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin n → Λ)) ⟶ G)
    (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)
    (hl : l ≫ (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map φ =
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map α) :
    ∃ (V : X.Etale) (_hx : x ∈ Set.range V.hom)
      (β : (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Fin n → Λ))) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj F),
      β ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).map α := by sorry

end AlgebraicGeometry.Scheme
