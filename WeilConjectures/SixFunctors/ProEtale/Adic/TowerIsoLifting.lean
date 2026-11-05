/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Lifting local isomorphisms of towers over weakly contractible objects

Let `R` and `G` be towers `ℕᵒᵖ ⥤ Sheaf J A` of sheaves on a site. Suppose that `R₀` and `G₀`
are locally isomorphic, and that every local isomorphism `Rₙ ≅ Gₙ` lifts locally to an
isomorphism `Rₙ₊₁ ≅ Gₙ₊₁` compatible with the transition maps. Then over every weakly
contractible object `W` the towers are isomorphic: `R|_W ≅ G|_W`
(`CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`).

This is the sheaf-theoretic step of the passage from a tower `(Gₙ)` of locally constant
`ℤ/ℓⁿ`-sheaves to the lattice `lim Gₙ`: local trivialisations `Gₙ ≅ (ℤ/ℓⁿ)ʳ` at each finite
level, which a priori are not compatible, become compatible over weakly contractible objects,
where every locally surjective map of sheaves of sets is surjective on sections. The proof
applies this to the sheaves of isomorphisms `Iso(Rₙ, Gₙ)` (`CategoryTheory.isoSheaf`) and to
the sheaves of compatible pairs of isomorphisms at consecutive levels
(`CategoryTheory.isoPairSheaf`), and chooses the lifts recursively.

## Main definitions

- `CategoryTheory.isoSheaf`: the sheaf of types `X ↦ (F|_X ≅ G|_X)`.
- `CategoryTheory.isoPairSheaf`: the sheaf of pairs of isomorphisms `(ψ, φ)`, with
  `ψ : F'|_X ≅ G'|_X` and `φ : F|_X ≅ G|_X` compatible with given maps `F' ⟶ F`, `G' ⟶ G`.

## Main results

- `CategoryTheory.isSheaf_isoPresheaf`: isomorphisms between sheaves glue.
- `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isWeaklyContractible`: towers
  with locally liftable local isomorphisms are isomorphic over weakly contractible objects; and
  `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_limit_of_isWeaklyContractible`
  for their limits.
- `CategoryTheory.GrothendieckTopology.exists_lift_iso_of_descent`: local lifting of
  isomorphisms follows from local triviality, descent of isomorphisms, and local lifting of
  automorphisms of one of the two towers.
- `CategoryTheory.Limits.exists_iso_comp_eq_of_isColimit_cokernelCofork`: descent of
  isomorphisms along cokernels (reduction modulo `ℓⁿ`).
- `CategoryTheory.GrothendieckTopology.nonempty_iso_overPullback_of_isColimit_cokernelCofork`:
  the case of `ℓ`-adic towers, `Xₙ₊₁/ℓⁿ ≅ Xₙ`.
- `AlgebraicGeometry.ProEtale.exists_cover_nonempty_iso_overPullback_limit` and
  `ProEtale.exists_cover_nonempty_iso_overPullback_limit_of_isColimit_cokernelCofork`:
  on the pro-étale site, the limits of such towers are locally isomorphic.
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf of types `X ↦ (F|_X ≅ G|_X)` of isomorphisms between the restrictions of two
sheaves to the slices `Over X`. -/
@[simps obj]
def isoPresheaf (F G : Sheaf J A) : Cᵒᵖ ⥤ Type _ where
  obj X := (J.overPullback A X.unop).obj F ≅ (J.overPullback A X.unop).obj G
  map f := ↾fun e ↦ (J.overMapPullback A f.unop).mapIso e
  map_id X := by
    ext e : 3
    refine Iso.ext ?_
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_id X) e.hom
  map_comp f g := by
    ext e : 3
    refine Iso.ext ?_
    exact ConcreteCategory.congr_hom ((sheafHom' F G).map_comp f g) e.hom

/-- The isomorphisms underlying sections of `isoPresheaf`, as a morphism to `sheafHom'`. -/
@[simps app]
def isoPresheafToSheafHom' (F G : Sheaf J A) : isoPresheaf F G ⟶ sheafHom' F G where
  app _ := ↾fun e ↦ e.hom

variable {F' F G' G : Sheaf J A}

namespace GrothendieckTopology.IsWeaklyContractible

variable {W : C}

end GrothendieckTopology.IsWeaklyContractible

namespace GrothendieckTopology

end GrothendieckTopology

namespace GrothendieckTopology

variable (J) in
/-- Restriction to a slice preserves the limits which exist in the coefficient category: limits
of sheaves are computed on sections. -/
instance preservesLimitsOfShape_overPullback {K : Type*} [Category* K] [HasLimitsOfShape K A]
    (X : C) : PreservesLimitsOfShape K (J.overPullback A X) := by
  have : PreservesLimitsOfShape K (J.overPullback A X ⋙ sheafToPresheaf (J.over X) A) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf J A ⋙ (Functor.whiskeringLeft _ _ A).obj (Over.forget X).op))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf (J.over X) A)

end GrothendieckTopology

namespace GrothendieckTopology

end GrothendieckTopology

namespace Limits

end Limits

namespace GrothendieckTopology

variable [Preadditive A]

end GrothendieckTopology

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.GrothendieckTopology

variable {T : Scheme.{u}} {A : Type u'} [Category.{v'} A]

end AlgebraicGeometry.ProEtale
