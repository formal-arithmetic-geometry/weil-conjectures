/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons

/-! # Coefficient compatibility of the derived étale exchange morphism -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The canonical inverse- and direct-image coefficient comparisons intertwine the
derived exchange morphisms. The endpoint comparisons are already constructed as
isomorphisms; this theorem asserts only the compatibility of the morphisms.

Source: Stacks Project, Remark 21.19.3, Tag 07A7, and Lemma 21.20.7(3), Tag 0D6J.
Proof: direct image and coextension of coefficients commute sectionwise. The
inverse-image coefficient isomorphism is the uniqueness isomorphism between the
two left adjoints of this composite, so it respects their units and counits. The
direct-image coefficient comparison is the unique morphism compatible with the
right-derived units. These characterizations show that the two composites in the
assertion have the same adjoint: apply inverse image along h, use the equality of
the two composite inverse images coming from the commutative square, and then
apply the inverse image along e of the counit for g. This is exactly the mate
construction in 07A7. The coefficient comparisons commute with each operation:
composition by uniqueness of adjoints and derived functors, and the counit by
the unit/counit identities of the uniqueness isomorphism. Equality of adjoints
gives the asserted equality. One may check the right-derived comparison identities
on bounded below injective resolutions; their restricted complexes are acyclic
for direct image, so their derived units are invertible. No base-change
isomorphism assertion, smoothness, or torsion hypothesis enters this argument.
(blueprint: lem-sbc-restrict-scalars-derived-exchange) -/
theorem derivedBaseChange_restrictScalars_exchange
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : IsPullback e h g p)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedBaseChangeSourceRestrictScalarsIso φ p g K).hom ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.map
          ((baseChange (ModuleCat.{u + 1} Λ') sq.toCommSq).app K) =
      (baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K) ≫
        (derivedBaseChangeTargetRestrictScalarsIso φ e h K).hom := by sorry

end AlgebraicGeometry.Etale
