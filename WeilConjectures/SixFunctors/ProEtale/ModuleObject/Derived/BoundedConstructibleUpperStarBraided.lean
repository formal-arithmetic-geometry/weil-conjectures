/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided

/-!
# The derived pullback of bounded constructible complexes is braided

The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` with its monoidal structure
`ProEtale.CondensedRing.monoidal_boundedConstructibleUpperStar` is braided for the Koszul braidings
`ProEtale.CondensedRing.boundedConstructibleBraiding`
(`ProEtale.CondensedRing.boundedConstructibleUpperStar_μ_map_braiding_hom`). It is the
restriction of the corresponding statement on the ambient derived categories
(`ProEtale.CondensedRing.leftDerivedUpperStar_μ_map_braiding_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsEllAdicFinitenessCoefficient ℓ Λ]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

attribute [local instance] boundedConstructibleBraiding

set_option maxHeartbeats 1000000 in
-- the braiding of the full subcategory is unfolded to that of the derived category
/-- The tensor comparison of the derived pullback of bounded constructible complexes is
compatible with the braidings. -/
lemma boundedConstructibleUpperStar_map_braiding_hom_δ (K M : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ f).map (β_ K M).hom ≫
        δ (boundedConstructibleUpperStar Λ ℓ f) M K =
      δ (boundedConstructibleUpperStar Λ ℓ f) K M ≫
        (β_ ((boundedConstructibleUpperStar Λ ℓ f).obj K)
          ((boundedConstructibleUpperStar Λ ℓ f).obj M)).hom := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    δ_boundedConstructibleUpperStar_hom]
  exact leftDerivedUpperStar_map_braiding_hom_comp_tensor Λ f.left K.obj M.obj

/-- **The derived pullback of bounded constructible complexes is braided**:
`μ_{K, M} ≫ Lf^* β_{K, M} = β_{Lf^* K, Lf^* M} ≫ μ_{M, K}`. -/
theorem boundedConstructibleUpperStar_μ_map_braiding_hom (K M : Dᵇc(Y.left)⟦Λ⟧) :
    Functor.LaxMonoidal.μ (boundedConstructibleUpperStar Λ ℓ f) K M ≫
        (boundedConstructibleUpperStar Λ ℓ f).map (β_ K M).hom =
      (β_ ((boundedConstructibleUpperStar Λ ℓ f).obj K)
          ((boundedConstructibleUpperStar Λ ℓ f).obj M)).hom ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar Λ ℓ f) M K :=
  Functor.Monoidal.μ_comp_map_braiding_hom_of_δ _ K M
    (boundedConstructibleUpperStar_map_braiding_hom_δ Λ ℓ f K M)

end AlgebraicGeometry.ProEtale.CondensedRing
