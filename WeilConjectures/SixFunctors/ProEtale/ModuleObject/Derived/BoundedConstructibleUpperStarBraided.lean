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

The derived pullback `Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` is compatible with the Koszul braidings
`ProEtale.CondensedRing.boundedConstructibleBraiding`
(`ProEtale.CondensedRing.boundedConstructibleUpperStar_δ_braiding`): both its tensor comparison and
the braidings are restricted from the ambient derived categories, where this is
`ProEtale.CondensedRing.leftDerivedUpperStarTensor_braiding`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsEllAdicFinitenessCoefficient ℓ Λ]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

attribute [local instance] boundedConstructibleBraiding

/-- **The derived pullback on bounded constructible complexes is braided**: its tensor comparison
is compatible with the Koszul braidings. -/
@[reassoc]
lemma boundedConstructibleUpperStar_δ_braiding (f : X ⟶ Y) (K M : Dᵇc(Y.left)⟦Λ⟧) :
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) K M ≫
        (β_ ((boundedConstructibleUpperStar Λ ℓ f).obj K)
          ((boundedConstructibleUpperStar Λ ℓ f).obj M)).hom =
      (boundedConstructibleUpperStar Λ ℓ f).map (β_ K M).hom ≫
        Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) M K := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleUpperStar_map_hom,
    δ_boundedConstructibleUpperStar_hom]
  exact leftDerivedUpperStarTensor_braiding Λ f.left K.obj M.obj

end AlgebraicGeometry.ProEtale.CondensedRing
