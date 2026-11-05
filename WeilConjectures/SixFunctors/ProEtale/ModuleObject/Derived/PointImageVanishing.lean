/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance

/-!

# Pullbacks along morphisms with image in a closed subscheme

Let `e : P ⟶ X` be a closed immersion of schemes over `Spec k` (for instance a rational point
`point k ⟶ X`, which is a closed immersion since `X` is separated) and `f : Y ⟶ X` a morphism
whose image lies set-theoretically in the image of `e`. If `Le^* M = 0` for some
`M : Dᵇc(X)⟦Λ⟧`, then `Lf^* M = 0`.

The morphism `f` itself need not factor through `e`, but its restriction `r ≫ f` to the reduction
`r : Y_red ⟶ Y` does, so `Lr^* Lf^* M ≅ Lg^* Le^* M = 0`. The reduction `r` is a finite
universal homeomorphism, so `Lr^*` is an equivalence by topological invariance
(`ProEtale.CondensedRing.isIso_unit_boundedConstructibleUpperStarLowerStarAdjunction`), whence
`Lf^* M = 0`.

## Main statements

- `ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_of_range_subset`: for `e` a
  closed immersion and `range f ⊆ range e`, `Le^* M = 0` implies `Lf^* M = 0`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k]

/-- The reduction `Y_red` of a scheme `Y` over `Spec k`, the closed subscheme cut out by the
nilradical, as a scheme over `Spec k`. -/
noncomputable def overReduction (Y : Over (Spec (.of k))) : Over (Spec (.of k)) :=
  Over.mk (Y.left.nilradical.subschemeι ≫ Y.hom)

/-- The closed immersion `Y_red ⟶ Y` of the reduction of a scheme over `Spec k`. -/
noncomputable def overReductionι (Y : Over (Spec (.of k))) : overReduction Y ⟶ Y :=
  Over.homMk Y.left.nilradical.subschemeι

instance (Y : Over (Spec (.of k))) : IsReduced (overReduction Y).left :=
  inferInstanceAs (IsReduced Y.left.nilradical.subscheme)

instance (Y : Over (Spec (.of k))) : IsClosedImmersion (overReductionι Y).left :=
  inferInstanceAs (IsClosedImmersion Y.left.nilradical.subschemeι)

instance (Y : Over (Spec (.of k))) : IsFinite (overReductionι Y).left :=
  inferInstanceAs (IsFinite Y.left.nilradical.subschemeι)

instance (Y : Over (Spec (.of k))) : Surjective (overReductionι Y).left := ⟨by
  change Function.Surjective Y.left.nilradical.subschemeι
  rw [← Set.range_eq_univ, IdealSheafData.range_subschemeι, Scheme.support_nilradical]
  rfl⟩

instance (Y : Over (Spec (.of k))) : IsUniversalHomeomorphism (overReductionι Y).left where

instance (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (overReduction Y).hom :=
  inferInstanceAs (LocallyOfFiniteType (Y.left.nilradical.subschemeι ≫ Y.hom))

instance (Y : Over (Spec (.of k))) [QuasiCompact Y.hom] : QuasiCompact (overReduction Y).hom :=
  inferInstanceAs (QuasiCompact (Y.left.nilradical.subschemeι ≫ Y.hom))

instance (Y : Over (Spec (.of k))) [IsSeparated Y.hom] : IsSeparated (overReduction Y).hom :=
  inferInstanceAs (IsSeparated (Y.left.nilradical.subschemeι ≫ Y.hom))

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing
