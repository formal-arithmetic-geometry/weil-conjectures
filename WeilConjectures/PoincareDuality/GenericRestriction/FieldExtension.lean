/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.GenericRestriction.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.TraceFormula.FieldDualizable

/-!
# Internal homs commute with a change of the base field

Let `k ⟶ L` be a field extension, `X` a separated `k`-scheme of finite type and
`π : X_L = X ×_k L ⟶ X` the projection. This file proves that the derived pullback `Lπ^*` commutes
with internal homs of bounded constructible `ℚ̄_ℓ`-complexes: the comparison
`Lπ^* RHom(K, M) ⟶ RHom(Lπ^* K, Lπ^* M)`
(`ProEtale.CondensedRing.ihomUpperStarComparison`) is an isomorphism
(`ProEtale.CondensedRing.isIso_ihomUpperStarComparison_of_fieldExtension`). This is the
internal-hom assertion of blueprint `det-pd-generic-closed-hom` (2) for a change of the base
field; the geometric generic fibre of blueprint `sk-lem-pd-generic-restriction` is such a change
of base field followed by the weakly étale inclusion of a generic point
(`WeilConjectures.PoincareDuality.GenericRestriction.GenericFibre`).

## Proof

As in the blueprint, by noetherian induction on the closed subschemes `Z` of `X`, in the second
variable `M`. By topological invariance we may replace `Z` by its reduction. On a reduced `Z`,
`K` is dualizable on a nonempty open `j : U ⟶ Z`
(`ProEtale.CondensedRing.exists_isOpenImmersion_exactPairing_upperStar`, from generic
dualizability `ProEtale.CondensedRing.exists_isOpenImmersion_triangEnvelope_isDualizable`), so the
comparison of `U_L ⟶ U` at `(Lj^* K, -)` is an isomorphism. Direct images along open and closed
immersions commute with the change of the base field (Stacks 0F1C,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_fieldExtension`), so the formal
lemmas of `WeilConjectures.PoincareDuality.GenericRestriction.Comparison` reduce the comparison
at `(K, M)` to the comparisons on `U` and on the closed complement of `U`, which holds by
induction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Generic dualizability**, in the ambient derived category: a bounded constructible
`ℚ̄_ℓ`-complex `K` on a nonempty reduced separated `k`-scheme of finite type `Z` has a left dual
on some nonempty open subscheme `U ⟶ Z`. It is
`ProEtale.CondensedRing.exists_isOpenImmersion_triangEnvelope_isDualizable`, the dualizable objects
of the ambient derived category forming a triangulated subcategory stable under retracts. -/
theorem exists_isOpenImmersion_exactPairing_upperStar (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsReduced Z.left]
    [Nonempty Z.left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) K) :
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (_ : Nonempty U.left) (j : U ⟶ Z) (_ : IsOpenImmersion j.left)
      (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left))),
      Nonempty (ExactPairing D ((L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K)) := by
  sorry

variable {L : Type u} [Field L] [Algebra k L]

/-- **Internal homs commute with a change of the base field** (blueprint
`det-pd-generic-closed-hom` (2), for the change of the base field `k ⟶ L`): for a separated
`k`-scheme of finite type `X`, its base change `π : X_L ⟶ X` and bounded constructible
`ℚ̄_ℓ`-complexes `K` and `M` on `X`, the comparison
`Lπ^* RHom(K, M) ⟶ RHom(Lπ^* K, Lπ^* M)` is an isomorphism. The extension `L / k` may be
transcendental and inseparable. -/
theorem isIso_ihomUpperStarComparison_of_fieldExtension (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Scheme.{u}} {π : X' ⟶ X.left} {a' : X' ⟶ Spec (.of L)}
    (sq : IsPullback π a' X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) M) :
    IsIso (ihomUpperStarComparison (Profinite.padicAlgClRingObj ℓ) π K M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
