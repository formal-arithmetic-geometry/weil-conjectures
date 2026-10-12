/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AssertionsTransfer

/-!
# The curve assertions only depend on the underlying abelian sheaf

The eight curve assertions `C(X, F)` (`AlgebraicGeometry.IsCurve.Assertions`) for a sheaf `F`
of `Λ`-modules are statements about the underlying abelian sheaf of `F` and its geometric
stalks. Hence they transfer between sheaves of modules over different coefficient rings whose
underlying abelian sheaves are isomorphic.

## Main statements

- `AlgebraicGeometry.Scheme.sheafFiberAddEquivOfForgetIso`: the additive equivalence of
  geometric stalks induced by an isomorphism of underlying abelian sheaves.
- `AlgebraicGeometry.IsCurve.assertions_of_underlying_abelian_iso`: the transfer of the
  eight assertions.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

variable {Λ R : Type (u + 1)} [CommRing Λ] [CommRing R] {X : Scheme.{u}}
  {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
  {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}

/-- An isomorphism between the underlying abelian sheaves of a sheaf `F` of `Λ`-modules and a
sheaf `G` of `R`-modules induces an additive equivalence between the geometric stalks of `F`
and `G`: taking stalks commutes with forgetting the module structure. -/
noncomputable def sheafFiberAddEquivOfForgetIso
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ↥((pointSmallEtale s).sheafFiber.obj F) ≃+ ↥((pointSmallEtale s).sheafFiber.obj G) :=
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  (((pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso e ≪≫
    ((pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).app G |>.addCommGroupIsoToAddEquiv

/-- Primary torsion only depends on the underlying abelian sheaf. -/
lemma IsPrimaryTorsionSheaf.of_forgetIso
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G) {p : ℕ}
    (hG : IsPrimaryTorsionSheaf R G p) : IsPrimaryTorsionSheaf Λ F p := fun Ω _ _ s x ↦ by
  obtain ⟨n, hn⟩ := hG Ω s (sheafFiberAddEquivOfForgetIso e s x)
  refine ⟨n, (sheafFiberAddEquivOfForgetIso e s).injective ?_⟩
  rw [map_nsmul, hn, map_zero]

/-- Torsion of invertible order only depends on the underlying abelian sheaf. -/
lemma IsTorsionSheafOfInvertibleOrder.of_forgetIso (S : Scheme.{u})
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G)
    [IsTorsionSheafOfInvertibleOrder S G] : IsTorsionSheafOfInvertibleOrder S F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨n, hn, hu, hx⟩ := IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
      (S := S) Ω s (sheafFiberAddEquivOfForgetIso e s x)
    refine ⟨n, hn, hu, (sheafFiberAddEquivOfForgetIso e s).injective ?_⟩
    rw [map_nsmul, hx, map_zero]

end Scheme

namespace IsCurve

open Etale

/-- **Curve assertions are invariant under forgetting coefficient scalars.** Let `F` and `G`
be constructible étale sheaves of `Λ`-modules and of `R`-modules respectively on a `k`-scheme
`f : X ⟶ Spec k`, whose underlying abelian sheaves are isomorphic. If the eight assertions
`C(X, G)` hold, then so do the eight assertions `C(X, F)`.
(blueprint: `lem-v2-underlying-abelian-assertions`) -/
theorem assertions_of_underlying_abelian_iso {Λ R : Type (u + 1)} [CommRing Λ] [CommRing R]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    [Scheme.IsConstructibleSheaf F] [Scheme.IsConstructibleSheaf G]
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G)
    (hG : Assertions R f G) : Assertions Λ f F := by
  have hinj (q : ℕ) := injective_H_map_of_retract e.hom e.inv e.hom_inv_id q
  refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_, fun p _ _ hp q hq ↦ ?_, fun q ↦ ?_, fun q ↦ ?_,
    fun k' _ _ X' ι f' ι' h q ↦ ?_, fun k' _ _ X' ι f' ι' h q ↦ ?_, fun {W} a _ ↦ ?_⟩
  · have := hG.subsingleton_of_two_lt q hq
    exact (hinj q).subsingleton
  · have := hG.subsingleton_of_one_lt_of_isAffine q hq
    exact (hinj q).subsingleton
  · have := hG.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p
      (Scheme.IsPrimaryTorsionSheaf.of_forgetIso e.symm hp) q hq
    exact (hinj q).subsingleton
  · have := Scheme.IsTorsionSheafOfInvertibleOrder.of_forgetIso (Spec (.of k)) e.symm
    have := hG.finite_of_isTorsionSheafOfInvertibleOrder q
    exact Finite.of_injective _ (hinj q)
  · have := hG.finite_of_isProper q
    exact Finite.of_injective _ (hinj q)
  · have := Scheme.IsTorsionSheafOfInvertibleOrder.of_forgetIso (Spec (.of k)) e.symm
    exact bijective_cohomologyMap_of_retract ι' e.hom e.inv e.hom_inv_id q
      (hG.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h q)
  · exact bijective_cohomologyMap_of_retract ι' e.hom e.inv e.hom_inv_id q
      (hG.bijective_cohomologyMap_of_isProper k' h q)
  · exact surjective_cohomologyMap_of_retract a e.hom e.inv e.hom_inv_id 2
      (hG.surjective_cohomologyMap_of_isOpenImmersion a)

end IsCurve

end AlgebraicGeometry
