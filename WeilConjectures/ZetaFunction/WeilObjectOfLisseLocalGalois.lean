/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelGaloisTrace
public import WeilConjectures.TraceFormula.WeilIdentityStalkTrace
public import WeilConjectures.ZetaFunction.WeilObjectOfLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStrictlyHenselian
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The local traces of the Weil object of a lisse sheaf as Galois traces

For a lisse `ℓ`-adic sheaf `H` on `X₀`, `b ∈ ℚ̄_ℓˣ` and an `𝔽_{q^{n+1}}`-point `y` of `X₀` with
geometric point `x̄ = Spec ι ≫ y`, the local trace of the Weil object `(H, b)` at `x̄`, read in
`ℚ̄_ℓ`, is `b^{n+1}` times the trace of the Galois action of `σ^{n+1}` on the global sections
`Γ(Spec k̄, x̄^* H)` of the model of the `ℓ`-adic sheaves
(`WeilComplex.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse_eq`); on
the side of the Weil sheaf `p^* H`, its trace function is the same Galois trace
(`WeilSheaf.traceFunction_geometricFiberPullback_eq_trace`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor Limits

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite

omit [Finite k₀] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- A point of degree `n + 1` for the identity is fixed by `σ^{n+1}`. -/
lemma comp_eq_of_comp_pow_refl {n : ℕ} {Ω : Type u} [CommRing Ω] {σ : Spec (.of Ω) ⟶ Spec (.of Ω)}
    {x : Spec (.of Ω) ⟶ (overSpec (k₀ := k₀) X).left}
    (hx : x ≫ ((Iso.refl (overSpec (k₀ := k₀) X)).pow (n + 1)).hom.left = σ ≫ x) : σ ≫ x = x := by
  rw [pow_hom_left_eq_id (by rw [Iso.refl_hom, Over.id_left]) (n + 1), Category.comp_id] at hx
  exact hx.symm

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- The geometric point of an `𝔽_{q^{n+1}}`-point is fixed by `σ^{n+1}`. -/
lemma frobeniusFixedPointsReflOfFieldPoint_fixed (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    ((geometricFrobeniusField k₀).pow (n + 1)).hom ≫
        (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1 =
      (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1 :=
  comp_eq_of_comp_pow_refl (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2

/-- The unfolding of `AlgebraicGeometry.ProEtale.galoisUpperStarEnd`. -/
lemma galoisUpperStarEnd_eq_comp {Ω : Type u} [Field Ω] [IsSepClosed Ω] {Y : Scheme.{u}}
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ Y) (h : σ ≫ x = x)
    (τ : (σ)^*⟦Profinite.padicAlgClRingObj l⟧ ≅ 𝟭 _)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) Y)) (f : M ⟶ M) :
    τ.inv.app ((x)^*⟦Profinite.padicAlgClRingObj l⟧.obj M) ≫
        (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) σ x).inv.app M ≫
        (CondensedRing.upperStarEqToIso (Profinite.padicAlgClRingObj l) h).hom.app M ≫
        (x)^*⟦Profinite.padicAlgClRingObj l⟧.map f =
      galoisUpperStarEnd σ x h τ M f :=
  rfl

theorem endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse_eq
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    endTensorUnitRingEquiv l (AlgebraicClosure k₀)
        (weilStalkTraceAlternatingSum l (n + 1) _
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2
          (weilObjectOfLisse (k₀ := k₀) hH b)) =
      (b : PadicAlgCl l) ^ (n + 1) * LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections
          ((geometricFrobeniusField k₀).pow (n + 1)).hom
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1
          (frobeniusFixedPointsReflOfFieldPoint_fixed n y) H)).hom := by
  have hK0 : (weilObjectOfLisse (k₀ := k₀) hH b).str =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj.{u} l) l _).app
        (weilObjectOfLisse (k₀ := k₀) hH b).carrier ≪≫ boundedConstructibleOfLisseSMulIso hH b :=
    IsoAlgebra.mk_str _ _
  have hK := congrArg Iso.hom hK0
  rw [Iso.trans_hom, Iso.app_hom] at hK
  rw [weilStalkTraceAlternatingSum_eq_traceOrZero_of_homology l _ _ hK (fun j hj ↦ ?_)
    ((adicSheafEquivCondensedMod l X).functor.obj H)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
      ((adicSheafEquivCondensedMod l X).functor.obj H))
    ((adicSheafEquivCondensedMod l X).functor.mapIso (WeilCoefficients.smulIso b H))
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.naturality
      ((adicSheafEquivCondensedMod l X).functor.map (WeilCoefficients.smulIso b H).hom))]
  · rw [weilSheafStalkTrace, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
      WeilSheaf.powFunctor_obj]
    -- remaining: `traceOrZero_stalkFunctor_obj_pow_mk`, `galoisUpperStarEnd_eq_comp` and
    -- `endTensorUnitRingEquiv_traceOrZero_galoisUpperStarEnd`; instantiating the first one at the
    -- concrete Frobenius makes the kernel time out
    sorry
  · obtain hj | hj := lt_or_gt_of_ne hj
    · exact ((DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)).isZero_of_isGE 0 j hj
    · exact ((DerivedCategory.singleFunctor _ 0).obj
        ((adicSheafEquivCondensedMod l X).functor.obj H)).isZero_of_isLE 0 j hj

/-- **The trace function of a pulled-back lisse sheaf is the trace of the Galois action**: at an
`𝔽_{q^{n+1}}`-point `y` with geometric point `x̄ = Spec ι ≫ y`, the trace function of `p^* H` is
the trace of the action of `σ^{n+1}` on the global sections `Γ(Spec k̄, x̄^* H)`. -/
theorem _root_.AlgebraicGeometry.WeilSheaf.traceFunction_geometricFiberPullback_eq_trace
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH).traceFunction (n + 1) y =
      LinearMap.trace (PadicAlgCl l) _
        ((WeilCoefficients.toModuleCat l).map (galoisGlobalSections
          ((geometricFrobeniusField k₀).pow (n + 1)).hom
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).1
          (frobeniusFixedPointsReflOfFieldPoint_fixed n y) H)).hom := by
  sorry

end AlgebraicGeometry.WeilComplex
