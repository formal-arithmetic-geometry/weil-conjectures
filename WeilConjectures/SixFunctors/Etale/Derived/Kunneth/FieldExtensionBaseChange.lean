/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.LimitBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PerfectSeparable
public import WeilConjectures.FieldTheory.SeparableSmoothColimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent

/-!
# Higher direct images commute with base change along field extensions

Let `L/K` be a field extension and `g : T ⟶ S` a quasi-compact quasi-separated morphism of
schemes over `K`. For every sheaf `F` on `T` whose geometric stalks are torsion of orders
invertible in `K`, the base-change map `R^q g_* F |_{S_L} ⟶ R^q g_{L,*} (F|_{T_L})` is an
isomorphism (blueprint `lem-kun-0f1c`, Stacks 0F1C). After passing to perfect closures (a
universal homeomorphism does not change the étale sites) the extension is separable, hence a
filtered colimit of smooth algebras, and smooth base change along limits
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth`) applies.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`

## References

- Stacks Project, Lemma 59.89.4, <https://stacks.math.columbia.edu/tag/0F1C>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Being torsion of orders invertible on `S` passes to any `S'` mapping to `S`. -/
lemma Scheme.IsTorsionSheafOfInvertibleOrder.of_hom {S S' T : Scheme.{u}} (b : S' ⟶ S)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [hF : Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    Scheme.IsTorsionSheafOfInvertibleOrder S' F where
  exists_isUnit_nsmul_eq_zero Ω _ _ s x := by
    obtain ⟨n, hn, hu, hx⟩ := hF.exists_isUnit_nsmul_eq_zero Ω s x
    exact ⟨n, hn, by simpa using hu.map b.appTop.hom, hx⟩

/-- **Base change along a separable field extension.** Let `L / K` be a separable field
extension and `g : T ⟶ S` a quasi-compact quasi-separated morphism of schemes over `K`. Then the
base-change map of the square `T_L = T ×_S S_L` is an isomorphism in every degree, at every sheaf
on `T` with torsion stalks of orders invertible in `K`. Indeed `L` is the filtered colimit of
its smooth finite type `K`-subalgebras (blueprint `lem-kun-separable-smooth-colimit`), so `S_L` is
the limit of the smooth `S`-schemes `S ×_K Spec A`, and blueprint `lem-kun-0f09` applies. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isSeparableExtension {K L : Type u} [Field K]
    [Field L] [Algebra K L] (hKL : Algebra.IsSeparableExtension K L) {S T S' T' : Scheme.{u}}
    (σ : S ⟶ Spec (.of K)) (g : T ⟶ S) [QuasiCompact g] [QuasiSeparated g] (p : S' ⟶ S)
    (σ' : S' ⟶ Spec (.of L))
    (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {e : T' ⟶ T} {h : T' ⟶ S'} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  let 𝒜 := {A : Subalgebra K L | Algebra.Smooth K A ∧ Algebra.FiniteType K A}
  have : IsFiltered 𝒜 := Algebra.isFiltered_smooth_finiteType_subalgebra_of_isSeparableExtension hKL
  have hcol := Algebra.isColimitSmoothFiniteTypeSubalgebraOfIsSeparableExtension hKL
  let D₀ : 𝒜ᵒᵖ ⥤ Scheme.{u} := (Subalgebra.diagram 𝒜).op ⋙ Scheme.Spec
  have : PreservesLimitsOfSize.{u, u} Scheme.Spec.{u} :=
    ΓSpec.adjunction.rightAdjoint_preservesLimits
  have hD₀ := isLimitOfPreserves Scheme.Spec.{u} hcol.op
  let π : D₀ ⟶ (Functor.const 𝒜ᵒᵖ).obj (Spec (.of K)) :=
    { app A := Spec.map (CommRingCat.ofHom (algebraMap K A.unop.1))
      naturality A B f := by
        simp only [D₀, Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        rw [Scheme.Spec_map, ← Spec.map_comp]
        rfl }
  have hP (A : 𝒜ᵒᵖ) : (Scheme.Spec.mapCone (Subalgebra.cocone 𝒜).op).π.app A ≫ π.app A =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    simp only [Functor.mapCone_π_app, Cocone.op_π, NatTrans.op_app, Scheme.Spec_map, π]
    rw [← Spec.map_comp]
    rfl
  let X := baseChangeOverDiagram D₀ π σ
  let c := baseChangeOverCone D₀ π (Scheme.Spec.mapCone (Subalgebra.cocone 𝒜).op)
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) hP σ
  have hc : IsLimit c := isLimitBaseChangeOverCone D₀ π _ _ hP σ hD₀
  let c' := c.extend hS.isoPullback.hom
  have hc' : IsLimit c' := hc.ofIsoLimit (Cones.extendIso c hS.isoPullback.symm)
  let pX : X ⟶ (Functor.const 𝒜ᵒᵖ).obj S :=
    { app A := pullback.fst σ (π.app A)
      naturality A B f := by simp [X] }
  have : ∀ A, Smooth (π.app A) := fun A ↦ by
    have : Algebra.Smooth K A.unop.1 := A.unop.2.1
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).2
      ((RingHom.smooth_algebraMap).2 inferInstance)
  have : ∀ A, Smooth (pX.app A) := fun A ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ (π.app A)) inferInstance
  have : ∀ A, QuasiCompact (pX.app A) := fun A ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ (π.app A)) inferInstance
  have : ∀ A, QuasiSeparated (pX.app A) := fun A ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback σ (π.app A)) inferInstance
  have : ∀ {A B : 𝒜ᵒᵖ} (f : A ⟶ B), IsAffineHom (D₀.map f) := fun f ↦
    (inferInstance : IsAffineHom (Spec.map _))
  have : Scheme.IsTorsionSheafOfInvertibleOrder S F :=
    Scheme.IsTorsionSheafOfInvertibleOrder.of_hom Λ σ F
  exact Etale.isIso_baseChangeHomologyMap_of_isLimit_smooth' Λ g X pX hc' p
    (fun A ↦ by simp [c', c, pX]) sq q F

/-- Blueprint `lem-kun-0f1c`: Direct image commutes with base change along field extensions.

Let `L/K` be a field extension, `σ : S ⟶ Spec K` a scheme over `K` and `g : T ⟶ S` a
quasi-compact quasi-separated morphism. Let `S' = S ×_K L` (the Cartesian square `hS`) and
`T' = T ×_S S'` (the Cartesian square `sq`). For every sheaf `F` of `Λ`-modules on `T` whose
geometric stalks are torsion of orders invertible in `K`, the base-change map
`R^q g_* F |_{S'} ⟶ R^q h_* (F|_{T'})` is an isomorphism in every degree `q`. -/
@[stacks 0F1C]
theorem Etale.isIso_baseChangeHomologyMap_of_fieldExtension {K L : Type u} [Field K] [Field L]
    [Algebra K L] {S T S' T' : Scheme.{u}} (σ : S ⟶ Spec (.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (p : S' ⟶ S) (σ' : S' ⟶ Spec (.of L))
    (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {e : T' ⟶ T} {h : T' ⟶ S'} (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
