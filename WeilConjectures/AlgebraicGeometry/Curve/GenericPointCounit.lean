/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.AlgebraicGeometry.Sites.GaloisDescent

/-!
# Pushforward along the generic point

Let `X` be an integral quasi-separated scheme with generic point `η : Spec k(X) ⟶ X`. For an
abelian étale sheaf `M` on `Spec k(X)`, the unit `η_* M ⟶ η_* η^* η_* M` is an isomorphism: by
continuity of sections at the limit `Spec k(X) = lim_U Spec Γ(X, U)`
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), the sections of
`η_* η^* G` over an affine étale `X`-scheme are the colimit of the sections of the
`j_{U*} j_U^* G`, and for `G = η_* M` all the units `G ⟶ j_{U*} j_U^* G` are isomorphisms since
`η` factors through the open immersion `j_U`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_bijective_app_of_isAffine`: a morphism of étale sheaves
  bijective on the sections over affine étale schemes is an isomorphism.
- `AlgebraicGeometry.Scheme.isIso_unit_app_lowerStar_fromSpecFunctionField`: the unit
  `η_* M ⟶ η_* η^* η_* M` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

section Spreading

open Polynomial TensorProduct

/-- **Spreading out a finite separable extension of a fraction field.** Let `R` be a domain with
fraction field `K` and `E/K` a finite separable extension. Then there is an étale `R`-algebra `T`
with an `R`-algebra map `T ⟶ E` and a `K`-algebra map `E ⟶ K ⊗_R T`: a primitive element of
`E` has a minimal polynomial with coefficients in some `R[1/b]`, and `T` is the standard étale
algebra of this polynomial over `R[1/b]`. -/
theorem exists_etale_algHom_tensorProduct {R K E : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] [Algebra R E] [IsScalarTower R K E] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T), Algebra.Etale R T ∧
      Nonempty (T →ₐ[R] E) ∧ Nonempty (E →ₐ[K] K ⊗[R] T) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable K E
  set f := minpoly K pb.gen
  have hfm : f.Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    f.coeffs
  have hbu : IsUnit (algebraMap R K b) := IsLocalization.map_units K ⟨b, hb⟩
  let Rb := Localization.Away b
  let φ : Rb →+* K := IsLocalization.Away.lift b hbu
  have hφ : φ.comp (algebraMap R Rb) = algebraMap R K := IsLocalization.Away.lift_comp b hbu
  have hrange (c : K) (hc : c ∈ f.coeffs) : c ∈ Set.range φ := by
    obtain ⟨r, hr⟩ := hint c hc
    refine ⟨IsLocalization.mk' Rb r (⟨b, 1, pow_one b⟩ : Submonoid.powers b), ?_⟩
    have h₁ : φ (IsLocalization.mk' Rb r (⟨b, 1, pow_one b⟩ : Submonoid.powers b)) *
        algebraMap R K b = algebraMap R K r := by
      rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    refine mul_right_cancel₀ hbu.ne_zero (h₁.trans ?_)
    rw [hr, Algebra.smul_def, mul_comm]
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeffs_subset_range _).2 fun c hc ↦ hrange c hc) hfm
  let P := StandardEtalePair.ofMonic hFm 1
  let T := P.Ring
  let : Algebra R T := ((algebraMap Rb T).comp (algebraMap R Rb)).toAlgebra
  have : IsScalarTower R Rb T := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R Rb := Algebra.Etale.of_isLocalizationAway b
  have : Algebra.Etale R T := Algebra.Etale.comp R Rb T
  -- the point `T ⟶ E`
  let : Algebra Rb E := ((algebraMap K E).comp φ).toAlgebra
  have : IsScalarTower R Rb E := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    change algebraMap R E r = algebraMap K E (φ (algebraMap R Rb r))
    rw [← RingHom.comp_apply φ, hφ, ← IsScalarTower.algebraMap_apply])
  have haeval (q : Rb[X]) : aeval pb.gen q = aeval pb.gen (q.map φ) := by
    rw [aeval_def, aeval_def, eval₂_map]
    rfl
  have hθ : P.HasMap pb.gen := by
    refine ⟨?_, ?_⟩
    · rw [StandardEtalePair.ofMonic_f, haeval, hF]
      exact minpoly.aeval K pb.gen
    · rw [StandardEtalePair.ofMonic_g, one_mul, haeval, ← Polynomial.derivative_map, hF]
      exact (Algebra.IsSeparable.isSeparable K pb.gen).aeval_derivative_ne_zero
        (minpoly.aeval K pb.gen) |>.isUnit
  refine ⟨T, inferInstance, inferInstance, inferInstance,
    ⟨(P.lift pb.gen hθ).restrictScalars R⟩, ⟨pb.lift (1 ⊗ₜ P.X) ?_⟩⟩
  -- the two maps `R[1/b] ⟶ K ⊗_R T` agree
  have hcomm : (algebraMap K (K ⊗[R] T)).comp φ =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap Rb T) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers b) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [← RingHom.comp_apply φ, hφ, ← IsScalarTower.algebraMap_apply R Rb T]
    change algebraMap R K r ⊗ₜ[R] (1 : T) = (1 : K) ⊗ₜ[R] algebraMap R T r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h₀ : aeval P.X F = 0 := P.hasMap_X.1
  change aeval _ f = 0
  rw [← hF, aeval_def, eval₂_map, hcomm]
  change eval₂ _ (Algebra.TensorProduct.includeRight.toRingHom P.X) F = 0
  rw [← Polynomial.hom_eval₂]
  change Algebra.TensorProduct.includeRight.toRingHom (aeval P.X F) = 0
  rw [h₀, map_zero]

end Spreading

namespace AlgebraicGeometry

open Etale

/-- A morphism of abelian étale sheaves which is bijective on the sections over every étale
scheme with affine underlying scheme is an isomorphism. -/
lemma Etale.isIso_of_bijective_app_of_isAffine {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : ∀ W : X.Etale, IsAffine W.left → Function.Bijective (φ.hom.app (op W))) : IsIso φ := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  refine (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨⟨fun {V} x y hxy ↦ ?_⟩, ⟨fun {V} s ↦ ?_⟩⟩
  · refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ (h W hW).1 ?_
    change φ.hom.app _ (F.obj.map g.op x) = φ.hom.app _ (F.obj.map g.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg _ hxy
  · refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ ?_
    obtain ⟨t, ht⟩ := (h W hW).2 (G.obj.map g.op s)
    exact ⟨t, ht⟩

namespace Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- For a nonempty affine open `U` of an integral scheme `X`, the unit `G ⟶ j_* j^* G` of the open
immersion `j : Spec Γ(X, U) ⟶ X` is an isomorphism on pushforwards `G = η_* M` from the generic
point, since `η` factors through `j`. -/
lemma isIso_affineOpenUnit_lowerStar (U : X.NonemptyAffineOpens)
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (X.affineOpenUnit U ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M)) := by
  let j := X.affineOpensDiagramι.app U
  let π := X.functionFieldCone.π.app U
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j
  let Z := (π)_*[AddCommGrpCat.{u + 1}].obj M
  let e : (X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M ≅
      (j)_*[AddCommGrpCat.{u + 1}].obj Z :=
    ((lowerStarComp AddCommGrpCat.{u + 1} π j X.fromSpecFunctionField
      (X.fromSpecFunctionField_eq_functionFieldCone_comp U)).app M).symm
  have : IsOpenImmersion j := U.2.1.isOpenImmersion_fromSpec
  have hZ : IsIso (adj.unit.app ((j)_*[AddCommGrpCat.{u + 1}].obj Z)) := by
    have h := adj.right_triangle_components Z
    have : IsIso ((j)_*[AddCommGrpCat.{u + 1}].map (adj.counit.app Z)) := inferInstance
    exact IsIso.of_isIso_comp_right _ ((j)_*[AddCommGrpCat.{u + 1}].map (adj.counit.app Z))
  have hn := adj.unit.naturality e.hom
  have : IsIso (adj.unit.app _ ≫ ((j)^*[AddCommGrpCat.{u + 1}] ⋙
      (j)_*[AddCommGrpCat.{u + 1}]).map e.hom) := by
    rw [← hn]
    change IsIso (e.hom ≫ _)
    infer_instance
  exact IsIso.of_isIso_comp_right (adj.unit.app _)
    (((j)^*[AddCommGrpCat.{u + 1}] ⋙ (j)_*[AddCommGrpCat.{u + 1}]).map e.hom)

/-- **Field points of the generic fibre.** Let `X` be an integral scheme with generic point
`η : Spec k(X) ⟶ X` and `E/k(X)` a finite separable extension. Then there is an étale `X`-scheme
`V` with nonempty generic fibre `V ×_X Spec k(X)` admitting a `k(X)`-morphism to `Spec E`: the
spectrum of the standard étale algebra of the minimal polynomial of a primitive element of `E`
over a nonempty affine open of `X`
(`exists_etale_algHom_tensorProduct`). -/
theorem exists_hom_etaleSpec_of_fromSpecFunctionField (E : Type u) [Field E]
    [Algebra X.functionField E] [Algebra.Etale X.functionField E] :
    ∃ (V : X.Etale) (_ : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
      X.fromSpecFunctionField).obj V ⟶ etaleSpec X.functionField E),
      Nonempty ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
        X.fromSpecFunctionField).obj V).left := by
  let K := X.functionField
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  let R := Γ(X, U)
  have : IsFractionRing R K := functionField_isFractionRing_of_isAffineOpen X U hU
  have hi : X.fromSpecFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hU.fromSpec := by
    change X.fromSpecStalk (genericPoint X) = _
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hηU]
    rfl
  have : Module.Finite K E := Algebra.FormallyUnramified.finite_of_free K E
  have : Algebra.IsSeparable K E := (Algebra.FormallyEtale.iff_isSeparable K E).1 inferInstance
  let : Algebra R E := ((algebraMap K E).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨T, _, _, hT, ⟨θ⟩, ⟨ψ⟩⟩ := exists_etale_algHom_tensorProduct (R := R) (K := K) (E := E)
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 hT)
  let V : X.Etale := Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ hU.fromSpec)
  let Y := Limits.pullback V.hom X.fromSpecFunctionField
  have w : pullback.fst V.hom X.fromSpecFunctionField ≫
      Spec.map (CommRingCat.ofHom (algebraMap R T)) =
      pullback.snd V.hom X.fromSpecFunctionField ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, ← hi]
    exact pullback.condition
  let ι : Y ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) := pullback.lift _ _ w.symm
  refine ⟨V, MorphismProperty.Over.homMk (ι ≫ (pullbackSpecIso R K T).hom ≫
    Spec.map (CommRingCat.ofHom ψ.toRingHom)) ?_, ?_⟩
  · change (ι ≫ (pullbackSpecIso R K T).hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) = pullback.snd _ _
    have hψ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact ψ.commutes x
    rw [Category.assoc, Category.assoc, hψ, pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  · have hc : Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ V.hom =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ X.fromSpecFunctionField := by
      change _ ≫ Spec.map _ ≫ _ = _
      rw [hi, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r
      exact (θ.commutes r).trans (IsScalarTower.algebraMap_apply R K E r)
    obtain ⟨z⟩ : Nonempty (Spec (.of E)) := inferInstance
    exact ⟨pullback.lift _ _ hc z⟩

lemma bijective_app_of_isIso {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [IsIso φ] (W : Y.Etale) : Function.Bijective (φ.hom.app (op W)) := by
  have : IsIso ((sheafToPresheaf _ _).map φ) := inferInstance
  have : IsIso (((sheafToPresheaf _ _).map φ).app (op W)) := inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

variable [QuasiSeparatedSpace X]

/-- **The unit at a pushforward from the generic point is an isomorphism.** For an integral
quasi-separated scheme `X` with generic point `η : Spec k(X) ⟶ X` and an abelian étale sheaf `M`
on `Spec k(X)`, the unit `η_* M ⟶ η_* η^* η_* M` is an isomorphism: on the sections over an affine
étale `X`-scheme it is the colimit of the units of the nonempty affine opens
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`), which are isomorphisms
(`AlgebraicGeometry.Scheme.isIso_affineOpenUnit_lowerStar`). -/
theorem isIso_unit_app_lowerStar_fromSpecFunctionField
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app
      ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M)) := by
  set G := (X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M
  let ε := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app G
  let D := X.affineOpensDiagram
  let ι := X.affineOpensDiagramι
  let c := X.functionFieldCone
  have hc : IsLimit c := X.isLimitFunctionFieldCone
  have hP := X.fromSpecFunctionField_eq_functionFieldCone_comp
  let τ (U : X.NonemptyAffineOpens) := unitComparison (c.π.app U) (ι.app U)
    X.fromSpecFunctionField (hP U) G
  have hτ (U : X.NonemptyAffineOpens) : X.affineOpenUnit U G ≫ τ U = ε :=
    unit_app_comp_unitComparison _ _ _ _ G
  refine Etale.isIso_of_bijective_app_of_isAffine ε fun W hW ↦ ⟨?_, fun t ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro g hg
    let U₀ : X.NonemptyAffineOpens := Classical.arbitrary _
    have h₀ : (τ U₀).hom.app (op W) ((X.affineOpenUnit U₀ G).hom.app (op W) g) = 0 := by
      rw [← hτ U₀] at hg
      exact hg
    obtain ⟨U, f', hU⟩ := exists_unitComparison_app_eq_zero_of_isLimit D ι c
      X.fromSpecFunctionField hP hc G W U₀ _ h₀
    have hgU : (X.affineOpenUnit U G).hom.app (op W) g = 0 := by
      rw [← X.affineOpenUnit_comp_transition f' G]
      exact hU
    have := isIso_affineOpenUnit_lowerStar X U M
    exact (bijective_app_of_isIso _ W).1 (hgU.trans (map_zero _).symm)
  · obtain ⟨U, s, hs⟩ := unitComparison_app_surjective_of_isLimit D ι c
      X.fromSpecFunctionField hP hc G W t
    have := isIso_affineOpenUnit_lowerStar X U M
    obtain ⟨g, rfl⟩ := (bijective_app_of_isIso (X.affineOpenUnit U G) W).2 s
    refine ⟨g, ?_⟩
    rw [← hs, ← hτ U]
    rfl

omit [QuasiSeparatedSpace X] in
/-- Every point of an étale `k(X)`-scheme lies in the image of a morphism from the generic fibre
`V ×_X Spec k(X)` of an étale `X`-scheme `V`. -/
lemma exists_hom_mem_range_of_fromSpecFunctionField (W : (Spec X.functionField).Etale)
    (w : W.left) :
    ∃ (V : X.Etale) (h : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
      X.fromSpecFunctionField).obj V ⟶ W), w ∈ Set.range h.left := by
  obtain ⟨E, _, _, _, e, ⟨z, hz⟩⟩ := exists_etaleSpec_hom_mem_range W w
  obtain ⟨V, g, ⟨y⟩⟩ := exists_hom_etaleSpec_of_fromSpecFunctionField X E
  refine ⟨V, g ≫ e, ⟨y, ?_⟩⟩
  have : Subsingleton (Spec (.of E)) := inferInstanceAs (Subsingleton (PrimeSpectrum E))
  change e.left (g.left y) = w
  rw [@Subsingleton.elim (Spec (.of E)) this (g.left y) z, hz]

/-- **The counit at the generic point is an isomorphism.** For an integral quasi-separated scheme
`X` with generic point `η : Spec k(X) ⟶ X`, the counit `η^* η_* M ⟶ M` is an isomorphism for
every abelian étale sheaf `M` on `Spec k(X)`, i.e. `η_*` is fully faithful. Its pushforward is
inverse to the unit `η_* M ⟶ η_* η^* η_* M`, an isomorphism
(`AlgebraicGeometry.Scheme.isIso_unit_app_lowerStar_fromSpecFunctionField`), so the counit is
bijective on the sections over the generic fibres of étale `X`-schemes; these cover every étale
`k(X)`-scheme (`AlgebraicGeometry.Scheme.exists_hom_mem_range_of_fromSpecFunctionField`). -/
theorem isIso_counit_app_fromSpecFunctionField
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).counit.app
      M) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : (Spec X.functionField).smallEtaleTopology.HasSheafCompose
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) := inferInstance
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField
  let c := adj.counit.app M
  have hε := isIso_unit_app_lowerStar_fromSpecFunctionField X M
  have hc : IsIso ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].map c) := by
    have h := adj.right_triangle_components M
    have : IsIso (adj.unit.app ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj M) ≫
        (X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].map c) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  -- the counit is bijective on the sections over generic fibres
  have hb (V : X.Etale) := bijective_app_of_isIso
    ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].map c) V
  refine (Sheaf.isLocallyBijective_iff_isIso c).1 ⟨⟨fun {W} x y hxy ↦ ?_⟩, ⟨fun {W} s ↦ ?_⟩⟩
  · refine (Scheme.mem_smallEtaleTopology_iff _).2 fun w ↦ ?_
    obtain ⟨V, h, hw⟩ := exists_hom_mem_range_of_fromSpecFunctionField X W.unop w
    refine ⟨_, h, (hb V).1 ?_, hw⟩
    change c.hom.app _ (_ : _) = c.hom.app _ _
    erw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg _ hxy
  · refine (Scheme.mem_smallEtaleTopology_iff _).2 fun w ↦ ?_
    obtain ⟨V, h, hw⟩ := exists_hom_mem_range_of_fromSpecFunctionField X W w
    obtain ⟨t, ht⟩ := (hb V).2 (M.obj.map h.op s)
    exact ⟨_, h, ⟨t, ht⟩, hw⟩

end Scheme

end AlgebraicGeometry
