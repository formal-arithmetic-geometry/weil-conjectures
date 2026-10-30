/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.SeparableClosureCover
public import WeilConjectures.TateTwist.RingSectionsUpperStar
public import WeilConjectures.TateTwist.RootsOfUnityTrivialization

/-!
# Pullback of the sheaves of roots of unity along an arbitrary morphism

Let `f : X ⟶ Y` be a morphism of schemes, where `Y` lives over a field `k`, and let `N` be
invertible in `k`. Then `f^* μ_{N,Y} ≅ μ_{N,X}` for the sheaves of `N`-th roots of unity on the
pro-étale sites (`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIsoOfField`), compatibly
with the power maps `μ_{m N} ⟶ μ_N`
(`AlgebraicGeometry.ProEtale.upperStar_map_rootsOfUnitySheafPow_comp_isoOfField`). Only weakly étale
`f` was treated before (`AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIso`).

## Proof

The isomorphism is the comparison map `φ_f : f^* μ_{N,Y} ⟶ μ_{N,X}` of
`WeilConjectures.TateTwist.RingSectionsUpperStar` for the functor `R ↦ μ_N(R)`, adjoint to
pulling back roots of unity along the projections `V ×_Y X ⟶ V`. To see that it is invertible:

* if `Y` lives over a field `K` containing a primitive `N`-th root of unity `ζ`, then
  `a ↦ ζ ^ a` exhibits `μ_N` as the cokernel of `N : ℤ ⟶ ℤ` on `Y` and on `X`
  (`AlgebraicGeometry.ProEtale.isColimitUnitToRootsOfUnitySheaf`), `f^*` is right exact and sends
  `ℤ` to `ℤ`, and `φ_f` is compatible with these presentations: both composites
  `ℤ ⟶ f_* μ_{N,X}` send `1` to `ζ`
  (`AlgebraicGeometry.ProEtale.unitToRootsOfUnitySections_comp_toLowerStar`). Hence `φ_f` is an
  isomorphism of cokernels
  (`AlgebraicGeometry.ProEtale.isIso_upperStarRingSectionsSheafHom_of_isPrimitiveRoot`);
* in general, let `kˢᵉᵖ` be a separable closure of `k`, `Y' = Y ×_k kˢᵉᵖ ⟶ Y` and
  `X' = X ×_k kˢᵉᵖ ⟶ X` the weakly étale covers and `f' : X' ⟶ Y'` the base change of `f`. Then
  `φ` is compatible with composition and is invertible for weakly étale maps, so from
  `X' ⟶ X ⟶ Y = X' ⟶ Y' ⟶ Y` and the previous case for `f'` the pullback of `φ_f` to `X'` is an
  isomorphism. Pullbacks along pro-étale covers detect isomorphisms
  (`AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction`).

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarRootsOfUnitySheafIsoOfField`: `f^* μ_{N,Y} ≅ μ_{N,X}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Limits

/-- Let `p : A ⟶ B` be a cokernel of `a : A' ⟶ A` and `q : C₀ ⟶ D` a cokernel of `b : B' ⟶ C₀`,
and let `e : A ≅ C₀`, `e' : A' ≅ B'` identify `a` with `b`. Then a morphism `φ : B ⟶ D` with
`p ≫ φ = e.hom ≫ q` is an isomorphism. -/
lemma isIso_of_isColimit_cokernelCofork {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A A' B C₀ B' D : C} {a : A' ⟶ A} {p : A ⟶ B} {wp : a ≫ p = 0}
    (hp : IsColimit (CokernelCofork.ofπ p wp)) {b : B' ⟶ C₀} {q : C₀ ⟶ D} {wq : b ≫ q = 0}
    (hq : IsColimit (CokernelCofork.ofπ q wq)) (e : A ≅ C₀) (e' : A' ≅ B')
    (he : a ≫ e.hom = e'.hom ≫ b) (φ : B ⟶ D) (hφ : p ≫ φ = e.hom ≫ q) : IsIso φ := by
  have hb : b ≫ e.inv ≫ p = 0 := by
    rw [← cancel_epi e'.hom, ← Category.assoc, ← he]
    simp [wp]
  let ψ : D ⟶ B := Cofork.IsColimit.desc hq (e.inv ≫ p) (by simpa using hb)
  have hψ : q ≫ ψ = e.inv ≫ p := Cofork.IsColimit.π_desc hq
  refine ⟨ψ, Cofork.IsColimit.hom_ext hp ?_, Cofork.IsColimit.hom_ext hq ?_⟩
  · simp only [Cofork.π_ofπ]
    rw [reassoc_of% hφ, hψ, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · simp only [Cofork.π_ofπ]
    rw [reassoc_of% hψ, hφ, Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### `μ_N` as a sheaf of the form `U ↦ F(Γ(U, 𝒪_U))` -/

/-- The presheaf `U ↦ μ_N(Γ(U, 𝒪_U))` is a sheaf
(`AlgebraicGeometry.ProEtale.isSheaf_rootsOfUnityPresheaf`), in the form required by
`AlgebraicGeometry.ProEtale.ringSectionsSheaf`. -/
lemma isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor (N : ℕ) (X : Scheme.{u}) :
    Presheaf.IsSheaf (ProEt.topology X)
      (ringSectionsPresheaf (CommRingCat.rootsOfUnityFunctor N) X) :=
  isSheaf_rootsOfUnityPresheaf X N

/-- The sheaf `U ↦ μ_N(Γ(U, 𝒪_U))`, isomorphic to `μ_N` by
`AlgebraicGeometry.ProEtale.rootsOfUnitySheafIso`. -/
noncomputable abbrev rootsOfUnitySections (X : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology X) Ab.{u + 1} :=
  ringSectionsSheaf (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) X

/-! ### Over a field containing a primitive root of unity -/

variable {K : Type u} [Field K] {N : ℕ}

/-- The map `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`, with values in the sheaf `U ↦ μ_N(Γ(U, 𝒪_U))`. -/
noncomputable def unitToRootsOfUnitySections {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) {ζ : K}
    (hζ : ζ ^ N = 1) : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ rootsOfUnitySections Y N :=
  unitToRootsOfUnitySheaf p hζ ≫ (rootsOfUnitySheafIso Y N).hom

/-- On the unit presheaf, `AlgebraicGeometry.ProEtale.unitToRootsOfUnitySections` is the map of
presheaves `a ↦ ζ ^ a`. -/
lemma ε_comp_unitToRootsOfUnitySections [NeZero N] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    {ζ : K} (hζ : ζ ^ N = 1) :
    ε (sheafToPresheaf (ProEt.topology Y) Ab.{u + 1}) ≫
      (sheafToPresheaf (ProEt.topology Y) Ab.{u + 1}).map (unitToRootsOfUnitySections p hζ) =
      unitToRootsOfUnityPresheaf p (rootsOfUnity.mkOfPowEq ζ hζ) := by
  have hε : ε (sheafToPresheaf (ProEt.topology Y) Ab.{u + 1}) =
      toSheafify (ProEt.topology Y) _ := by
    rw [← sheafificationAdjunction_unit_app]
    exact ((sheafificationAdjunction _ _).homEquiv_unit _ _ _).trans (Category.comp_id _)
  rw [hε, unitToRootsOfUnitySections, unitToRootsOfUnitySheaf_eq]
  change toSheafify (ProEt.topology Y) (𝟙_ (Y.ProEtᵒᵖ ⥤ Ab.{u + 1})) ≫
    sheafifyMap (ProEt.topology Y) (unitToRootsOfUnityPresheaf p (rootsOfUnity.mkOfPowEq ζ hζ)) ≫
      (isoSheafify (ProEt.topology Y) (isSheaf_rootsOfUnityPresheaf Y N)).inv = _
  rw [← toSheafify_naturality_assoc, ← isoSheafify_hom (hP := isSheaf_rootsOfUnityPresheaf Y N),
    Iso.hom_inv_id, Category.comp_id]

/-- The ring maps `K ⟶ Γ(V, 𝒪_V)` are compatible with pulling back along the projection
`V ×_Y X ⟶ V`. -/
lemma fieldToSections_comp_appTop_pullbackFst {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of K)) (V : Y.ProEt) :
    fieldToSections p V ≫ (pullback.fst V.hom f).appTop =
      fieldToSections (f ≫ p) ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V) := by
  simp only [fieldToSections, Category.assoc, ← Scheme.Hom.comp_appTop]
  rw [pullback.condition_assoc]
  rfl

/-- The two maps `ℤ ⟶ f_* μ_{N,X}` agree: `a ↦ ζ ^ a` on `Y` followed by pulling back roots of
unity, and the unit `ℤ ⟶ f_* ℤ` followed by `f_*` of `a ↦ ζ ^ a` on `X`. -/
lemma unitToRootsOfUnitySections_comp_toLowerStar [NeZero N] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of K)) {ζ : K} (hζ : ζ ^ N = 1) :
    unitToRootsOfUnitySections p hζ ≫ toLowerStarRingSectionsSheaf _ f =
      ε (f)_*[Ab.{u + 1}] ≫ (f)_*[Ab.{u + 1}].map (unitToRootsOfUnitySections (f ≫ p) hζ) := by
  apply Sheaf.unit_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ε_comp_unitToRootsOfUnitySections]
  ext V : 2
  have h1 := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) Ab.{u + 1} (ProEt.topology Y)
      (ProEt.topology X) V
  have h2 := congr_app (ε_comp_unitToRootsOfUnitySections (f ≫ p) hζ)
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj V)
  simp only [NatTrans.comp_app]
  rw [NatTrans.comp_app] at h2
  erw [reassoc_of% h1, h2]
  refine (Category.assoc _ _ _).trans (congrArg (unitToRootsOfUnity _ ≫ ·) ?_)
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  exact fieldToSections_comp_appTop_pullbackFst f p V.unop

/-- `φ_f` is compatible with the maps `ℤ ⟶ μ_N`, `a ↦ ζ ^ a`, on `Y` and on `X`, through the
identification `f^* ℤ ≅ ℤ`. -/
lemma upperStar_map_unitToRootsOfUnitySections_comp [NeZero N] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of K)) {ζ : K} (hζ : ζ ^ N = 1) :
    (f)^*[Ab.{u + 1}].map (unitToRootsOfUnitySections p hζ) ≫
        upperStarRingSectionsSheafHom (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f =
      η (f)^*[Ab.{u + 1}] ≫ unitToRootsOfUnitySections (f ≫ p) hζ := by
  rw [upperStarRingSectionsSheafHom, ← Adjunction.homEquiv_naturality_left_symm,
    unitToRootsOfUnitySections_comp_toLowerStar, Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- **`φ_f` is an isomorphism over a field containing a primitive `N`-th root of unity**: both
`f^* μ_{N,Y}` and `μ_{N,X}` are cokernels of `N : ℤ ⟶ ℤ`, compatibly with `φ_f`. -/
lemma isIso_upperStarRingSectionsSheafHom_of_isPrimitiveRoot [NeZero N] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (p : Y ⟶ Spec (.of K)) {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    IsIso (upperStarRingSectionsSheafHom
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f) := by
  let k := (f)^*[Ab.{u + 1}].mapIso (rootsOfUnitySheafIso Y N)
  let l : rootsOfUnitySheaf X N ≅ rootsOfUnitySections X N := rootsOfUnitySheafIso X N
  have : IsIso (k.hom ≫ upperStarRingSectionsSheafHom
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f ≫ l.inv) := by
    refine isIso_of_isColimit_cokernelCofork (isColimitCoforkMapOfIsColimit'
        (f)^*[Ab.{u + 1}] _ (isColimitUnitToRootsOfUnitySheaf p hζ))
      (isColimitUnitToRootsOfUnitySheaf (f ≫ p) hζ) (asIso (η (f)^*[Ab.{u + 1}]))
      (asIso (η (f)^*[Ab.{u + 1}])) ?_ _ ?_
    · simp
    · have h := upperStar_map_unitToRootsOfUnitySections_comp f p hζ.pow_eq_one
      simp only [unitToRootsOfUnitySections, Functor.map_comp] at h
      simp only [k, l, Functor.mapIso_hom, asIso_hom, ← Category.assoc, h]
      simp
  have : IsIso (upperStarRingSectionsSheafHom
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f ≫ l.inv) :=
    IsIso.of_isIso_comp_left k.hom _
  exact IsIso.of_isIso_comp_right _ l.inv

/-! ### Over an arbitrary field -/

/-- **`φ_f` is an isomorphism over a field `k` in which `N` is invertible**, for an arbitrary
morphism `f : X ⟶ Y` and `Y` over `k`: after base change to a separable closure of `k`, this is
the case of a field containing a primitive `N`-th root of unity. -/
lemma isIso_upperStarRingSectionsSheafHom_rootsOfUnity {k : Type u} [Field k] [NeZero (N : k)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Spec (.of k)) :
    IsIso (upperStarRingSectionsSheafHom
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f) := by
  have : NeZero N := ⟨fun h ↦ NeZero.ne (N : k) (by simp [h])⟩
  have : NeZero (N : SeparableClosure k) :=
    ‹NeZero (N : k)›.of_injective (algebraMap k (SeparableClosure k)).injective
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} (SeparableClosure k) N
  let s := specSepClosureHom k
  let f' : pullback (f ≫ p) s ⟶ pullback p s :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hsq : pullback.fst (f ≫ p) s ≫ f = f' ≫ pullback.fst p s :=
    (pullback.lift_fst _ _ _).symm
  have h₁ : IsIso (upperStarRingSectionsSheafHom
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) (pullback.fst (f ≫ p) s ≫ f)) := by
    rw [hsq, upperStarRingSectionsSheafHom_comp]
    have := isIso_upperStarRingSectionsSheafHom_of_weaklyEtale
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) (pullback.fst p s)
    have := isIso_upperStarRingSectionsSheafHom_of_isPrimitiveRoot f' (pullback.snd p s) hζ
    infer_instance
  have h₂ : IsIso ((pullback.fst (f ≫ p) s)^*[Ab.{u + 1}].map
      (upperStarRingSectionsSheafHom (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f)) := by
    rw [upperStarRingSectionsSheafHom_comp] at h₁
    have := isIso_upperStarRingSectionsSheafHom_of_weaklyEtale
      (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) (pullback.fst (f ≫ p) s)
    rwa [isIso_comp_left_iff, isIso_comp_right_iff] at h₁
  have : ∀ i, WeaklyEtale ((sepClosureCover (f ≫ p)).f i) := fun i ↦
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ (sepClosureCover _).mem₀ (.mk i)
  refine isIso_of_isIso_localizationRestriction Ab.{u + 1} _ (sepClosureCover (f ≫ p)).f
    (sepClosureCover (f ≫ p)).mem₀ fun i ↦ ?_
  exact (NatIso.isIso_map_iff (upperStarIsoLocalizationRestriction Ab.{u + 1}
    (pullback.fst (f ≫ p) s) inferInstance) _).1 h₂

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **The pullback of `μ_N` along an arbitrary morphism**: for `f : X ⟶ Y` with `Y` over a field
`k` in which `N` is invertible, `f^* μ_{N,Y} ≅ μ_{N,X}`. It is induced by pulling back roots of
unity (`AlgebraicGeometry.ProEtale.upperStarRingSectionsSheafHom`). -/
noncomputable def upperStarRootsOfUnitySheafIsoOfField (N : ℕ) [NeZero (N : k)] (f : X ⟶ Y)
    (p : Y ⟶ Spec (.of k)) :
    (f)^*[Ab.{u + 1}].obj (rootsOfUnitySheaf Y N) ≅ rootsOfUnitySheaf X N :=
  haveI := isIso_upperStarRingSectionsSheafHom_rootsOfUnity (N := N) f p
  (f)^*[Ab.{u + 1}].mapIso (rootsOfUnitySheafIso Y N) ≪≫
    asIso (upperStarRingSectionsSheafHom (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f) ≪≫
      (rootsOfUnitySheafIso X N).symm

/-- The isomorphism `f^* μ_N ≅ μ_N` is compatible with the power maps `μ_{m N} ⟶ μ_N`. -/
lemma upperStar_map_rootsOfUnitySheafPow_comp_isoOfField (N m : ℕ) [NeZero (N : k)]
    [NeZero ((m * N : ℕ) : k)] (f : X ⟶ Y) (p : Y ⟶ Spec (.of k)) :
    (f)^*[Ab.{u + 1}].map (rootsOfUnitySheafPow Y N m) ≫
        (upperStarRootsOfUnitySheafIsoOfField N f p).hom =
      (upperStarRootsOfUnitySheafIsoOfField (m * N) f p).hom ≫ rootsOfUnitySheafPow X N m := by
  have h := upperStar_map_ringSectionsSheafMap_comp (CommRingCat.rootsOfUnityPow N m)
    (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor (m * N))
    (isSheaf_ringSectionsPresheaf_rootsOfUnityFunctor N) f
  simp only [upperStarRootsOfUnitySheafIsoOfField, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, rootsOfUnitySheafPow_comp_rootsOfUnitySheafIso_hom,
    Functor.map_comp_assoc, rootsOfUnitySheafIso_inv_comp_rootsOfUnitySheafPow]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ (rootsOfUnitySheafIso X N).inv) h

/-- The isomorphism `f^* μ_N ≅ μ_N` is compatible with the identifications `μ_N = μ_{N'}` for
`N = N'`. -/
@[reassoc]
lemma upperStar_map_eqToHom_comp_isoOfField {N N' : ℕ} [NeZero (N : k)] [NeZero (N' : k)]
    (h : N = N') (f : X ⟶ Y) (p : Y ⟶ Spec (.of k)) :
    (f)^*[Ab.{u + 1}].map (eqToHom (congrArg (rootsOfUnitySheaf Y) h)) ≫
        (upperStarRootsOfUnitySheafIsoOfField N' f p).hom =
      (upperStarRootsOfUnitySheafIsoOfField N f p).hom ≫
        eqToHom (congrArg (rootsOfUnitySheaf X) h) := by
  subst h
  simp

end AlgebraicGeometry.ProEtale
