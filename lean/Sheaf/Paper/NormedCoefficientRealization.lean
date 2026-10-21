/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-!
# Realization of finite normed coefficient fields

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.8.1 and
Remark 6.8.15; the node's algebraic embedding and scalar transport expansion
(blueprint: lem-sfb-normed-coefficient-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormedCoefficientRealization

/-- Postcomposition by a continuous ring map, in the existing universe-sized continuous
coefficient construction. Source: Bhatt--Scholze, Definition 6.8.1, and the continuous-map
formula of sk-def-sfb-condensed-ring (blueprint: lem-sfb-normed-coefficient-realization). -/
def condenseMap {T T' : Type u} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (φ : T →+* T') (hφ : Continuous φ) :
    Mon.mk (Profinite.continuousCoefficientRingObj T) ⟶
      Mon.mk (Profinite.continuousCoefficientRingObj T') :=
  Mon.Hom.mk ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ⟨{ app := fun _ ↦ RingCat.ofHom
           (ULift.ringEquiv.symm.toRingHom.comp
             ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
         naturality := fun _ _ _ ↦ rfl }⟩)

/-- The actual termwise inverse scalar restriction for the point-induced coefficient
isomorphism. Source: the node's proof step 4; Stacks 03CZ
(blueprint: lem-sfb-normed-coefficient-realization). -/
abbrev transport {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ') (Z : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ.X Z)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ'.X Z)) :=
  (Mod.comap (coefficientMap a.inv.hom Z) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ'.X Z)).mapDerivedCategory

/-- The canonical inverse-image comparison from the coefficient square induced from the
point. Source: the node's proof steps 7 and 9; Stacks 03CZ
(blueprint: lem-sfb-normed-coefficient-realization). -/
def pullComparison {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPullback Λ.X f ⋙ transport a X ≅
      transport a Y ⋙ CondensedRing.moduleObjectDerivedPullback Λ'.X f :=
  Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f) (transport a X) ≪≫
    CondensedRing.derivedComapUpperStarIso a.inv.hom f ≪≫
    Functor.isoWhiskerLeft (transport a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).symm

/-- All the categorical conclusions for one of the two coefficient isomorphisms. The
comparison is constrained by the actual derived module-adjunction counits and the
point-induced inverse-image comparison, rather than by a freely chosen adjunction.
Source: Bhatt--Scholze, Remark 6.8.15; the node's proof steps 4--10; Stacks 03CZ, 010N,
015F, 09T5 (blueprint: lem-sfb-normed-coefficient-realization). -/
def IsCoefficientTransport {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ') : Prop :=
  (∀ Z : Scheme.{u},
    Nonempty ((Mod.extendScalars (coefficientMap a.hom.hom Z)).leftDerivedFunctor ≅
      transport a Z) ∧
    (transport a Z).IsEquivalence ∧ (transport a Z).IsTriangulated ∧
    (transport a.symm Z).IsEquivalence ∧ (transport a.symm Z).IsTriangulated ∧
    (∀ K n, (DerivedCategory.IsLE ((transport a Z).obj K) n ↔
        DerivedCategory.IsLE K n) ∧
      (DerivedCategory.IsGE ((transport a Z).obj K) n ↔ DerivedCategory.IsGE K n)) ∧
    (∀ K n, (DerivedCategory.IsLE ((transport a.symm Z).obj K) n ↔
        DerivedCategory.IsLE K n) ∧
      (DerivedCategory.IsGE ((transport a.symm Z).obj K) n ↔ DerivedCategory.IsGE K n)) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ'.X Z) ((transport a Z).obj K) ↔
      boundedConstructible (condensedRingObj Λ.X Z) K) ∧
    (∀ K, boundedConstructible (condensedRingObj Λ.X Z) ((transport a.symm Z).obj K) ↔
      boundedConstructible (condensedRingObj Λ'.X Z) K)) ∧
  (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    ∃ γ : CondensedRing.moduleObjectDerivedPushforward Λ.X f ⋙ transport a Y ≅
        transport a X ⋙ CondensedRing.moduleObjectDerivedPushforward Λ'.X f,
      ∀ K,
        (CondensedRing.moduleObjectDerivedPullback Λ'.X f).map (γ.inv.app K) ≫
          (pullComparison a f).inv.app
            ((CondensedRing.moduleObjectDerivedPushforward Λ.X f).obj K) ≫
          (transport a X).map
            ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ.X f).counit.app K) =
        (CondensedRing.derivedUpperStarLowerStarAdjunction Λ'.X f).counit.app
          ((transport a X).obj K))

private theorem norm_spectral (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖) (x : E) :
    ‖x‖ = spectralNorm ℚ_[ℓ] E x :=
  spectralNorm_unique_field_norm_ext (f := NormedField.toAbsoluteValue E) hE x

private theorem integers_norm (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖) (x : E) :
    x ∈ Padic.coefficientExtensionIntegers ℓ E ↔ ‖x‖ ≤ 1 := by
  have h := (Padic.extension_integers_dvr ℓ E (Padic.coefficientExtensionAbsoluteValue ℓ E)
    (spectralNorm_extends (K := ℚ_[ℓ]) (L := E))).choose_spec.choose_spec.1 x
  change x ∈ Padic.coefficientExtensionIntegers ℓ E ↔ spectralNorm ℚ_[ℓ] E x ≤ 1 at h
  rw [← norm_spectral ℓ E hE x] at h
  exact h

private theorem embedding_isometry (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Type u} [NormedField E] [NormedField F]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] [Algebra ℚ_[ℓ] F]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖)
    (hF : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] F x‖ = ‖x‖) (σ : E →ₐ[ℚ_[ℓ]] F) :
    Isometry σ := by
  let v : AbsoluteValue E ℝ :=
    { toFun := fun x ↦ ‖σ x‖
      map_mul' := fun x y ↦ by simp only [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero]
      add_le' := fun x y ↦ by simpa only [map_add] using norm_add_le (σ x) (σ y) }
  have hv (x : E) : ‖σ x‖ = ‖x‖ := by
    exact (spectralNorm_unique_field_norm_ext (f := v)
      (fun a ↦ by change ‖σ (algebraMap ℚ_[ℓ] E a)‖ = ‖a‖; rw [σ.commutes]; exact hF a)
      x).trans (norm_spectral ℓ E hE x).symm
  exact AddMonoidHomClass.isometry_of_norm σ hv

private def condenseIso {T T' : Type u} [TopologicalSpace T] [CommRing T]
    [IsTopologicalRing T] [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (φ : T ≃+* T') (hφ : Continuous φ) (hφi : Continuous φ.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj T) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj T') where
  hom := condenseMap φ.toRingHom hφ
  inv := condenseMap φ.symm.toRingHom hφi
  hom_inv_id := by
    ext S x
    change ULift.up _ = x
    apply ULift.ext
    ext t
    exact φ.symm_apply_apply _
  inv_hom_id := by
    ext S x
    change ULift.up _ = x
    apply ULift.ext
    ext t
    exact φ.apply_symm_apply _

private local instance comap_iso_equivalence {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    (Mod.comap φ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R).IsEquivalence :=
  (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor

private theorem bounds_comap {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R)) (n : ℤ) :
    (DerivedCategory.IsLE ((Mod.comap φ).mapDerivedCategory.obj K) n ↔
      DerivedCategory.IsLE K n) ∧
    (DerivedCategory.IsGE ((Mod.comap φ).mapDerivedCategory.obj K) n ↔
      DerivedCategory.IsGE K n) := by
  constructor
  · rw [DerivedCategory.isLE_iff, DerivedCategory.isLE_iff]
    constructor
    · intro h i hi
      exact (Mod.comap φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (h i hi)
    · intro h i hi
      exact (Mod.comap φ).isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)
  · rw [DerivedCategory.isGE_iff, DerivedCategory.isGE_iff]
    constructor
    · intro h i hi
      exact (Mod.comap φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
        (h i hi)
    · intro h i hi
      exact (Mod.comap φ).isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)

private theorem constructible_comap_iff {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R) :
    IsConstructibleModuleObject S ((Mod.comap φ).obj M) ↔
      IsConstructibleModuleObject R M := by
  constructor
  · intro h
    exact constructible_of_iso ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm
      (constructible_comap _ h)
  · exact constructible_comap φ

private theorem bounded_comap_iff {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R)) :
    boundedConstructible S ((Mod.comap φ).mapDerivedCategory.obj K) ↔
      boundedConstructible R K := by
  rw [mem_boundedConstructible_iff, mem_boundedConstructible_iff]
  apply and_congr
  · constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, fun i hi ↦
        (Mod.comap φ).isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (h i hi)⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, fun i hi ↦
        (Mod.comap φ).isZero_homologyFunctor_mapDerivedCategory_obj (h i hi)⟩
  · apply forall_congr'
    intro n
    let e := ((Mod.comap φ).mapDerivedCategoryHomologyFunctorIso n).app K
    exact ⟨fun h ↦ (constructible_comap_iff φ _).1 (constructible_of_iso e.symm h),
      fun h ↦ constructible_of_iso e ((constructible_comap_iff φ _).2 h)⟩

private theorem transport_property {Λ Λ' : Profinite.CondensedRing.{u}}
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (a : Λ ≅ Λ') :
    IsCoefficientTransport a := by
  constructor
  · intro Z
    let φ := coefficientMap a.hom.hom Z
    let ψ := coefficientMap a.inv.hom Z
    have hφ : IsIso φ := by dsimp [φ, coefficientMap]; infer_instance
    have hψ : IsIso ψ := by dsimp [ψ, coefficientMap]; infer_instance
    have hi : inv φ = ψ := by
      dsimp [φ, ψ, coefficientMap]
      rw [← Functor.map_inv]
      congr 1
      exact IsIso.inv_eq_of_hom_inv_id (by
        change (Mon.forget _).map a.hom ≫ (Mon.forget _).map a.inv = 𝟙 _
        rw [← Functor.map_comp, a.hom_inv_id]
        exact (Mon.forget _).map_id Λ)
    have hlim : PreservesFiniteLimits (Mod.extendScalars φ) :=
      preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv φ).symm
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ?_, bounds_comap ψ, bounds_comap φ,
      bounded_comap_iff ψ, bounded_comap_iff φ⟩
    · exact (Mod.extendScalars φ).leftDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (Mod.extendScalarsIsoComapInv φ) ≪≫
        Functor.mapDerivedCategoryNatIso (Mod.comapCongr hi)
    all_goals infer_instance
  · intro X Y f
    let adj := CondensedRing.derivedUpperStarLowerStarAdjunction Λ.X f
    let adj' := CondensedRing.derivedUpperStarLowerStarAdjunction Λ'.X f
    have hX : (transport a X).IsEquivalence := by
      dsimp [transport]
      infer_instance
    have hY : (transport a Y).IsEquivalence := by
      dsimp [transport]
      infer_instance
    let θ := (pullComparison a f).symm
    let β := (mateEquiv adj adj' θ.hom).natTrans
    have hβ : IsIso β := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
      adj adj' (transport a Y) (transport a X) θ
    refine ⟨asIso β, fun K ↦ ?_⟩
    have hm := mateEquiv_counit adj adj' θ.hom K
    change (CondensedRing.moduleObjectDerivedPullback Λ'.X f).map (inv β |>.app K) ≫
      θ.hom.app _ ≫ (transport a X).map (adj.counit.app K) = adj'.counit.app _
    rw [← hm]
    change (CondensedRing.upperStar Λ'.X f).leftDerivedFunctor.map ((inv β).app K) ≫
      (CondensedRing.upperStar Λ'.X f).leftDerivedFunctor.map (β.app K) ≫
        adj'.counit.app _ = adj'.counit.app _
    rw [← Functor.map_comp_assoc]
    simp


/-- A finite normed extension is realized isometrically in the fixed algebraic closure;
its unit ball and both condensed coefficient presentations induce the specified exact
unbounded derived equivalences, preserving bounds and stratified local finite presentation.

Source: Bhatt--Scholze, Definition 6.8.1 and Remark 6.8.15; agent expansion recorded in
the DAG (blueprint: lem-sfb-normed-coefficient-realization).

Proof:
1. Finite dimension makes E algebraic. Apply the algebraic-closure embedding theorem
(lem-weil-pbc-algebraic-extension-embeds-algebraically-closed, Stacks 09GU), take E' to be
the field range of the embedding and transport finite dimension along the algebra
isomorphism onto it.
2. Pull back the closure absolute value. Its restriction is the normalized p-adic norm,
so spectral-norm uniqueness (lem-weil-l-adic-extension-absolute-value) identifies it with
the supplied norm. This makes the algebra isomorphism and its inverse isometric. The
membership clause of lem-weil-l-adic-extension-integers-dvr identifies the chosen integer
subrings with the closed unit balls, so the isometry restricts to the integer rings.
3. Postcomposition gives the condensed ring isomorphisms. The integer-ring square
commutes sectionwise because its map is the restriction of the field map.
4. For the pulled-back invertible coefficient map c, scalar restriction along c is an
equivalence and Ext_c is isomorphic to Res_(c^-1) (sk-def-sfb-change-of-scalars, Stacks
03CZ). The exact-functor comparison L(Ext_c) = D(Ext_c)
(lem-weil-pbc-exact-functor-derived-functor) identifies the derived extension with the
transport; it is a triangulated equivalence (lem-sf-exact-functor-derived-triangulated).
5. Exact scalar restriction commutes with cohomology and is faithful
(lem-weil-pbc-exact-functor-complex-cohomology, Stacks 010N), so it preserves and
reflects every bound.
6. The scalar-restriction transport of constructible modules
(lem-weil-pbc-module-constructible-pullback), applied along c and its inverse with the
scalar-equivalence unit, and the cohomology comparison of step 5 give
sk-def-sfb-bounded-constructible in both directions.
7. For f : X → Y let θ be the inverse of the point-induced pullback comparison and β its
mate under the published derived pullback/pushforward adjunctions. The vertical
transports are equivalences, so β is invertible (lem-weil-mate-iso-along-equivalences).
The mate counit identity, precomposed with Lf'^*(β_K^-1), is the displayed counit
equation for γ = β.
-/
theorem normed_coefficient_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E Ω : Type u) [NormedField E] [NormedField Ω]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    [Algebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (hE : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] E x‖ = ‖x‖)
    (hΩ : ∀ x : ℚ_[ℓ], ‖algebraMap ℚ_[ℓ] Ω x‖ = ‖x‖) :
    ∃ (E' : IntermediateField ℚ_[ℓ] Ω) (_ : FiniteDimensional ℚ_[ℓ] E')
      (σ : E ≃ₐ[ℚ_[ℓ]] E') (_hσ : Continuous σ) (_hσi : Continuous σ.symm)
      (τ : Padic.coefficientExtensionIntegers ℓ E ≃+*
        Padic.coefficientExtensionIntegers ℓ E')
      (_hτ : Continuous τ) (_hτi : Continuous τ.symm)
      (sE : Mon.mk (Profinite.continuousCoefficientRingObj E) ≅
        Mon.mk (Profinite.continuousCoefficientRingObj E'))
      (sA : Mon.mk (Profinite.continuousCoefficientRingObj
          (Padic.coefficientExtensionIntegers ℓ E)) ≅
        Mon.mk (Profinite.continuousCoefficientRingObj
          (Padic.coefficientExtensionIntegers ℓ E'))),
      Isometry σ ∧ Isometry τ ∧
      (∀ x : E, x ∈ Padic.coefficientExtensionIntegers ℓ E ↔ ‖x‖ ≤ 1) ∧
      (∀ x : E', x ∈ Padic.coefficientExtensionIntegers ℓ E' ↔ ‖x‖ ≤ 1) ∧
      (∀ x, (τ x : E') = σ (x : E)) ∧
      sE.hom = condenseMap σ.toRingHom _hσ ∧
      sA.hom = condenseMap τ.toRingHom _hτ ∧
      condenseMap (Padic.coefficientExtensionIntegers ℓ E).subtype
          continuous_subtype_val ≫ sE.hom =
        sA.hom ≫ condenseMap (Padic.coefficientExtensionIntegers ℓ E').subtype
          continuous_subtype_val ∧
      IsCoefficientTransport sE ∧ IsCoefficientTransport sA := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ_[ℓ]
  let i : E →ₐ[ℚ_[ℓ]] Ω := IsAlgClosed.lift
  let E' := i.fieldRange
  let σ : E ≃ₐ[ℚ_[ℓ]] E' := i.equivFieldRange
  let : FiniteDimensional ℚ_[ℓ] E' := σ.toLinearEquiv.finiteDimensional
  have hE' (x : ℚ_[ℓ]) : ‖algebraMap ℚ_[ℓ] E' x‖ = ‖x‖ := hΩ x
  have hσ : Isometry σ := embedding_isometry ℓ hE hE' σ.toAlgHom
  have hσi : Isometry σ.symm := embedding_isometry ℓ hE' hE σ.symm.toAlgHom
  let τ := σ.toRingEquiv.restrict (Padic.coefficientExtensionIntegers ℓ E)
    (Padic.coefficientExtensionIntegers ℓ E') (fun x ↦ by
      rw [integers_norm ℓ E hE, integers_norm ℓ E' hE']
      change ‖x‖ ≤ 1 ↔ ‖σ x‖ ≤ 1
      rw [(AddMonoidHomClass.isometry_iff_norm σ).1 hσ x])
  have hτ : Isometry τ := by
    intro x y
    exact hσ x.val y.val
  have hτi : Isometry τ.symm := by
    intro x y
    exact hσi x.val y.val
  let sE := condenseIso σ.toRingEquiv hσ.continuous hσi.continuous
  let sA := condenseIso τ hτ.continuous hτi.continuous
  refine ⟨E', inferInstance, σ, hσ.continuous, hσi.continuous, τ,
    hτ.continuous, hτi.continuous, sE, sA, hσ, hτ, integers_norm ℓ E hE,
    integers_norm ℓ E' hE', ?_, rfl, rfl, ?_, transport_property sE,
    transport_property sA⟩
  · intro x
    rfl
  · ext S x
    rfl

end AlgebraicGeometry.ProEtale.NormedCoefficientRealization
