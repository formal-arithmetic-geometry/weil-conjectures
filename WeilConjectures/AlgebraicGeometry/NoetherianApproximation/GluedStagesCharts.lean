/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluingStages
public import WeilConjectures.AlgebraicGeometry.OpensGlueData

/-!
# Chart maps of subrings of section rings

Let `U` be an open of a scheme `S` and `A ⊆ Γ(S, U)` a subring. For every open `W ≤ U` the
inclusion `A ⊆ Γ(S, U) ⟶ Γ(S, W)` induces a morphism `W ⟶ Spec A`
(`AlgebraicGeometry.Scheme.subringChart`). These are the chart maps from `S` to the charts of
the finite-type stages of a finite affine gluing presentation.

If `U` is affine, the chart maps are *epimorphic towards affine schemes* on the opens
`⋃ᵢ D(kᵢ)` of `Spec A` (`AlgebraicGeometry.Scheme.chartLift_cancel`): two morphisms out of
`⋃ᵢ D(kᵢ) ⊆ Spec A` into an affine scheme agree as soon as they agree on `⋃ᵢ D_S(kᵢ) ⊆ S`.
This is the geometric form of the fact that `A[1/k] → Γ(S, D(k)) = Γ(S, U)[1/k]` is injective
(localization is exact). Moreover a morphism `⋃ᵢ D_S(kᵢ) ⟶ Spec R` extends to `⋃ᵢ D(kᵢ)` as soon
as on every `D_S(kᵢ)` it is given by sections lying in `A[1/kᵢ]`
(`AlgebraicGeometry.Scheme.exists_chartLift_comp_eq`), and we have a criterion for the image of
such an extension (`AlgebraicGeometry.Scheme.range_subset_iSup_basicOpen`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

lemma resLE_comp {U W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    S.resLE h ≫ S.resLE h' = S.resLE (h'.trans h) := by
  rw [resLE, resLE, ← Functor.map_comp]
  rfl

lemma resLE_resLE_apply {U W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(S, U)) :
    S.resLE h' (S.resLE h x) = S.resLE (h'.trans h) x := by
  rw [← resLE_comp h h']
  rfl

@[reassoc]
lemma homOfLE_toSpecΓ_SpecMap {W W' : S.Opens} (h : W' ≤ W) {R : CommRingCat.{u}}
    (ρ : R ⟶ Γ(S, W)) :
    S.homOfLE h ≫ W.toSpecΓ ≫ Spec.map ρ = W'.toSpecΓ ≫ Spec.map (ρ ≫ S.resLE h) := by
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp]


/-! ### Basic opens of spectra -/

/-- The basic open `D(r)` of `Spec R`, as an open of the scheme `Spec R`. -/
def specBasicOpen {R : CommRingCat.{u}} (r : R) : (Spec R).Opens :=
  PrimeSpectrum.basicOpen r


/-- `D(r) ⊆ Spec R` is isomorphic to `Spec R[1/r]`. -/
noncomputable def specBasicOpenIso {R : CommRingCat.{u}} (r : R) :
    (specBasicOpen r).toScheme ≅ Spec (CommRingCat.of (Localization.Away r)) :=
  basicOpenIsoSpecAway r

@[reassoc (attr := simp)]
lemma specBasicOpenIso_hom_SpecMap {R : CommRingCat.{u}} (r : R) :
    (specBasicOpenIso r).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
      (specBasicOpen r).ι :=
  basicOpenIsoSpecAway_hom_SpecMap r
variable {U : S.Opens}

/-- The basic open `D(x)` of `Spec A`, for `x` in a subring `A ⊆ Γ(S, U)`. -/
abbrev chartBasicOpen (A : Subring Γ(S, U)) (x : A) : (Spec (CommRingCat.of A)).Opens :=
  specBasicOpen (R := CommRingCat.of A) x

/-- `D(x) ⊆ Spec A` is isomorphic to `Spec A[1/x]`. -/
noncomputable abbrev chartBasicOpenIso (A : Subring Γ(S, U)) (x : A) :
    (chartBasicOpen A x).toScheme ≅ Spec (CommRingCat.of (Localization.Away x)) :=
  specBasicOpenIso (R := CommRingCat.of A) x

/-- The ring map `A ⟶ Γ(S, W)` induced by a subring `A ⊆ Γ(S, U)`, for `W ≤ U`. -/
noncomputable def subringRes (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U) :
    CommRingCat.of A ⟶ Γ(S, W) :=
  CommRingCat.ofHom ((S.resLE h).hom.comp A.subtype)


@[reassoc (attr := simp)]
lemma subringRes_comp_resLE (A : Subring Γ(S, U)) {W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    subringRes A h ≫ S.resLE h' = subringRes A (h'.trans h) := by
  ext x
  exact resLE_resLE_apply h h' (x : Γ(S, U))

/-- The chart map `W ⟶ Spec A` induced by a subring `A ⊆ Γ(S, U)`, for `W ≤ U`. -/
noncomputable def subringChart (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U) :
    W.toScheme ⟶ Spec (CommRingCat.of A) :=
  W.toSpecΓ ≫ Spec.map (subringRes A h)

@[reassoc (attr := simp)]
lemma homOfLE_subringChart (A : Subring Γ(S, U)) {W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    S.homOfLE h' ≫ subringChart A h = subringChart A (h'.trans h) := by
  rw [subringChart, homOfLE_toSpecΓ_SpecMap, subringRes_comp_resLE]
  rfl

/-- The chart maps are compatible with inclusions of subrings. -/
@[reassoc (attr := simp)]
lemma subringChart_comp_SpecMap_inclusion {A A' : Subring Γ(S, U)} (hAA' : A ≤ A')
    {W : S.Opens} (h : W ≤ U) :
    subringChart A' h ≫ Spec.map (CommRingCat.ofHom (Subring.inclusion hAA')) =
      subringChart A h := by
  rw [subringChart, subringChart, Category.assoc, ← Spec.map_comp]
  rfl


/-- The chart map `W ⟶ Spec A`, lifted to an open `V ⊆ Spec A` containing its image. -/
noncomputable def chartLift (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    (V : (Spec (CommRingCat.of A)).Opens) (hV : Set.range (subringChart A h) ⊆ V) :
    W.toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (subringChart A h) (by rwa [Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
lemma chartLift_ι (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    (V : (Spec (CommRingCat.of A)).Opens) (hV : Set.range (subringChart A h) ⊆ V) :
    chartLift A h V hV ≫ V.ι = subringChart A h :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma homOfLE_chartLift (A : Subring Γ(S, U)) {W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W)
    {V V' : (Spec (CommRingCat.of A)).Opens} (hVV' : V' ≤ V)
    (hV : Set.range (subringChart A h) ⊆ V) (hV' : Set.range (subringChart A (h'.trans h)) ⊆ V') :
    S.homOfLE h' ≫ chartLift A h V hV =
      chartLift A (h'.trans h) V' hV' ≫ (Spec (CommRingCat.of A)).homOfLE hVV' := by
  rw [← cancel_mono V.ι]
  simp

/-! ### Basic opens -/

section BasicOpen

variable (A : Subring Γ(S, U)) (x : A)

/-- The ring map `A[1/x] ⟶ Γ(S, D(x))`. -/
noncomputable def awayLift : Localization.Away x →+* Γ(S, S.basicOpen (x : Γ(S, U))) :=
  IsLocalization.Away.lift x (g := (subringRes A (S.basicOpen_le (x : Γ(S, U)))).hom)
    (RingedSpace.isUnit_res_basicOpen S.toRingedSpace _)

lemma awayLift_algebraMap (y : A) :
    awayLift A x (algebraMap A _ y) = S.resLE (S.basicOpen_le (x : Γ(S, U))) (y : Γ(S, U)) :=
  IsLocalization.Away.lift_eq _ _ _

lemma ofHom_algebraMap_comp_awayLift :
    CommRingCat.ofHom (algebraMap (CommRingCat.of A) (Localization.Away x)) ≫
      CommRingCat.ofHom (awayLift A x) = subringRes A (S.basicOpen_le (x : Γ(S, U))) := by
  ext y
  exact awayLift_algebraMap A x y


variable {A x}

/-- The chart lift to `D(x)`, read through `D(x) ≅ Spec A[1/x]`, is `Spec` of `awayLift`. -/
@[reassoc]
lemma chartLift_chartBasicOpenIso (h : S.basicOpen (x : Γ(S, U)) ≤ U) (hV) :
    chartLift A h (chartBasicOpen A x) hV ≫ (chartBasicOpenIso A x).hom =
      (S.basicOpen (x : Γ(S, U))).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayLift A x)) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CommRingCat.of A) (Localization.Away x)))) :=
    IsOpenImmersion.of_isLocalization x
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom
    (algebraMap (CommRingCat.of A) (Localization.Away x)))), Category.assoc,
    specBasicOpenIso_hom_SpecMap, chartLift_ι, Category.assoc, ← Spec.map_comp,
    ofHom_algebraMap_comp_awayLift]
  rfl


end BasicOpen

/-! ### Finite unions of basic opens -/

section iSup

variable {A : Subring Γ(S, U)} {σ : Type*} (k : σ → A)


end iSup

end AlgebraicGeometry.Scheme
