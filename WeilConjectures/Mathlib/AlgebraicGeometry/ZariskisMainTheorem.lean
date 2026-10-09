/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.Mathlib.RingTheory.Nakayama

/-!
# Zariski's Main Theorem: the finite factorization

Mathlib's `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` proves Grothendieck's form of
Zariski's Main Theorem: a separated, quasi-compact, locally quasi-finite morphism `f : X ⟶ S`
locally of finite type factors as an open immersion into the relative normalization of `S` in
`X` followed by an integral morphism. Over a quasi-compact quasi-separated base we deduce the
factorization through a *finite* `S`-scheme (Stacks Project Tag 05K0), by writing the relative
normalization as a cofiltered limit of finite `S`-schemes and descending the open immersion to
a finite stage.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.FiniteApproximation`: a presentation of `f : X ⟶ S` as a
  cofiltered limit of finite `S`-schemes.

## Main results

- `AlgebraicGeometry.Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`: an integral
  morphism to a qcqs scheme is a limit of finite morphisms of finite presentation
  (Stacks Project Tag 09YZ).
- `AlgebraicGeometry.Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion`:
  a quasi-compact open of such a limit is open in a closed subscheme of some stage
  (blueprint `thm-pqf-immersion-descent`).
- `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`:
  **Zariski's Main Theorem**, finite factorization (Stacks Project Tag 05K0; blueprint
  `thm-pqf-zmt-factorization`).

We also prove a criterion for closed immersions: a proper morphism of schemes locally of finite
type over an algebraically closed field which is injective on closed points and whose stalk maps
at closed points are unramified is a closed immersion
(`AlgebraicGeometry.isClosedImmersion_of_injective_of_le_map_maximalIdeal`).

## Blueprint

This file formalises part (i) of `sk-prop-nagata-sketch-zmt`. The refinement for morphisms
locally of finite presentation is
`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_locallyOfFinitePresentation`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A **finite approximation** of a morphism `f : X ⟶ S` is a cofiltered system `D` of
schemes finite over `S` together with a limit cone with point `X` whose projections are
compatible with `f`: it presents `X` as a cofiltered limit of finite `S`-schemes. The transition
morphisms are then affine (`Scheme.Hom.FiniteApproximation.isAffineHom_map`).

An integral morphism to a quasi-compact quasi-separated scheme admits one, with stages of
finite presentation (`Scheme.Hom.exists_finiteApproximation_of_isIntegralHom`, Stacks Project
Tag 09YZ). This is the "finite approximation tail" of the proof of blueprint
`thm-pqf-zmt-factorization`. -/
structure Scheme.Hom.FiniteApproximation {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The index category of the inverse system. -/
  I : Type u
  /-- The category structure on the index type. -/
  [smallCategory : SmallCategory I]
  /-- The index category is cofiltered. -/
  [isCofiltered : IsCofiltered I]
  /-- The diagram of finite `S`-schemes. -/
  D : I ⥤ Scheme.{u}
  /-- The structure morphisms of the stages to `S`. -/
  p (i : I) : D.obj i ⟶ S
  /-- The transition morphisms are `S`-morphisms. -/
  map_p {i j : I} (g : i ⟶ j) : D.map g ≫ p j = p i
  /-- Every stage is finite over `S`. -/
  isFinite_p (i : I) : IsFinite (p i)
  /-- The morphisms from `X` to the stages. -/
  π : (Functor.const I).obj X ⟶ D
  /-- `X` is the limit of the stages. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The morphisms from `X` to the stages are compatible with `f`. -/
  π_p (i : I) : π.app i ≫ p i = f

namespace Scheme.Hom.FiniteApproximation

attribute [instance] smallCategory isCofiltered isFinite_p

variable {X S : Scheme.{u}} {f : X ⟶ S} (F : f.FiniteApproximation)

/-- The transition morphisms of a finite approximation are affine. -/
instance isAffineHom_map {i j : F.I} (g : i ⟶ j) : IsAffineHom (F.D.map g) := by
  have : IsAffineHom (F.D.map g ≫ F.p j) := by rw [F.map_p]; infer_instance
  exact IsAffineHom.of_comp _ (F.p j)

instance compactSpace_obj [CompactSpace S] (i : F.I) : CompactSpace (F.D.obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (F.p i)

instance quasiSeparatedSpace_obj [QuasiSeparatedSpace S] (i : F.I) :
    QuasiSeparatedSpace (F.D.obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (F.p i)

end Scheme.Hom.FiniteApproximation

/-- **An integral morphism is a limit of finite morphisms of finite presentation** (Stacks
Project Tag 09YZ). If `f : X ⟶ S` is integral and `S` is quasi-compact and quasi-separated,
then `X` is a cofiltered limit of schemes finite and of finite presentation over `S`.

This is Step 2 ("the finite approximation tail") of the proof of blueprint
`thm-pqf-zmt-factorization`: `f_* 𝒪_X` is the filtered union of its finite quasi-coherent
subalgebras. -/
@[stacks 09YZ]
theorem Scheme.Hom.exists_finiteApproximation_of_isIntegralHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegralHom f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ F : f.FiniteApproximation, ∀ i, LocallyOfFinitePresentation (F.p i) :=
  sorry

/-- **Descent of the immersion to a finite stage** (blueprint `thm-pqf-immersion-descent`).
Let `ν : N ⟶ S` be presented as a cofiltered limit of finite `S`-schemes `T_λ`, with `S`
quasi-compact and quasi-separated, and let `ι : X ⟶ N` be a quasi-compact open immersion with
`X` locally of finite type over `S`. Then there are an index `λ₀` and a factorization
`X ⟶ T ⟶ T_{λ₀}` of `X ⟶ N ⟶ T_{λ₀}` into a quasi-compact open immersion followed by a closed
immersion. If `S` is locally Noetherian, `T_{λ₀}` is moreover of finite presentation over `S`.

The image of `X` descends to a quasi-compact open `U` of some stage (Stacks Project Tag 01Z4),
`X ⟶ U` is a closed immersion from some stage on (Tag 081B), and the quasi-compact immersion
`X ⟶ U ⟶ T_{λ₀}` factors through its scheme-theoretic image (Tag 01QV). -/
theorem Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion
    {X N S : Scheme.{u}} {ν : N ⟶ S} (F : ν.FiniteApproximation) [CompactSpace S]
    [QuasiSeparatedSpace S] (ι : X ⟶ N) [IsOpenImmersion ι] [QuasiCompact ι]
    [LocallyOfFiniteType (ι ≫ ν)] :
    ∃ (i : F.I) (T : Scheme.{u}) (j : X ⟶ T) (k : T ⟶ F.D.obj i), IsOpenImmersion j ∧
      QuasiCompact j ∧ IsClosedImmersion k ∧ j ≫ k = ι ≫ F.π.app i ∧
      (IsLocallyNoetherian S → LocallyOfFinitePresentation (F.p i)) := by
  have : CompactSpace N := Scheme.compactSpace_of_isLimit F.D _ F.isLimit
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace ι
  have (i : F.I) : LocallyOfFiniteType (ι ≫ (Cone.mk N F.π).π.app i ≫ F.p i) := by
    change LocallyOfFiniteType (ι ≫ F.π.app i ≫ F.p i)
    rw [F.π_p]; infer_instance
  obtain ⟨i, U, g, hU, hg, hgU⟩ :=
    Scheme.exists_isClosedImmersion_of_isOpenImmersion_of_isLimit F.isLimit F.p ι
  have : QuasiCompact U.ι := U.quasiCompact_ι hU
  let h := g ≫ U.ι
  have : QuasiCompact h.toImage := QuasiCompact.of_comp h.toImage h.imageι
  refine ⟨i, h.image, h.toImage, h.imageι, inferInstance, inferInstance, inferInstance, ?_,
    fun _ ↦ inferInstance⟩
  rw [Scheme.Hom.toImage_imageι]
  exact hgU

/-- **Zariski's Main Theorem, finite factorization** (Stacks Project Tag 05K0; blueprint
`thm-pqf-zmt-factorization`, statement (i) of blueprint `sk-prop-nagata-sketch-zmt`). A
separated, quasi-compact, locally quasi-finite morphism `f : X ⟶ S` locally of finite type to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion `j : X ⟶ T`
followed by a finite morphism `p : T ⟶ S`.

By Grothendieck's form of Zariski's Main Theorem, `X` is a quasi-compact open of the relative
normalization of `S` in `X`, which is integral over `S` and hence a limit of finite
`S`-schemes (Tag 09YZ); the immersion descends to a finite stage
(`Scheme.Hom.FiniteApproximation.exists_isOpenImmersion_isClosedImmersion`). -/
@[stacks 05K0]
theorem Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f]
    [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (p : T ⟶ S), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsFinite p ∧ j ≫ p = f := by
  obtain ⟨F, -⟩ := f.fromNormalization.exists_finiteApproximation_of_isIntegralHom
  have : LocallyOfFiniteType (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]; infer_instance
  obtain ⟨i, T, j, k, hj, hjc, hk, hjk, -⟩ := F.exists_isOpenImmersion_isClosedImmersion
    f.toNormalization
  refine ⟨T, j, k ≫ F.p i, hj, hjc, inferInstance, ?_⟩
  rw [reassoc_of% hjk, F.π_p, f.toNormalization_fromNormalization]

section ClosedImmersion

variable {X Y : Scheme.{u}}

lemma IsAffineOpen.exists_primeIdealOf_eq {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = p :=
  ⟨hU.isoSpec.inv p, by
    rw [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl⟩

/-- A point which is alone in its fibre is a point at which the morphism is quasi-finite. -/
lemma Scheme.Hom.quasiFiniteAt_of_preimage_singleton {f : X ⟶ Y} [LocallyOfFiniteType f]
    {x : X} (h : f ⁻¹' {f x} = {x}) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : Subsingleton (f ⁻¹' {f x}) := by rw [h]; infer_instance
  have : Subsingleton (f.fiber (f x)) := (f.fiberHomeo (f x)).injective.subsingleton
  convert isOpen_univ
  ext y
  simp [Subsingleton.elim y (f.asFiber x)]

/-- If a closed point `x` is alone over `f x` among the closed points, and the maximal ideal of
`𝒪_{X, x}` is generated by that of `𝒪_{Y, f x}`, then `x` is alone in its fibre. -/
lemma Scheme.Hom.preimage_singleton_eq_of_le_map_maximalIdeal (f : X ⟶ Y) [CompactSpace X]
    (hf : IsClosedMap f) {x : X} (hx : IsClosed {x})
    (hinj : ∀ y : X, IsClosed {y} → f y = f x → y = x)
    (hunr : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom) :
    f ⁻¹' {f x} = {x} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun z hz ↦ ?_⟩
  obtain ⟨w, hw, hwcl⟩ := (isClosed_closure (s := {z})).exists_closed_singleton
    ⟨z, subset_closure rfl⟩
  have hfx : IsClosed {f x} := by simpa using hf _ hx
  have hfw : f w = f x := by
    have := map_mem_closure f.continuous hw (t := {f x}) fun a ha ↦ by
      rw [Set.mem_singleton_iff.mp ha]
      exact hz
    rwa [hfx.closure_eq] at this
  obtain rfl := hinj w hwcl hfw
  obtain ⟨q, rfl⟩ : z ∈ Set.range (X.fromSpecStalk w) := by
    rw [Scheme.range_fromSpecStalk]
    exact specializes_iff_mem_closure.mpr hw
  have h1 : f (X.fromSpecStalk w q) = Y.fromSpecStalk (f w) (Spec.map (f.stalkMap w) q) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply]
  have h2 : Spec.map (f.stalkMap w) q = IsLocalRing.closedPoint _ :=
    (Y.fromSpecStalk (f w)).isEmbedding.injective
      (by rw [← h1, Scheme.fromSpecStalk_closedPoint]; exact hz)
  have h3 : q = IsLocalRing.closedPoint _ := by
    have h4 : q.asIdeal.comap (f.stalkMap w).hom = IsLocalRing.maximalIdeal _ :=
      congrArg PrimeSpectrum.asIdeal h2
    refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal q.2.ne_top)
      (hunr.trans ?_))
    rw [← h4]
    exact Ideal.map_comap_le
  rw [h3, Scheme.fromSpecStalk_closedPoint]

/-- For an affine open `U` of a Jacobson scheme, the point of `U` at a maximal ideal of
`Γ(X, U)` is a closed point of `X`. -/
lemma IsAffineOpen.isClosed_singleton_of_isMaximal [JacobsonSpace X] {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (hx : (hU.primeIdealOf x).asIdeal.IsMaximal) :
    IsClosed {x.1} := by
  have h1 : IsClosed {hU.primeIdealOf x} :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hx
  have h2 : IsClosed {x} := by
    have e : ({x} : Set U) = hU.isoSpec.hom ⁻¹' {hU.primeIdealOf x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h ↦ h ▸ rfl, fun h ↦ hU.isoSpec.hom.isOpenEmbedding.injective h⟩
    rw [e]
    exact h1.preimage hU.isoSpec.hom.continuous
  have h3 : x ∈ (Subtype.val : U → X) ⁻¹' closedPoints X := by
    rw [U.isOpenEmbedding'.preimage_closedPoints]
    exact h2
  exact h3

/-- **A criterion for closed immersions.** Let `f : X ⟶ Y` be a proper morphism of schemes over
an algebraically closed field `k`, with `X` quasi-compact and locally of finite type over `k`. If
`f` is injective on closed points and unramified at closed points, i.e. `𝔪_{Y, f x}` generates
`𝔪_{X, x}`, then `f` is a closed immersion (compare Hartshorne II.7.3). -/
theorem isClosedImmersion_of_injective_of_le_map_maximalIdeal {k : Type u} [Field k]
    [IsAlgClosed k] (f : X ⟶ Y) [IsProper f] (fX : X ⟶ Spec (.of k)) [LocallyOfFiniteType fX]
    (fY : Y ⟶ Spec (.of k)) (hf : f ≫ fY = fX) [CompactSpace X]
    (hinj : ∀ x y : X, IsClosed {x} → IsClosed {y} → f x = f y → x = y)
    (hunr : ∀ x : X, IsClosed {x} → IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom) :
    IsClosedImmersion f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  have hfib (x : X) (hx : IsClosed {x}) : f ⁻¹' {f x} = {x} :=
    f.preimage_singleton_eq_of_le_map_maximalIdeal f.isClosedMap hx
      (fun y hy hxy ↦ hinj y x hy hx hxy) (hunr x hx)
  have : LocallyQuasiFinite f := by
    rw [← f.quasiFiniteLocus_eq_top_iff]
    by_contra hne
    obtain ⟨x, hxZ, hxcl⟩ := f.quasiFiniteLocus.isOpen.isClosed_compl.exists_closed_singleton
      (by
        rw [Set.nonempty_compl]
        exact fun h ↦ hne (SetLike.coe_injective h))
    exact hxZ (f.mem_quasiFiniteLocus.mpr (f.quasiFiniteAt_of_preimage_singleton (hfib x hxcl)))
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  rw [isClosedImmersion_iff_isAffineHom]
  refine ⟨inferInstance, fun U hU ↦ ?_⟩
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  -- every maximal ideal of `Γ(X, f⁻¹ U)` comes from a closed point
  have hpt (n : Ideal Γ(X, f ⁻¹ᵁ U)) (hn : n.IsMaximal) :
      ∃ x : f ⁻¹ᵁ U, hV.primeIdealOf x = ⟨n, hn.isPrime⟩ ∧ IsClosed {x.1} := by
    obtain ⟨x, hx⟩ := hV.exists_primeIdealOf_eq ⟨n, hn.isPrime⟩
    exact ⟨x, hx, hV.isClosed_singleton_of_isMaximal x (by rw [hx]; exact hn)⟩
  have hcomap (x : f ⁻¹ᵁ U) : (hV.primeIdealOf x).asIdeal.comap (f.app U).hom =
      (hU.primeIdealOf ⟨f x, x.2⟩).asIdeal := by
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU (f ⁻¹ᵁ U) hV le_rfl x.2
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg PrimeSpectrum.asIdeal this
  refine RingHom.surjective_of_finite_of_forall_isMaximal (IsFinite.finite_app f U hU)
    ?_ ?_ ?_
  · intro n hn b
    let ιB : k →+* Γ(X, f ⁻¹ᵁ U) :=
      (fX.appLE ⊤ (f ⁻¹ᵁ U) le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    let ιA : k →+* Γ(Y, U) := (fY.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    have hAB (c : k) : (f.app U).hom (ιA c) = ιB c := by
      simp only [ιA, ιB, RingHom.comp_apply]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      subst hf
      rfl
    have hft : ((Ideal.Quotient.mk n).comp ιB).FiniteType :=
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp
        ((fX.finiteType_appLE (isAffineOpen_top _) hV le_top).comp
          (RingHom.FiniteType.of_surjective _
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2))
    let : Field (Γ(X, f ⁻¹ᵁ U) ⧸ n) := Ideal.Quotient.field n
    have hfin : ((Ideal.Quotient.mk n).comp ιB).Finite := by
      algebraize [((Ideal.Quotient.mk n).comp ιB)]
      exact finite_of_finite_type_of_isJacobsonRing k (Γ(X, f ⁻¹ᵁ U) ⧸ n)
    obtain ⟨c, hc⟩ := (IsAlgClosed.ringHom_bijective_of_isIntegral _ hfin.to_isIntegral).2
      (Ideal.Quotient.mk n b)
    refine ⟨ιA c, ?_⟩
    rw [← Ideal.Quotient.eq, hAB]
    exact hc.symm
  · intro n hn b hb
    obtain ⟨x, hx, hxc⟩ := hpt n hn
    let : Algebra Γ(X, f ⁻¹ᵁ U) (X.presheaf.stalk x.1) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf x
    let : Algebra Γ(Y, U) (Y.presheaf.stalk (f x.1)) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨f x, x.2⟩
    have hX : IsLocalization.AtPrime (X.presheaf.stalk x.1) n := by
      have := hV.isLocalization_stalk x
      rwa [hx] at this
    have hY : IsLocalization.AtPrime (Y.presheaf.stalk (f x.1)) (n.comap (f.app U).hom) := by
      have e : n.comap (f.app U).hom = (hU.primeIdealOf ⟨f x, x.2⟩).asIdeal := by
        rw [← hcomap, hx]
      have e' : (n.comap (f.app U).hom).primeCompl =
          (hU.primeIdealOf ⟨f x, x.2⟩).asIdeal.primeCompl := by
        ext
        simp only [Ideal.mem_primeCompl_iff, e]
      unfold IsLocalization.AtPrime
      rw [e']
      exact hU.isLocalization_stalk ⟨f x, x.2⟩
    have hgerm (a : Γ(Y, U)) : f.stalkMap x.1 (algebraMap _ _ a) =
        algebraMap Γ(X, f ⁻¹ᵁ U) (X.presheaf.stalk x.1) ((f.app U).hom a) := by
      change (Y.presheaf.germ U (f x) x.2 ≫ f.stalkMap x.1) a =
        (f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x x.2) a
      rw [Scheme.Hom.germ_stalkMap]
    have h1 : algebraMap _ (X.presheaf.stalk x.1) b ∈ IsLocalRing.maximalIdeal _ := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal n (X.presheaf.stalk x.1)]
      exact Ideal.mem_map_of_mem _ hb
    have h2 := hunr x hxc h1
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (n.comap (f.app U).hom)
      (Y.presheaf.stalk (f x.1)), Ideal.map_map] at h2
    have h3 : (f.stalkMap x.1).hom.comp (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x.1))) =
        (algebraMap Γ(X, f ⁻¹ᵁ U) (X.presheaf.stalk x.1)).comp (f.app U).hom :=
      RingHom.ext hgerm
    rw [h3, ← Ideal.map_map] at h2
    obtain ⟨⟨a, s⟩, has⟩ := (IsLocalization.mem_map_algebraMap_iff n.primeCompl
      (X.presheaf.stalk x.1)).mp h2
    rw [← map_mul] at has
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists n.primeCompl (X.presheaf.stalk x.1)).mp has
    refine ⟨t * s, n.primeCompl.mul_mem t.2 s.2, ?_⟩
    have : t * s * b = t * a := by rw [← ht]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ a.2
  · intro n n' hn hn' h
    obtain ⟨x, hx, hxc⟩ := hpt n hn
    obtain ⟨x', hx', hxc'⟩ := hpt n' hn'
    have h1 : hU.primeIdealOf ⟨f x, x.2⟩ = hU.primeIdealOf ⟨f x', x'.2⟩ := by
      ext1
      rw [← hcomap, ← hcomap, hx, hx']
      exact h
    have h2 : f x = f x' := by
      have := congrArg hU.fromSpec h1
      rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
    have h3 : x = x' := Subtype.ext (hinj x x' hxc hxc' h2)
    have := congrArg PrimeSpectrum.asIdeal (hx.symm.trans (h3 ▸ hx'))
    exact this

end ClosedImmersion

end AlgebraicGeometry
