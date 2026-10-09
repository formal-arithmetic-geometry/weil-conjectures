/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.PushforwardZero
public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor
public import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Duality
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Birational.RationalMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Local theory of smooth curves and finite morphisms to the projective line

Let `X` be a smooth curve over a field `k`, i.e. `X ⟶ Spec k` is smooth of relative dimension
one. This file collects the inputs of the proof of Serre duality on `X`
(`AlgebraicGeometry.Scheme.serreDuality`): the local rings of `X` at closed points are discrete
valuation rings and closed points are effective Cartier divisors; a rational function `t` on a
proper `X`, transcendental over `k`, defines a finite flat morphism `X ⟶ ℙ¹_k`; along a finite
flat morphism `f : X ⟶ ℙ¹_k` one has the duality `Hom(f_* ℳ, ω_{ℙ¹}) ≅ H⁰(X, ℳᵛ ⊗ ω_X)`; and the
degree of a principal divisor is zero.

## Main statements

- `AlgebraicGeometry.Scheme.isDiscreteValuationRing_stalk_of_isClosed`: the local rings at closed
  points are discrete valuation rings.
- `AlgebraicGeometry.Scheme.isInvertible_vanishingIdeal_of_isClosed`: closed points are effective
  Cartier divisors.
- `AlgebraicGeometry.Scheme.exists_hom_projectiveLine_of_functionField` and
  `AlgebraicGeometry.Scheme.isFinite_flat_of_hom_projectiveLine_of_functionField`: a rational
  function transcendental over `k` is a finite flat morphism to `ℙ¹_k`.
- `AlgebraicGeometry.Scheme.exists_isFinite_flat_hom_projectiveLine`: every smooth proper curve
  has a finite flat morphism to `ℙ¹_k`.
- `AlgebraicGeometry.Scheme.nonempty_homObj_pushforward_iso`: duality along a finite flat
  morphism to `ℙ¹_k`.
- `AlgebraicGeometry.Scheme.nonempty_dual_H_one_iso` and
  `AlgebraicGeometry.Scheme.nonempty_dual_H_zero_iso`: Serre duality on a smooth proper curve in
  degrees `1` and `0`, assembled from the above; they make up
  `AlgebraicGeometry.Scheme.serreDuality`.
- `AlgebraicGeometry.Scheme.finsum_ord_eq_finrank` and
  `AlgebraicGeometry.Scheme.finsum_ord_eq_zero`: degrees of pulled back points and of principal
  divisors.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite IsLocalRing

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Local

variable (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]

include f

/-- The local ring of a smooth curve at a closed point has dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_isClosed {x : X} (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = 1 :=
  ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one f hx

/-- The local ring of a smooth curve at a closed point is a discrete valuation ring: it is a
regular local ring (`AlgebraicGeometry.IsRegular.of_smooth`), in particular a domain, of
dimension one. -/
theorem isDiscreteValuationRing_stalk_of_isClosed {x : X} (hx : IsClosed {x}) :
    ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
  have := SmoothOfRelativeDimension.smooth 1 f
  have := IsRegular.of_smooth f
  ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing _
    (ringKrullDim_stalk_eq_one_of_isClosed f hx)⟩

/-- **Local regularity of smooth curves.** The local rings of a smooth curve over a field are
regular local rings, hence domains, and at closed points they are discrete valuation rings.

(blueprint: `rem-pc-regularity-sc`) -/
theorem isRegularLocalRing_stalk_and_isDiscreteValuationRing (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) ∧ ∃ _ : IsDomain (X.presheaf.stalk x),
      IsClosed {x} → IsDiscreteValuationRing (X.presheaf.stalk x) :=
  have := SmoothOfRelativeDimension.smooth 1 f
  have := IsRegular.of_smooth f
  ⟨inferInstance, inferInstance, fun hx ↦ by
    obtain ⟨_, h⟩ := isDiscreteValuationRing_stalk_of_isClosed f hx
    exact h⟩

/-- **Closed points are Cartier divisors on smooth curves.** A closed point `x` of a smooth
curve, with its reduced structure, is an effective Cartier divisor: its ideal sheaf is locally
generated by one non-zerodivisor, a uniformizer of the discrete valuation ring `𝒪_{X,x}`.
Consequently every effective divisor, a finite sum of closed points, is an effective Cartier
divisor.

(blueprint: `lem-sc-point-cartier`) -/
theorem isInvertible_vanishingIdeal_of_isClosed {x : X} (hx : IsClosed {x}) :
    (IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).IsInvertible :=
  isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one f hx

/-- **Closed points of curves are Cartier divisors.** A closed point `x` of a smooth curve has
invertible ideal sheaf, and `𝒪_{X,x}` is a discrete valuation ring.

(blueprint: `rem-pc-closed-point-cartier-sc`) -/
theorem isInvertible_vanishingIdeal_and_isDiscreteValuationRing {x : X} (hx : IsClosed {x}) :
    (IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).IsInvertible ∧
      ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
  ⟨isInvertible_vanishingIdeal_of_isClosed f hx, isDiscreteValuationRing_stalk_of_isClosed f hx⟩

/-- The local rings of a smooth curve over a field are valuation rings: discrete valuation rings
at closed points and fields at generic points. -/
theorem valuationRing_stalk [IsIntegral X] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := IsRegular.of_smooth f
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim x).trans
      (by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension f 1)
  by_cases h1 : ringKrullDim (X.presheaf.stalk x) = 1
  · have := IsRegularLocalRing.isDiscreteValuationRing _ h1
    infer_instance
  · have h0 : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
      generalize ringKrullDim (X.presheaf.stalk x) = d at *
      induction d using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe n =>
        induction n using ENat.recTopCoe with
        | top => exact absurd hle (by decide)
        | coe m =>
          have : m ≤ 1 := by exact_mod_cast hle
          have : m ≠ 1 := fun h ↦ h1 (by rw [h]; rfl)
          have : m = 0 := by omega
          subst this; rfl
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := ⟨by exact_mod_cast h0⟩
    let := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    infer_instance

end Local

/-- The ring map `k →+* k(X)` of an integral `k`-scheme `X`. -/
noncomputable abbrev functionFieldRingHom (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsIntegral X] : k →+* X.functionField :=
  (X.germToFunctionField ⊤ (h := ⟨⟨genericPoint X, trivial⟩⟩)).hom.comp
    (globalSectionsRingHom k (X := X))

/-- An integral scheme over a field `k` with a point whose local ring is not a field has a
rational function transcendental over `k`. -/
theorem exists_transcendental_functionField [X.Over (Spec (.of k))] [IsIntegral X] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) ≠ 0) :
    ∃ t : X.functionField, letI := (functionFieldRingHom k X).toAlgebra; Transcendental k t := by
  let := (functionFieldRingHom k X).toAlgebra
  let : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ ⊤ x trivial).hom.comp (globalSectionsRingHom k (X := X))).toAlgebra
  by_contra! h
  have : Algebra.IsAlgebraic k X.functionField := ⟨fun t ↦ not_not.mp (h t)⟩
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) :=
    IsFractionRing.injective _ _
  have : Algebra.IsAlgebraic k (X.presheaf.stalk x) :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq (RingHom.id k)
      (algebraMap (X.presheaf.stalk x) X.functionField) Function.surjective_id hinj (by
        ext a
        simp only [RingHom.algebraMap_toAlgebra, functionFieldRingHom, RingHom.coe_comp,
          RingHom.coe_coe, RingHom.coe_id, Function.comp_apply, id_eq]
        rw [← CommRingCat.comp_apply]
        erw [TopCat.Presheaf.germ_stalkSpecializes])
  have hfield : IsField (X.presheaf.stalk x) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k _).injective).mp (Field.toIsField k)
  exact hx (ringKrullDim_eq_zero_of_isField hfield)

/-- In an irreducible scheme of dimension at most one, a point which is not closed is the
generic point. -/
theorem eq_genericPoint_of_not_isClosed {Z : Scheme.{u}} [IrreducibleSpace Z]
    (h : topologicalKrullDim Z ≤ 1) {z : Z} (hz : ¬ IsClosed {z}) : z = genericPoint Z := by
  have : closure {z} = (Set.univ : Set Z) := by
    by_contra hne
    exact hz (IsOpen.isClosed_singleton_of_mem_compl h isClosed_closure.isOpen_compl
      (Set.nonempty_compl.mpr hne) fun hmem ↦ hmem (subset_closure rfl))
  exact (show IsGenericPoint z ⊤ from this).eq (genericPoint_spec Z)

/-- The stalk maps of an integral scheme along specializations are injective. -/
theorem injective_stalkSpecializes {Z : Scheme.{u}} [IsIntegral Z] {a b : Z} (h : a ⤳ b) :
    Function.Injective (Z.presheaf.stalkSpecializes h) := by
  have hinj := IsFractionRing.injective (Z.presheaf.stalk b) Z.functionField
  have e := TopCat.Presheaf.stalkSpecializes_comp Z.presheaf
    ((genericPoint_spec Z).specializes trivial) h
  refine fun u v huv ↦ hinj ?_
  change Z.presheaf.stalkSpecializes _ u = Z.presheaf.stalkSpecializes _ v
  rw [← e, CommRingCat.comp_apply, CommRingCat.comp_apply, huv]

section ProjectiveLine

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- The homogeneous coordinates `[1 : t]` of a rational function `t`, as global sections of
`Spec k(X)`: the `k(X)`-point of `ℙ¹` with affine coordinate `t`. -/
noncomputable abbrev functionFieldCoordinates [IsIntegral X] (t : X.functionField) :
    ULift.{u} (Fin 2) → Γ(Spec X.functionField, ⊤) :=
  fun i ↦ (Scheme.ΓSpecIso X.functionField).inv (![1, t] i.down)

/-- **Rational functions define morphisms to `ℙ¹`.** Let `X` be a proper smooth integral curve
over `k` and `t ∈ k(X)` transcendental over `k`. Then there is a morphism `π_t : X ⟶ ℙ¹_k` over
`k` with `π_t^* (x₁ / x₀) = t`: at the generic point it is the point `[1 : t]` of `ℙ¹(k(X))`. On
an affine open `Spec A` of `X` one writes `t = a / b` with `(a, b) = A`, using that the local
rings at closed points are discrete valuation rings, and maps `x₀ ↦ b`, `x₁ ↦ a`; these glue since
`ℙ¹_k` is separated.

(blueprint: `lem-sc-rational-function-morphism`) -/
theorem exists_hom_projectiveLine_of_functionField [IsIntegral X] (t : X.functionField)
    (ht : letI := (functionFieldRingHom k X).toAlgebra; Transcendental k t) :
    ∃ π : X ⟶ ProjectiveLine (Spec (.of k)), π.IsOver (Spec (.of k)) ∧
      ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
        (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (functionFieldCoordinates t) hs := by
  have hs : Ideal.span (Set.range (functionFieldCoordinates (X := X) t)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) (by simp)
  have : (ProjectiveLine (Spec (.of k))).IsSeparated :=
    ⟨by rw [← terminal.comp_from (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))]
        infer_instance⟩
  obtain ⟨π, hπ, h⟩ := exists_hom_of_valuationRing_stalk (S := Spec (.of k))
    (valuationRing_stalk (X ↘ Spec (.of k)))
    (ProjectiveSpace.homOfSections (X.fromSpecFunctionField ≫ X ↘ Spec (.of k))
      (functionFieldCoordinates t) hs) (ProjectiveSpace.homOfSections_over _ _ _)
  exact ⟨π, hπ, fun _ ↦ h⟩

/-- **Rational functions define finite morphisms to `ℙ¹`.** Let `X` be a proper smooth integral
curve over `k`, `t ∈ k(X)` transcendental over `k`, and `π_t : X ⟶ ℙ¹_k` the morphism of
`exists_hom_projectiveLine_of_functionField`. Then `π_t` is finite, surjective and flat, of
degree `[k(X) : k(t)]`. It is surjective since its image is closed and not a point; its fibres
are finite, so it is finite; and `π_* 𝒪_X` is torsion free on the smooth curve `ℙ¹_k`, hence
locally free, so `π_t` is flat.

(blueprint: `lem-sc-morphism-from-function`) -/
theorem isFinite_flat_of_hom_projectiveLine_of_functionField [IsIntegral X]
    (t : X.functionField) (ht : letI := (functionFieldRingHom k X).toAlgebra; Transcendental k t)
    (π : X ⟶ ProjectiveLine (Spec (.of k))) [π.IsOver (Spec (.of k))]
    (hπ : ∀ hs, X.fromSpecFunctionField ≫ π = ProjectiveSpace.homOfSections
      (X.fromSpecFunctionField ≫ X ↘ Spec (.of k)) (functionFieldCoordinates t) hs) :
    IsFinite π ∧ Surjective π ∧ Flat π ∧
      ∀ y, π.finrank y = Module.finrank
        (Subfield.closure (Set.range (functionFieldRingHom k X) ∪ {t})) X.functionField := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let P := ProjectiveLine (Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  have hdimX : topologicalKrullDim X ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1
  have hdimP : topologicalKrullDim P ≤ 1 := topologicalKrullDim_projectiveLine_le_one k
  have hover : π ≫ P ↘ Spec (.of k) = X ↘ Spec (.of k) :=
    HomIsOver.comp_over (f := π) (S := Spec (.of k))
  have : IsProper π := by
    have : IsProper (π ≫ P ↘ Spec (.of k)) := by rw [hover]; infer_instance
    exact IsProper.of_comp π (P ↘ Spec (.of k))
  -- `π` maps the generic point of `X` to the generic point of `ℙ¹`.
  have hg₀ : X.fromSpecFunctionField ≫ X ↘ Spec (.of k) =
      Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext a
    simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, functionFieldRingHom,
      globalSectionsRingHom]
    rfl
  have hs : Ideal.span (Set.range (functionFieldCoordinates (X := X) t)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) (by simp)
  have hpt : ProjectiveSpace.homOfSections (Spec.map (CommRingCat.ofHom (functionFieldRingHom k X)))
      (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of X.functionField)).inv (![1, t] i.down)) hs
      (IsLocalRing.closedPoint X.functionField) = π (genericPoint X) := by
    have e := hπ hs
    rw [hg₀] at e
    refine (congrArg (fun f ↦ f (IsLocalRing.closedPoint X.functionField)) e).symm.trans ?_
    exact congrArg π Scheme.fromSpecStalk_closedPoint
  have hηc : ¬ IsClosed {π (genericPoint X)} := by
    rw [← hpt]
    exact ProjectiveLine.not_isClosed_homOfSections (functionFieldRingHom k X) t ht hs _
  have hηP : π (genericPoint X) = genericPoint P := eq_genericPoint_of_not_isClosed hdimP hηc
  -- the points of `X` and `ℙ¹` are closed or generic
  have hptX (x : X) (hx : ¬ IsClosed {x}) : x = genericPoint X :=
    eq_genericPoint_of_not_isClosed hdimX hx
  have hptP (y : P) (hy : ¬ IsClosed {y}) : y = genericPoint P :=
    eq_genericPoint_of_not_isClosed hdimP hy
  have hPgen : ¬ IsClosed ({genericPoint P} : Set P) := hηP ▸ hηc
  have hsurj : Surjective π := by
    refine ⟨fun y ↦ ?_⟩
    have hclosed : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have : closure {genericPoint P} ⊆ Set.range π :=
      closure_minimal (by rintro _ rfl; exact ⟨_, hηP⟩) hclosed
    rw [show closure ({genericPoint P} : Set P) = Set.univ from genericPoint_spec P] at this
    exact this trivial
  have hfib (y : P) : (π ⁻¹' {y}).Finite := by
    by_cases hy : IsClosed ({y} : Set P)
    · have hc : IsClosed (π ⁻¹' {y}) := hy.preimage π.continuous
      have hη : genericPoint X ∉ π ⁻¹' {y} := by
        intro h
        rw [Set.mem_preimage, Set.mem_singleton_iff, hηP] at h
        exact hPgen (h ▸ hy)
      have := IsOpen.finite_compl_of_topologicalKrullDim_le_one hdimX hc.isOpen_compl
        ⟨_, hη⟩
      simpa using this
    · refine (Set.finite_singleton (genericPoint X)).subset fun x hx ↦ ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      refine hptX x fun hxc ↦ hy ?_
      rw [← hx, ← Set.image_singleton]
      exact π.isClosedMap _ hxc
  have : LocallyQuasiFinite π := (locallyQuasiFinite_iff_finite_preimage_singleton).mpr hfib
  have hfin : IsFinite π := IsFinite.of_isProper_of_locallyQuasiFinite π
  have hflat : Flat π := by
    refine Flat.of_stalkMap π fun x ↦ ?_
    have hval := valuationRing_stalk (P ↘ Spec (.of k)) (π x)
    have hinj : Function.Injective (π.stalkMap x) := by
      have h₁ := Scheme.Hom.stalkSpecializes_stalkMap π (genericPoint X) x
        ((genericPoint_spec X).specializes (Set.mem_univ x))
      have hF : IsField (P.presheaf.stalk (π (genericPoint X))) :=
        hηP ▸ Field.toIsField P.functionField
      have h₂ : Function.Injective (P.presheaf.stalkSpecializes
          (π.base.hom.map_specializes ((genericPoint_spec X).specializes (Set.mem_univ x))) ≫
            π.stalkMap (genericPoint X)) := by
        let := hF.toField
        exact (RingHom.injective (π.stalkMap (genericPoint X)).hom).comp
          (injective_stalkSpecializes _)
      rw [h₁] at h₂
      exact fun a b hab ↦ h₂ (by rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hab])
    algebraize [(π.stalkMap x).hom]
    change Module.Flat (P.presheaf.stalk (π x)) (X.presheaf.stalk x)
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun m ⟨⟨r, hr⟩, hrm⟩ ↦ ?_
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap (P.presheaf.stalk (π x)) (X.presheaf.stalk x) r ≠ 0 := by
      exact fun h ↦ hr0 (hinj (h.trans (π.stalkMap x).hom.map_zero.symm))
    rw [Submonoid.smul_def, Algebra.smul_def] at hrm
    exact (mul_eq_zero.mp hrm).resolve_left this
  refine ⟨hfin, hsurj, hflat, fun y ↦ ?_⟩
  sorry

/-- **Finite flat morphisms to the projective line.** Every smooth proper curve `X` over `k` has
a finite flat morphism `X ⟶ ℙ¹_k` over `k`. Each connected component of `X` is integral
(`AlgebraicGeometry.IsRegular.irreducibleSpace`) of dimension one, so its function field has a
transcendental element `t`, and `π_t` is finite flat
(`isFinite_flat_of_hom_projectiveLine_of_functionField`); there are finitely many components,
and the morphisms on the components glue. -/
theorem exists_isFinite_flat_hom_projectiveLine :
    ∃ f : X ⟶ ProjectiveLine (Spec (.of k)), f.IsOver (Spec (.of k)) ∧ IsFinite f ∧ Flat f ∧
      LocallyOfFinitePresentation f := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let U : ConnectedComponents X → X.Opens := fun c ↦ ⟨ConnectedComponents.mk ⁻¹' {c}, by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hUc (c) : IsClosed (U c : Set X) :=
    isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have key (c) : ∃ g : (U c).toScheme ⟶ ProjectiveLine (Spec (.of k)),
      g ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = (U c).ι ≫ X ↘ Spec (.of k) ∧
        IsFinite g ∧ Flat g := by
    let : (U c).toScheme.Over (Spec (.of k)) := ⟨(U c).ι ≫ X ↘ Spec (.of k)⟩
    have : SmoothOfRelativeDimension 1 ((U c).toScheme ↘ Spec (.of k)) := by
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((U c).ι ≫ X ↘ Spec (.of k)))
    have : IsClosedImmersion (U c).ι :=
      .of_isPreimmersion _ ((U c).range_ι ▸ hUc c)
    have : IsProper ((U c).toScheme ↘ Spec (.of k)) := by
      change IsProper ((U c).ι ≫ X ↘ Spec (.of k))
      infer_instance
    have : ConnectedSpace (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      have h : (U (ConnectedComponents.mk x) : Set X) = connectedComponent x :=
        connectedComponents_preimage_singleton
      exact isConnected_iff_connectedSpace.mp (h ▸ isConnected_connectedComponent)
    have := SmoothOfRelativeDimension.smooth 1 ((U c).toScheme ↘ Spec (.of k))
    have : CompactSpace (U c) := isCompact_iff_compactSpace.mp (hUc c).isCompact
    have := IsRegular.of_smooth ((U c).toScheme ↘ Spec (.of k))
    have := IsRegular.irreducibleSpace (U c).toScheme
    have : IsReduced (U c).toScheme := isReduced_of_isReduced_stalk _
    have : Nonempty (U c) := by
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      exact ⟨⟨x, rfl⟩⟩
    have : IsIntegral (U c).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton (X := (U c).toScheme)
      Set.univ_nonempty
    obtain ⟨t, ht⟩ := exists_transcendental_functionField (k := k) x (by
      rw [ringKrullDim_stalk_eq_one_of_isClosed ((U c).toScheme ↘ Spec (.of k)) hx]
      exact one_ne_zero)
    obtain ⟨π, hπ, hπ'⟩ := exists_hom_projectiveLine_of_functionField t ht
    obtain ⟨h₁, -, h₂, -⟩ := isFinite_flat_of_hom_projectiveLine_of_functionField t ht π hπ'
    exact ⟨π, hπ.comp_over, h₁, h₂⟩
  choose g hg hfin hflat using key
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U <| eq_top_iff.2 fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨ConnectedComponents.mk x, rfl⟩
  have hcompat (c d) : pullback.fst (𝒰.f c) (𝒰.f d) ≫ g c = pullback.snd _ _ ≫ g d := by
    by_cases hcd : c = d
    · subst hcd
      have : pullback.fst (𝒰.f c) (𝒰.f c) = pullback.snd _ _ :=
        (cancel_mono (𝒰.f c)).1 pullback.condition
      rw [this]
    · have : IsEmpty (Limits.pullback (𝒰.f c) (𝒰.f d) : Scheme) := by
        refine ⟨fun z ↦ hcd ?_⟩
        have h₁ := ((pullback.fst (𝒰.f c) (𝒰.f d)) z).2
        have h₂ := ((pullback.snd (𝒰.f c) (𝒰.f d)) z).2
        have h : 𝒰.f c (pullback.fst (𝒰.f c) (𝒰.f d) z) =
            𝒰.f d (pullback.snd (𝒰.f c) (𝒰.f d) z) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
        simp only [𝒰, Scheme.openCoverOfIsOpenCover_f] at h
        exact h₁.symm.trans ((congrArg ConnectedComponents.mk h).trans h₂)
      exact isInitialOfIsEmpty.hom_ext _ _
  let f := 𝒰.glueMorphisms g hcompat
  have hf (c) : (U c).ι ≫ f = g c := 𝒰.ι_glueMorphisms g hcompat c
  have hover : f ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k) = X ↘ Spec (.of k) :=
    𝒰.hom_ext _ _ fun c ↦ by
      simp only [𝒰, Scheme.openCoverOfIsOpenCover_f]
      rw [reassoc_of% (hf c), hg]
  have : IsProper (f ≫ ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hover]; infer_instance
  have : IsProper f := IsProper.of_comp f (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : LocallyQuasiFinite f :=
    IsZariskiLocalAtSource.of_openCover 𝒰 fun c ↦ by
      simp only [𝒰, Scheme.openCoverOfIsOpenCover_f]
      rw [hf]; infer_instance
  have : Flat f :=
    IsZariskiLocalAtSource.of_openCover 𝒰 fun c ↦ by
      simp only [𝒰, Scheme.openCoverOfIsOpenCover_f]
      rw [hf]; infer_instance
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  exact ⟨f, ⟨hover⟩, inferInstance, inferInstance,
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance⟩


end ProjectiveLine

section FiniteDuality

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **Trace identification along a finite flat morphism to `ℙ¹`.** Let `X` be a smooth curve
over `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. There is a trace map
`τ : f_* Ω¹_{X/k} ⟶ Ω¹_{ℙ¹_k/k}` such that `f_* Ω¹_{X/k} ⟶ Hom(f_* 𝒪_X, Ω¹_{ℙ¹_k/k})`,
`ω ↦ (a ↦ τ(a ω))`, is an isomorphism: the comparison `φ ↦ τ ∘ f_* φ` for `ℳ = 𝒪_X`. Locally
over `Spec R ⊆ ℙ¹_k` with `f⁻¹(Spec R) = Spec B` this is `Ω¹_{B/k} ≅ Hom_R(B, Ω¹_{R/k})`, the
codifferent of the finite flat extension `R ⊆ B` of Dedekind domains, i.e. Grothendieck duality
`f^! Ω¹_{ℙ¹} ≅ Ω¹_{X/k}` for `f`.

(blueprint: `lem-sc-finite-duality`, the trace identification) -/
theorem exists_isIso_pushforwardHomObjComparison_unit (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f] :
    ∃ τ : (Modules.pushforward f).obj (X ↘ Spec (.of k)).relativeDifferentials ⟶
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials,
      IsIso (Modules.pushforwardHomObjComparison f τ (SheafOfModules.unit X.ringCatSheaf)) :=
  sorry

/-- **Duality along a finite flat morphism to `ℙ¹`, comparison map.** Let `X` be a smooth curve
over `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. There is a trace map
`τ : f_* Ω¹_{X/k} ⟶ Ω¹_{ℙ¹_k/k}` such that `f_* Hom(ℳ, Ω¹_{X/k}) ⟶ Hom(f_* ℳ, Ω¹_{ℙ¹_k/k})`,
`φ ↦ τ ∘ f_* φ`, is an isomorphism for every finite locally free `ℳ`. For `ℳ = 𝒪_X` this is the
trace identification `exists_isIso_pushforwardHomObjComparison_unit`; the general case follows
since `ℳ` is a direct summand of a free module of finite rank over the affine opens `f⁻¹V`
(`Modules.isIso_pushforwardHomObjComparison_of_isIso_unit`).

(blueprint: `lem-sc-finite-duality`, the sheaf-level statement) -/
theorem exists_isIso_pushforwardHomObjComparison (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f] :
    ∃ τ : (Modules.pushforward f).obj (X ↘ Spec (.of k)).relativeDifferentials ⟶
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials,
      ∀ ℳ : X.Modules, ℳ.IsFiniteLocallyFree →
        IsIso (Modules.pushforwardHomObjComparison f τ ℳ) := by
  obtain ⟨τ, hτ⟩ := exists_isIso_pushforwardHomObjComparison_unit f
  exact ⟨τ, fun ℳ _ ↦ Modules.isIso_pushforwardHomObjComparison_of_isIso_unit hτ ℳ⟩

/-- **Duality along a finite flat morphism to `ℙ¹`, sheaf-level.** Let `X` be a smooth curve
over `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. Then
`Hom_{𝒪_{ℙ¹}}(f_* ℳ, Ω¹_{ℙ¹_k/k}) ≅ f_* Hom_{𝒪_X}(ℳ, Ω¹_{X/k})` as sheaves of modules on `ℙ¹_k`,
naturally in finite locally free `ℳ`: the isomorphism `φ ↦ τ ∘ f_* φ` of
`exists_isIso_pushforwardHomObjComparison`.

(blueprint: `lem-sc-finite-duality`, the sheaf-level statement) -/
theorem nonempty_homObj_pushforward_iso_pushforward_homObj (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f] :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.pushforward f).op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (SheafOfModules.homFunctor X.sheaf).flip.obj (X ↘ Spec (.of k)).relativeDifferentials ⋙
          Modules.pushforward f) := by
  obtain ⟨τ, hτ⟩ := exists_isIso_pushforwardHomObjComparison f
  have (ℳ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategoryᵒᵖ) :
      IsIso ((Functor.whiskerLeft (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
        (Modules.pushforwardHomObjComparisonNatTrans f τ)).app ℳ) :=
    hτ ℳ.unop.obj ℳ.unop.property
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft
    (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
    (Modules.pushforwardHomObjComparisonNatTrans f τ))
  exact ⟨(asIso (Functor.whiskerLeft (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
    (Modules.pushforwardHomObjComparisonNatTrans f τ))).symm⟩

/-- **Duality along a finite flat morphism to `ℙ¹`.** Let `X` be a smooth curve over `k` and
`f : X ⟶ ℙ¹_k` a finite flat morphism over `k`. Then
`Hom_{𝒪_{ℙ¹}}(f_* ℳ, Ω¹_{ℙ¹_k/k}) ≅ H⁰(X, ℳᵛ ⊗ Ω¹_{X/k})`, naturally in finite locally free
`ℳ`. Taking global sections in `nonempty_homObj_pushforward_iso_pushforward_homObj` gives
`Hom(f_* ℳ, Ω¹_{ℙ¹}) ≅ H⁰(ℙ¹, f_* Hom(ℳ, Ω¹_{X/k})) = H⁰(X, Hom(ℳ, Ω¹_{X/k}))`
(`Modules.pushforwardCompCohomologyFunctorZeroIso`), and `Hom(ℳ, Ω¹_{X/k}) ≅ ℳᵛ ⊗ Ω¹_{X/k}`
since `Ω¹_{X/k}` is invertible (`Modules.dualTensorHomIso`).

(blueprint: `lem-sc-finite-duality`) -/
theorem nonempty_homObj_pushforward_iso (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f] :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.pushforward f).op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⋙
        Modules.cohomologyFunctor k 0 ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k 0) := by
  obtain ⟨E⟩ := nonempty_homObj_pushforward_iso_pushforward_homObj f
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  exact ⟨Functor.isoWhiskerRight E (Modules.cohomologyFunctor k 0) ≪≫
    Functor.isoWhiskerLeft ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
      (SheafOfModules.homFunctor X.sheaf).flip.obj (X ↘ Spec (.of k)).relativeDifferentials)
      (Modules.pushforwardCompCohomologyFunctorZeroIso k f) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op
      (Functor.isoWhiskerRight (Modules.dualTensorHomIso (X ↘ Spec (.of k)).relativeDifferentials)
        (Modules.cohomologyFunctor k 0)).symm⟩

end FiniteDuality

section Divisors

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsAlgClosed k]

/-- **Degree of pullbacks of divisors.** Let `π : X ⟶ Y` be a finite flat morphism of proper
smooth integral curves over an algebraically closed field `k`, of degree `d`, so that `π_* 𝒪_X`
is locally free of rank `d`. Let `y` be a closed point of `Y` with uniformizer `t`, a section on
an open `V ∋ y` whose germ generates the maximal ideal of `𝒪_{Y,y}`. Then the pullback divisor
`π^*[y] = ∑_{π(x) = y} v_x(π^* t) [x]` has degree `d`. By linearity `deg π^* D = d · deg D` for
every divisor `D` on `Y`.

(blueprint: `lem-sc-pullback-degree`) -/
theorem finsum_ord_eq_finrank [IsIntegral X] [IsLocallyNoetherian X] {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    [IsProper (Y ↘ Spec (.of k))] [IsIntegral Y] (π : X ⟶ Y) [π.IsOver (Spec (.of k))]
    [IsFinite π] [Flat π] {y : Y} (hy : IsClosed {y}) {V : Y.Opens} (hyV : y ∈ V)
    (t : Γ(Y, V))
    (ht : maximalIdeal (Y.presheaf.stalk y) = Ideal.span {Y.presheaf.germ V y hyV t}) :
    ∑ᶠ (x : X) (hx : π.base x = y), X.ord (algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ (π ⁻¹ᵁ V) x (show π.base x ∈ V from hx ▸ hyV) (π.app V t))) x =
      π.finrank (genericPoint Y) :=
  sorry

variable (k X) in
include k in
/-- **Principal divisors have degree zero.** For a nonzero rational function `f` on a proper
smooth integral curve over an algebraically closed field `k`,
`deg div(f) = ∑_x v_x(f) = 0`. For `f ∉ k` this is `div(f) = π_f^*([0] - [∞])` for the finite
flat morphism `π_f : X ⟶ ℙ¹_k` of degree `d`, whose degree is `d - d = 0`.

(blueprint: `lem-sc-deg-principal-zero`) -/
theorem finsum_ord_eq_zero [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField}
    (hf : f ≠ 0) : ∑ᶠ x : X, X.ord f x = 0 :=
  sorry

end Divisors

section Duality

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- **Serre duality on a curve, `q = 1`.** On a smooth proper curve `X` over `k`, with
`ω = Ω¹_{X/k}`, there is an isomorphism `H¹(X, ℳ)^∨ ≅ H⁰(X, ℳᵛ ⊗ ω)`, natural in finite locally
free `ℳ`. Choose a finite flat `f : X ⟶ ℙ¹_k` (`exists_isFinite_flat_hom_projectiveLine`); then
`H¹(X, ℳ) ≅ H¹(ℙ¹_k, f_* ℳ)` since `f` is affine, `H¹(ℙ¹_k, f_* ℳ)^∨ ≅ Hom(f_* ℳ, ω_{ℙ¹})` by
duality on `ℙ¹_k` (`f_* ℳ` is finite locally free, hence coherent), and
`Hom(f_* ℳ, ω_{ℙ¹}) ≅ H⁰(X, ℳᵛ ⊗ ω)` by duality along `f`.

(blueprint: `thm-sc-serre-duality-curve`, case `q = n = 1`) -/
theorem nonempty_dual_H_one_iso :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k 0) := by
  obtain ⟨f, _, _, _, _⟩ := exists_isFinite_flat_hom_projectiveLine (k := k) (X := X)
  obtain ⟨T⟩ := Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k f 1
  obtain ⟨D⟩ := ProjectiveLine.nonempty_dual_H_one_iso k
  obtain ⟨E⟩ := nonempty_homObj_pushforward_iso f
  let L₁ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ObjectProperty.lift _ (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι fun ℱ ↦ by
      have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
      exact inferInstanceAs ℱ.obj.IsQuasicoherent
  let L₂ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory ⥤
      (Modules.isCoherent (ProjectiveLine (Spec (.of k)))).FullSubcategory :=
    ObjectProperty.lift _
      ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙ Modules.pushforward f)
      fun ℱ ↦ by
        have : ℱ.obj.IsFiniteLocallyFree := ℱ.property
        let 𝒢 := (Modules.pushforward f).obj ℱ.obj
        have := Modules.isFiniteLocallyFree_pushforward f ℱ.obj
        exact ⟨SheafOfModules.instIsQuasicoherentOfIsLocallyFree 𝒢,
          SheafOfModules.IsFiniteLocallyFree.isFinitePresentation 𝒢⟩
  -- `H¹(X, ℳ)^∨ ≅ H¹(ℙ¹, f_* ℳ)^∨ ≅ Hom(f_* ℳ, ω_{ℙ¹}) ≅ H⁰(X, ℳᵛ ⊗ ω)`
  exact ⟨Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft L₁ T).symm)
    (ModuleCat.dualFunctor k) ≪≫ Functor.isoWhiskerLeft L₂.op D ≪≫ E⟩

/-- **Serre duality on a curve, `q = 0`.** On a smooth proper curve `X` over `k`, with
`ω = Ω¹_{X/k}`, there is an isomorphism `H⁰(X, ℳ)^∨ ≅ H¹(X, ℳᵛ ⊗ ω)`, natural in finite locally
free `ℳ`. Apply `nonempty_dual_H_one_iso` to `𝒩 = ℳᵛ ⊗ ω` and use `(ℳᵛ ⊗ ω)ᵛ ⊗ ω ≅ ℳ` (`ω` is
invertible) to get `H¹(X, 𝒩)^∨ ≅ H⁰(X, ℳ)`; then dualise, `H¹(X, 𝒩)` being finite-dimensional.

(blueprint: `thm-sc-serre-duality-curve`, reduction to `q = n`) -/
theorem nonempty_dual_H_zero_iso :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k 1) := by
  obtain ⟨E⟩ := nonempty_dual_H_one_iso (k := k) (X := X)
  have := Hom.isInvertible_relativeDifferentials (X ↘ Spec (.of k))
  obtain ⟨B⟩ := Modules.nonempty_iso_dual_tensorObj_dual_tensorObj
    (X ↘ Spec (.of k)).relativeDifferentials
  let D := Modules.dualTensorFunctor (X ↘ Spec (.of k)).relativeDifferentials
  -- `H¹(ℱᵛ ⊗ ω)^∨ ≅ H⁰(ℱ)`, naturally in `ℱ`.
  let G : opOp _ ⋙ D.op ⋙ ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
      (Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k) ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙ Modules.cohomologyFunctor k 0 :=
    Functor.isoWhiskerLeft (opOp _ ⋙ D.op) E ≪≫
      (Functor.isoWhiskerRight B (Modules.cohomologyFunctor k 0)).symm
  have hfin (ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategoryᵒᵖ) :
      FiniteDimensional k ((D ⋙ (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙
        Modules.cohomologyFunctor k 1).obj ℱ) := by
    have : (D.obj ℱ).obj.IsFiniteLocallyFree := (D.obj ℱ).property
    have := SheafOfModules.IsFiniteLocallyFree.isFinitePresentation (D.obj ℱ).obj
    have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree (D.obj ℱ).obj
    exact Modules.finiteDimensional_H_of_isProper (D.obj ℱ).obj 1
  exact ⟨Functor.isoWhiskerRight (NatIso.op G) (ModuleCat.dualFunctor k) ≪≫
    ModuleCat.dualDualIso (D ⋙ (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι ⋙
      Modules.cohomologyFunctor k 1)⟩

end Duality

end AlgebraicGeometry.Scheme
