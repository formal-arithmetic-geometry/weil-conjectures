/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.PoincareDuality.Biduality.CoefficientChangeBraided
public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.TraceFormula.CoefficientMorphism
public import WeilConjectures.TraceFormula.IntegralCoefficientComparison
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

/-!

# The integral trace formula

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, `Φ` the model Frobenius
of `X = X₀ ×_{k₀} k`, `K` a bounded constructible `𝒪_E`-complex on `X` and `θ : LΦ^* K ⟶ K` an
arbitrary morphism (an integral Frobenius correspondence). The *integral trace formula*
states that for every `m ≥ 1`
```
tr_{𝒪_E}(T_{c_m}(θ_m) | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr_{𝒪_E}(θ_{m,x} | K_x)
```
(`ProEtale.CondensedRing.PadicIntegersRingObj.trace_frobeniusCompactOperator_eq_sum`), both sides
being categorical traces in `Dᵇc(Spec k)⟦𝒪_E⟧`.

## Implementation details

One can deduce the integral formula from the formula with finite coefficients `𝒪_E ⧸ πⁿ` by
reduction. In this library the trace formula for Frobenius correspondences is proved directly
with `ℚ̄_ℓ`-coefficients (`ProEtale.CondensedRing.trace_frobeniusCompactOperator_eq_sum`), so the
integral formula is deduced from it by the extension of scalars
`T = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` (`ProEtale.CondensedRing.boundedConstructibleIntegersToPadicAlgCl`) instead:

* `T` is braided monoidal on the point, so it carries traces to traces through the ring map
  `ρ_T : End(𝟙) ⟶ End(𝟙)` it induces on the endomorphisms of the units
  (`CategoryTheory.Functor.trace_eq_unitEndRingHom_trace`); on the separably closed point this
  map is the inclusion `𝒪_E ⊆ ℚ̄_ℓ`, hence injective
  (`ProEtale.CondensedRing.injective_unitEndRingHom_boundedConstructibleIntegersToPadicAlgCl`);
* `T` commutes with `RΓ_c`, with the pullbacks and with the operators `h^♯`
  (`ProEtale.CondensedRing.integersToPadicAlgCl_map_compactPullback_app`), so it carries the
  global operator and the stalk maps of `θ` to those of the `ℚ̄_ℓ`-coefficient map `ψ = T θ`.

Applying `ρ_T` to both sides of the integral formula therefore gives the two sides of the
`ℚ̄_ℓ`-formula for `(T K, ψ)`.

The instance `ProEtale.CondensedRing.additive_constructibleToPadicAlgCl` takes the instances on
the derived categories from the functor, to avoid an expensive search.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `ℚ̄_ℓ`.
set_option quotPrecheck false in
local notation "ℚ̄" => Profinite.padicAlgClRingObj ℓ

-- The extension of scalars `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -`.
set_option quotPrecheck false in
local notation "𝐓" => boundedConstructibleIntegersToPadicAlgCl ℓ E


/-! ### Braided monoidal structure and the scalars of the point -/

section Monoidal

attribute [local instance] boundedConstructibleBraiding
  PadicIntegersRingObj.boundedConstructibleBraiding

attribute [local instance] DerivedCategory.braidedCategory' in
/-- The extension of scalars `T_X = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` is a braided monoidal functor for the Koszul
braidings, as the composite of the braided monoidal extensions of scalars along `𝒪_E ⟶ E` and
`E ⟶ ℚ̄_ℓ` (`boundedConstructibleExtendScalarsLaxBraided`,
`constructibleToPadicAlgClLaxBraided`). -/
@[instance_reducible]
noncomputable def boundedConstructibleIntegersToPadicAlgClBraided (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] : (𝐓 X).Braided :=
  letI : (boundedConstructibleExtendScalars X.left ℓ E).Braided :=
    { braided := (boundedConstructibleExtendScalarsLaxBraided ℓ E X).braided }
  letI : (constructibleToPadicAlgCl X.left ℓ E).Braided :=
    { braided := (constructibleToPadicAlgClLaxBraided ℓ E X).braided }
  inferInstanceAs (boundedConstructibleExtendScalars X.left ℓ E ⋙
    constructibleToPadicAlgCl X.left ℓ E).Braided

/-- The extension of scalars `ℚ̄_ℓ ⊗ᴸ_E -` on bounded constructible complexes is additive, as the
derived extension of scalars, a triangulated functor, is. -/
instance additive_constructibleToPadicAlgCl (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : (constructibleToPadicAlgCl X.left ℓ E).Additive where
  map_add {_ _ f g} := (boundedConstructible _).ι.map_injective (by
    have := @Functor.IsTriangulated.instAdditive _ _ _ _ _ _
      (derivedExtendScalarsToPadicAlgCl X.left ℓ E) _ _ _ _ _ (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance) _ _ _
    exact (derivedExtendScalarsToPadicAlgCl X.left ℓ E).map_add)

/-- The extension of scalars `T = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` on bounded constructible complexes is additive.
-/
instance additive_boundedConstructibleIntegersToPadicAlgCl (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] : (𝐓 X).Additive :=
  inferInstanceAs (boundedConstructibleExtendScalars X.left ℓ E ⋙
    constructibleToPadicAlgCl X.left ℓ E).Additive

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- For `k` separably closed, the extension of scalars `ℚ̄_ℓ ⊗_{𝒪_E} -` kills no nonzero
endomorphism of the unit of `Mod_{𝒪̲_E,s}`: such an endomorphism is a scalar `a ∈ 𝒪_E`, sent to
the multiplication by the image of `a` in `ℚ̄_ℓ`. -/
lemma eq_zero_of_pointModExtendScalars_map_eq_zero [IsSepClosed k]
    (u : 𝟙_ (PointModIntegral ℓ k E) ⟶ 𝟙_ (PointModIntegral ℓ k E))
    (h : (pointModExtendScalars ℓ k E).map u = 0) : u = 0 := by
  obtain ⟨r, hr⟩ := surjective_pointIntegersUnitEndRingHom ℓ k E (End.of u)
  have h₁ := pointModExtendScalarsUnitIso_inv_comp_map ℓ k E (shrinkRingEquiv ℓ E.1 r)
  have hu : (pointIntegersScalarsOp ℓ k E (shrinkRingEquiv ℓ E.1 r)).unop.asHom = u :=
    congrArg End.asHom ((congrArg (pointIntegersUnitEndRingHom ℓ k E)
      ((shrinkRingEquiv ℓ E.1).symm_apply_apply r)).trans hr)
  rw [hu, h, Limits.comp_zero, eq_comm, Preadditive.IsIso.comp_right_eq_zero] at h₁
  have h₂ : pointUnitEndRingHom ℓ k (integersToULift ℓ E.1 (shrinkRingEquiv ℓ E.1 r)).down = 0 := by
    apply End.ext
    rw [End.zero_asHom]
    exact h₁
  have h₃ : integersToULift ℓ E.1 (shrinkRingEquiv ℓ E.1 r) = 0 :=
    ULift.ext ((injective_iff_map_eq_zero _).1 (bijective_pointUnitEndRingHom ℓ k).1 _ h₂)
  have hr0 : r = 0 := (map_eq_zero_iff _ (shrinkRingEquiv ℓ E.1).injective).1
    ((injective_iff_map_eq_zero _).1 (integersToULift_injective ℓ E.1) _ h₃)
  rw [hr0, map_zero] at hr
  exact (congrArg End.asHom hr).symm

omit [Fact (ringChar k).Prime] in
/-- For `k` separably closed, the extension of scalars `T = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` kills no nonzero
endomorphism of the unit of `Dᵇc(Spec k)⟦𝒪_E⟧`: the unit is `𝒪̲_E,s` placed in degree `0`, and
`T` is computed by the exact extension of scalars `ℚ̄_ℓ ⊗_{𝒪_E} -` of module objects. -/
lemma eq_zero_of_boundedConstructibleIntegersToPadicAlgCl_map_eq_zero [IsSepClosed k]
    (g : 𝟙_ (Dᵇc((point k).left)⟦𝒪⟧) ⟶ 𝟙_ (Dᵇc((point k).left)⟦𝒪⟧))
    (h : (𝐓 (point k)).map g = 0) : g = 0 := by
  have h₁ : (boundedConstructible _).ι.map ((𝐓 (point k)).map g) = 0 := by
    rw [h, Functor.map_zero]
  have h₂ : (derivedExtendScalarsToPadicAlgCl (point k).left ℓ E).map
      ((boundedConstructible _).ι.map ((boundedConstructibleExtendScalars (point k).left ℓ E).map
        g)) = 0 :=
    NatIso.map_eq_zero_of_map_eq_zero
      (boundedConstructibleToPadicAlgClCompatibility (point k).left ℓ E)
      (f := (boundedConstructibleExtendScalars (point k).left ℓ E).map g) h₁
  have h₃ := NatIso.map_eq_zero_of_map_eq_zero
    (boundedConstructibleExtendScalarsCompatibility (point k).left ℓ E) (f := g)
    ((derivedExtendScalarsToPadicAlgCl (point k).left ℓ E).map_injective
      (h₂.trans (Functor.map_zero _ _ _).symm))
  have h₄ := Functor.eq_zero_of_leftDerivedFunctor_map_eq_zero
    (Mod.extendScalars (padicIntegersToPadicSubfield (point k).left ℓ E))
    ((boundedConstructible _).ι.map g)
    (fun u hu ↦ eq_zero_of_pointModExtendScalars_map_eq_zero ℓ E u (by
      rw [Functor.comp_map, hu, Functor.map_zero])) h₃
  apply (boundedConstructible _).ι.map_injective
  rw [Functor.map_zero]
  exact h₄

attribute [local instance] boundedConstructibleIntegersToPadicAlgClBraided

/-- **The extension of scalars is injective on the scalars of the point**: for `k` separably
closed, the ring map `End(𝟙) ⟶ End(𝟙)` induced by `T = ℚ̄_ℓ ⊗ᴸ_{𝒪_E} -` on the endomorphisms of the
units of `Dᵇc(Spec k)⟦𝒪_E⟧` and `Dᵇc(Spec k)⟦ℚ̄_ℓ⟧` is injective: it is the inclusion
`𝒪_E ⊆ ℚ̄_ℓ`. -/
theorem injective_unitEndRingHom_boundedConstructibleIntegersToPadicAlgCl [IsSepClosed k] :
    Function.Injective (𝐓 (point k)).unitEndRingHom := by
  refine (injective_iff_map_eq_zero (𝐓 (point k)).unitEndRingHom.toAddMonoidHom).2 fun t ht ↦ ?_
  have h : Functor.LaxMonoidal.ε (𝐓 (point k)) ≫ (𝐓 (point k)).map t.asHom ≫
      Functor.OplaxMonoidal.η (𝐓 (point k)) = 0 := congrArg End.asHom ht
  rw [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero] at h
  apply End.ext
  rw [End.zero_asHom]
  exact eq_zero_of_boundedConstructibleIntegersToPadicAlgCl_map_eq_zero ℓ E t.asHom h

end Monoidal

/-! ### The integral trace formula -/

section TraceFormula

attribute [local instance] boundedConstructibleBraiding
  PadicIntegersRingObj.boundedConstructibleBraiding
  boundedConstructibleIntegersToPadicAlgClBraided

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **The stalk maps commute with the extension of scalars**: for a rational point `x` fixed by
`h`, under the comparison `T Lx^* ≅ Lx^* T`, the extension of scalars of the stalk map `v_x` of an
integral coefficient map `v : Lh^* K ⟶ K` is the stalk map of the coefficient map
`Lh^* T K ≅ T Lh^* K --T v--> T K`. -/
theorem integersToPadicAlgCl_map_graphStalkMap {h : X ⟶ X} (K : Dᵇc(X.left)⟦𝒪⟧)
    (v : (boundedConstructibleUpperStar 𝒪 ℓ h).obj K ⟶ K) (x : RationalPoint X)
    (hx : x ≫ h = x) :
    (𝐓 (point k)).map (PadicIntegersRingObj.graphStalkMap K h v x hx) ≫
        (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E x).hom.app K =
      (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E x).hom.app K ≫
        Correspondence.graphStalkMap ((𝐓 X).obj K) h
          ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h).inv.app K ≫
            (𝐓 X).map v) x hx := by
  simp only [PadicIntegersRingObj.graphStalkMap, Correspondence.graphStalkMap]
  exact map_graphStalkMap_aux (boundedConstructibleUpperStarComp 𝒪 ℓ x h)
    (boundedConstructibleUpperStarComp ℚ̄ ℓ x h)
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E x)
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h)
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E (x ≫ h)) K
    (eqToHom (by rw [hx])) (eqToHom (by rw [hx]))
    (integersToPadicAlgCl_map_upperStarComp_hom_app ℓ E x h K)
    (boundedConstructibleUpperStarIntegersToPadicAlgClIso_hom_app_congr ℓ E hx K) v

/-- **The global operator commutes with the extension of scalars**: for a proper `h`, under the
comparison `T RΓ_c ≅ RΓ_c T`, the extension of scalars of `RΓ_c(X, v) ∘ h^♯` is the operator of
the coefficient map `Lh^* T K ≅ T Lh^* K --T v--> T K`. -/
theorem integersToPadicAlgCl_map_compactPullback_app_comp {h : X ⟶ X} [IsProper h.left]
    (K : Dᵇc(X.left)⟦𝒪⟧) (v : (boundedConstructibleUpperStar 𝒪 ℓ h).obj K ⟶ K) :
    (𝐓 (point k)).map ((PadicIntegersRingObj.compactPullback ℓ E.1 h).app K ≫
          (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).map v) ≫
        (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X)).hom.app K =
      (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X)).hom.app K ≫
        (compactPullback ℓ h).app ((𝐓 X).obj K) ≫
          (boundedConstructibleLowerShriek ℓ (toPoint X)).map
            ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h).inv.app K ≫
              (𝐓 X).map v) := by
  refine map_compactPullback_comp_aux (PadicIntegersRingObj.compactPullback ℓ E.1 h)
    (compactPullback ℓ h) (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E h)
    (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X)) K ?_ v
  set_option maxRecDepth 20000 in
  exact integersToPadicAlgCl_map_compactPullback_app ℓ E h K

/-- **The integral trace formula in degree one, from the `ℚ̄_ℓ`-formula**: if the trace formula
in degree one holds for a proper endomorphism `Φ` with `ℚ̄_ℓ`-coefficients
(`ProEtale.CondensedRing.TraceFormulaHolds`), it holds with `𝒪_E`-coefficients: for every bounded
constructible `𝒪_E`-complex `K` and every morphism `θ : LΦ^* K ⟶ K`,
```
tr_{𝒪_E}(RΓ_c(X, θ) ∘ Φ^♯ | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ x = x} tr_{𝒪_E}(θ_x | K_x).
``` -/
theorem PadicIntegersRingObj.trace_compactPullback_comp_eq_sum [IsSepClosed k] {Φ : X ⟶ X}
    [IsProper Φ.left] (hΦ : TraceFormulaHolds ℓ Φ) (K : Dᵇc(X.left)⟦𝒪⟧)
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K)
    [HasRightDual ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K)]
    [∀ x : RationalPoint X, HasRightDual ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)]
    [Fintype {x : RationalPoint X // x ≫ Φ = x}] :
    trace ((PadicIntegersRingObj.compactPullback ℓ E.1 Φ).app K ≫
        (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).map θ) =
      ∑ x : {x : RationalPoint X // x ≫ Φ = x},
        trace (PadicIntegersRingObj.graphStalkMap K Φ θ x.1 x.2) := by
  let T := 𝐓 (point k)
  let A := (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K
  let eG := (lowerShriekIntegersToPadicAlgClIso ℓ E (toPoint X)).app K
  let ψ := (boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E Φ).inv.app K ≫ (𝐓 X).map θ
  let : ExactPairing (T.obj A) (T.obj Aᘁ) := ExactPairing.map T A Aᘁ
  let : HasRightDual (T.obj A) := ⟨T.obj Aᘁ⟩
  let : ExactPairing ((CondensedRing.boundedConstructibleLowerShriek ℓ (toPoint X)).obj
      ((𝐓 X).obj K)) (T.obj Aᘁ) := exactPairingCongrLeft (X' := T.obj A) eG.symm
  let : HasRightDual ((CondensedRing.boundedConstructibleLowerShriek ℓ (toPoint X)).obj
      ((𝐓 X).obj K)) := ⟨T.obj Aᘁ⟩
  let : ∀ x : RationalPoint X,
      ExactPairing (T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K))
        (T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)ᘁ) := fun x ↦
    ExactPairing.map T ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)
      ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)ᘁ
  let : ∀ x : RationalPoint X,
      HasRightDual (T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)) := fun x ↦
    ⟨T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)ᘁ⟩
  let : ∀ x : RationalPoint X,
      ExactPairing ((boundedConstructibleUpperStar ℚ̄ ℓ x).obj ((𝐓 X).obj K))
        (T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)ᘁ) := fun x ↦
    exactPairingCongrLeft (X' := T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K))
      ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E x).app K).symm
  let : ∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar ℚ̄ ℓ x).obj ((𝐓 X).obj K)) := fun x ↦
    ⟨T.obj ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)ᘁ⟩
  have hG : trace ((CondensedRing.compactPullback ℓ Φ).app ((𝐓 X).obj K) ≫
        (CondensedRing.boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ) =
      (T.unitEndRingHom (.of (trace ((PadicIntegersRingObj.compactPullback ℓ E.1 Φ).app K ≫
        (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).map θ)))).asHom :=
    T.trace_eq_unitEndRingHom_trace _ _ eG
      (integersToPadicAlgCl_map_compactPullback_app_comp ℓ E K θ)
  have hS : ∀ x : {x : RationalPoint X // x ≫ Φ = x},
      trace (Correspondence.graphStalkMap ((𝐓 X).obj K) Φ ψ x.1 x.2) =
        (T.unitEndRingHom (.of (trace (PadicIntegersRingObj.graphStalkMap K Φ θ x.1 x.2)))).asHom :=
    fun x ↦ T.trace_eq_unitEndRingHom_trace _ _
      ((boundedConstructibleUpperStarIntegersToPadicAlgClIso ℓ E x.1).app K)
      (integersToPadicAlgCl_map_graphStalkMap ℓ E K θ x.1 x.2)
  have key : T.unitEndRingHom (.of (trace ((PadicIntegersRingObj.compactPullback ℓ E.1 Φ).app K ≫
        (PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).map θ))) =
      T.unitEndRingHom (∑ x : {x : RationalPoint X // x ≫ Φ = x},
        .of (trace (PadicIntegersRingObj.graphStalkMap K Φ θ x.1 x.2))) := by
    have hQ := hΦ ((𝐓 X).obj K) ψ
    have hsum : T.unitEndRingHom (∑ x : {x : RationalPoint X // x ≫ Φ = x},
          .of (trace (PadicIntegersRingObj.graphStalkMap K Φ θ x.1 x.2))) =
        ∑ x : {x : RationalPoint X // x ≫ Φ = x},
          T.unitEndRingHom (.of (trace (PadicIntegersRingObj.graphStalkMap K Φ θ x.1 x.2))) :=
      map_sum T.unitEndRingHom.toAddMonoidHom _ _
    apply End.ext
    exact hG.symm.trans (hQ.trans ((Finset.sum_congr rfl fun x _ ↦ hS x).trans
      ((End.sum_asHom _ _ _).symm.trans (congrArg End.asHom hsum.symm))))
  simpa only [End.sum_asHom] using
    congrArg End.asHom (injective_unitEndRingHom_boundedConstructibleIntegersToPadicAlgCl ℓ E key)


/-- **The integral trace formula**: let `Φ` be the model Frobenius of a separated model `X₀`
of finite type over a finite field `k₀`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of
integers `𝒪_E`, `K` a bounded constructible `𝒪_E`-complex on `X` and `θ : LΦ^* K ⟶ K` an arbitrary
morphism. For every `m ≥ 1`,
```
tr_{𝒪_E}(T_{c_m}(θ_m) | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr_{𝒪_E}(θ_{m,x} | K_x),
```
the sum running over the rational points `x` fixed by `Φ_m`, both sides being categorical traces
in `Dᵇc(Spec k)⟦𝒪_E⟧`. The dualizability of `RΓ_c(X, K)` and of the stalks `K_x` is
assumed, as in the `ℚ̄_ℓ`-formula `ProEtale.CondensedRing.trace_frobeniusCompactOperator_eq_sum`. -/
theorem PadicIntegersRingObj.trace_frobeniusCompactOperator_eq_sum [IsAlgClosed k]
    {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X}
    (hΦ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left] (K : Dᵇc(X.left)⟦𝒪⟧)
    (θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K ⟶ K) {m : ℕ} (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual ((PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K)]
    [∀ x : RationalPoint X, HasRightDual ((boundedConstructibleUpperStar 𝒪 ℓ x).obj K)] :
    trace (PadicIntegersRingObj.frobeniusCompactOperator ℓ E.1 θ m) =
      ∑ x : FixedPoint Φ m, trace (PadicIntegersRingObj.graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate θ m) x.1 x.2) := by
  obtain ⟨k₁, _, _, _, _, _, hcard⟩ := exists_finiteField_natCard_eq_pow k₀ k (m := m) (by omega)
  exact PadicIntegersRingObj.trace_compactPullback_comp_eq_sum ℓ E
    (traceFormulaHolds_of_isModelFrobenius (hΦ.fieldChange (k₁ := k₁) hcard)) K
    (frobeniusCoefficientIterate θ m)

end TraceFormula

end AlgebraicGeometry.ProEtale.CondensedRing
