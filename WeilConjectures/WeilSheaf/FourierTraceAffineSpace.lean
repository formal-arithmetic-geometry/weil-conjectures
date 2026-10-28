/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPointsPi
public import WeilConjectures.FourierTransform.ClassicalAffineSpace
public import WeilConjectures.WeilSheaf.FourierAffineSpace
public import WeilConjectures.WeilSheaf.FourierTrace

/-!
# The trace function of the Fourier–Deligne transform on an affine space

Let `k₀` be a finite field with `q` elements, `ψ` an additive character of `k₀` with values in
`ℚ̄_ℓ` and `ι` a finite index type with `r` elements. The `𝔽_{qⁿ}`-rational points of the affine
space `𝔸^ι` are the vectors `ι → 𝔽_{qⁿ}` (`AlgebraicGeometry.AffineSpace.fieldPointsEquivPi`),
so the trace function `t_K` of a Weil complex `K` on `𝔸^ι` at level `n` is a function on
`𝔽_{qⁿ}^ι`. The *Fourier trace formula* says that the trace function of the Fourier–Deligne
transform `FT_ψ(K)` (`AlgebraicGeometry.affineSpaceFourierTransform`) is, up to the sign `(-1)^r`
coming from the shift `[r]`, the classical Fourier transform of the trace function of `K`
(`FiniteField.fourierTransformPi`):

`t_{FT_ψ(K)}(y) = (-1)^r ∑_{x ∈ 𝔽_{qⁿ}^ι} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}⟨x, y⟩)`.

The proof is the one on the affine line
(`AlgebraicGeometry.WeilComplex.traceFunction_fourierTransform`): base change of `Rpr₂!` along
the point `y`, the Grothendieck–Lefschetz formula on the fibre of `pr₂` over `y`, whose
`𝔽_{qⁿ}`-points are the pairs `(φ, x)` of a `k₀`-embedding `φ` of `𝔽_{qⁿ}` and a vector `x`,
and the trace function of the Artin–Schreier sheaf pulled back along the pairing.

## Main statements

- `AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform`: the Fourier trace
  formula on `𝔸^ι`.
- `AlgebraicGeometry.WeilComplex.traceFunction_affineSpaceFourierTransform_inv`: trace-level
  Fourier inversion on `𝔸^ι`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (ι : Type u)

section Points

variable (k₀ : Type u) [Field k₀] {K L : Type u} [Field K] [Field L] [Algebra k₀ K]
  [Algebra k₀ L]

/-- The identification `𝔸^ι(K) ≃ K^ι` is compatible with isomorphisms of the coefficient
field. -/
lemma AffineSpace.fieldPointsEquivPi_fieldPointsCongr (σ : K ≃ₐ[k₀] L)
    (x : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    AffineSpace.fieldPointsEquivPi ι k₀ L (Scheme.Hom.fieldPointsCongr _ σ x) =
      fun i ↦ σ (AffineSpace.fieldPointsEquivPi ι k₀ K x i) :=
  funext fun _ ↦ ΓSpecIso_hom_appTop_specMap_comp _ x.1 _

omit [Algebra k₀ L] in
/-- The coordinate of the pairing `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` of the coordinates of a point `z` of
`𝔸^ι ×_{k₀} 𝔸^ι`. -/
lemma affineSpacePair.ΓSpecIso_hom_appTop_pairing [Fintype ι]
    (z : Spec (CommRingCat.of L) ⟶ affineSpacePair ι k₀) :
    (Scheme.ΓSpecIso (.of L)).hom.hom
        ((z ≫ affineSpacePair.pairing ι k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
      ∑ i, (Scheme.ΓSpecIso (.of L)).hom.hom
          ((z ≫ affineSpacePair.fst ι k₀).appTop (AffineSpace.coord _ i)) *
        (Scheme.ΓSpecIso (.of L)).hom.hom
          ((z ≫ affineSpacePair.snd ι k₀).appTop (AffineSpace.coord _ i)) := by
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineSpacePair.pairing_appTop_coord, map_sum, map_mul]

end Points

section Fibre

variable {ι} {k₀ : Type u} [Field k₀] {K : Type u} [Field K] [Algebra k₀ K]

/-- The fibre product `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{pr₂, 𝔸^ι, y} Spec K` of the second projection and a
`K`-rational point `y` of `𝔸^ι`, as a `k₀`-scheme through `Spec K`. -/
noncomputable def affineSpacePair.sndFiber
    (y : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints K) :
    Scheme.{u} :=
  pullback (affineSpacePair.snd ι k₀) (specOver.homOfFieldPoint y)

variable (y : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints K)

noncomputable instance affineSpacePair.sndFiber.instOver :
    (affineSpacePair.sndFiber y).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.snd _ _ ≫ specOver K ↘ Spec (CommRingCat.of k₀)⟩

/-- The projection `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{𝔸^ι} Spec K ⟶ 𝔸^ι ×_{k₀} 𝔸^ι`. -/
noncomputable def affineSpacePair.sndFiber.fst :
    affineSpacePair.sndFiber y ⟶ affineSpacePair ι k₀ :=
  pullback.fst _ _

/-- The projection `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{𝔸^ι} Spec K ⟶ Spec K`, the base change of `pr₂`. -/
noncomputable def affineSpacePair.sndFiber.snd : affineSpacePair.sndFiber y ⟶ specOver K :=
  pullback.snd _ _

lemma affineSpacePair.sndFiber.isPullback :
    IsPullback (affineSpacePair.sndFiber.fst y) (affineSpacePair.sndFiber.snd y)
      (affineSpacePair.snd ι k₀) (specOver.homOfFieldPoint y) :=
  IsPullback.of_hasPullback _ _

lemma affineSpacePair.sndFiber.over :
    (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) =
      affineSpacePair.sndFiber.snd y ≫ specOver K ↘ Spec (CommRingCat.of k₀) :=
  rfl

instance affineSpacePair.sndFiber.isOver_snd :
    (affineSpacePair.sndFiber.snd y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance affineSpacePair.sndFiber.isOver_fst :
    (affineSpacePair.sndFiber.fst y).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    rw [← comp_over (affineSpacePair.snd ι k₀) (Spec (CommRingCat.of k₀)), ← Category.assoc,
      (affineSpacePair.sndFiber.isPullback y).w, Category.assoc, comp_over]
    rfl⟩

instance affineSpacePair.sndFiber.isSeparated_snd : IsSeparated (affineSpacePair.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.sndFiber.quasiCompact_snd :
    QuasiCompact (affineSpacePair.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.sndFiber.locallyOfFiniteType_snd [Finite ι] :
    LocallyOfFiniteType (affineSpacePair.sndFiber.snd y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.sndFiber.isSeparated_over [Module.Finite k₀ K] :
    IsSeparated (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (IsSeparated (affineSpacePair.sndFiber.snd y ≫ _))

instance affineSpacePair.sndFiber.quasiCompact_over [Module.Finite k₀ K] :
    QuasiCompact (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (QuasiCompact (affineSpacePair.sndFiber.snd y ≫ _))

instance affineSpacePair.sndFiber.locallyOfFiniteType_over [Finite ι] [Module.Finite k₀ K] :
    LocallyOfFiniteType (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (affineSpacePair.sndFiber.snd y ≫ _))

variable {y} in
/-- The morphism `Spec L ⟶ (𝔸^ι ×_{k₀} 𝔸^ι) ×_{𝔸^ι} Spec K` given by the point `(x, φ(y))` of
`𝔸^ι ×_{k₀} 𝔸^ι` over the point `φ : Spec L ⟶ Spec K`, for a `k₀`-embedding `φ : K ⟶ L` and
`x ∈ L^ι`. -/
noncomputable def affineSpacePair.sndFiber.lift {L : Type u} [Field L] [Algebra k₀ L]
    (φ : K →ₐ[k₀] L) (x : ι → L) : Spec (CommRingCat.of L) ⟶ affineSpacePair.sndFiber y :=
  pullback.lift
    (pullback.lift ((AffineSpace.fieldPointsEquivPi ι k₀ L).symm x).1
      ((specOver.algHomEquivFieldPoints k₀ K L φ).1 ≫ y.1) (by
        rw [((AffineSpace.fieldPointsEquivPi ι k₀ L).symm x).2, Category.assoc, y.2]
        exact (specOver.algHomEquivFieldPoints k₀ K L φ).2.symm))
    (specOver.algHomEquivFieldPoints k₀ K L φ).1 (pullback.lift_snd _ _ _)

section Lift

variable {y} {L : Type u} [Field L] [Algebra k₀ L] (φ : K →ₐ[k₀] L) (x : ι → L)

lemma affineSpacePair.sndFiber.lift_snd :
    affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.snd y =
      (specOver.algHomEquivFieldPoints k₀ K L φ).1 :=
  pullback.lift_snd _ _ _

lemma affineSpacePair.sndFiber.lift_fst_fst :
    affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.fst y ≫
        affineSpacePair.fst ι k₀ =
      ((AffineSpace.fieldPointsEquivPi ι k₀ L).symm x).1 := by
  rw [affineSpacePair.sndFiber.lift, affineSpacePair.sndFiber.fst, pullback.lift_fst_assoc,
    affineSpacePair.fst, pullback.lift_fst]

lemma affineSpacePair.sndFiber.lift_fst_snd :
    affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.fst y ≫
        affineSpacePair.snd ι k₀ =
      (specOver.algHomEquivFieldPoints k₀ K L φ).1 ≫ y.1 := by
  rw [affineSpacePair.sndFiber.lift, affineSpacePair.sndFiber.fst, pullback.lift_fst_assoc,
    affineSpacePair.snd, pullback.lift_snd]

/-- The pairing of the coordinates of the point `(x, φ(y))` of `𝔸^ι ×_{k₀} 𝔸^ι` is
`∑ᵢ xᵢ φ(yᵢ)`. -/
lemma affineSpacePair.sndFiber.ΓSpecIso_hom_appTop_lift_pairing [Fintype ι] :
    (Scheme.ΓSpecIso (.of L)).hom.hom
        ((affineSpacePair.sndFiber.lift φ x ≫ affineSpacePair.sndFiber.fst y ≫
          affineSpacePair.pairing ι k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
      ∑ i, x i * φ (AffineSpace.fieldPointsEquivPi ι k₀ K y i) := by
  rw [← Category.assoc, affineSpacePair.ΓSpecIso_hom_appTop_pairing]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Category.assoc, Category.assoc, affineSpacePair.sndFiber.lift_fst_fst,
    affineSpacePair.sndFiber.lift_fst_snd, specOver.algHomEquivFieldPoints_apply_coe,
    ΓSpecIso_hom_appTop_specMap_comp, ← AffineSpace.fieldPointsEquivPi_apply,
    Equiv.apply_symm_apply, ← AffineSpace.fieldPointsEquivPi_apply]
  rfl

lemma affineSpacePair.sndFiber.lift_over :
    affineSpacePair.sndFiber.lift φ x ≫ (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ L)) := by
  rw [affineSpacePair.sndFiber.over, ← Category.assoc, affineSpacePair.sndFiber.lift_snd]
  exact (specOver.algHomEquivFieldPoints k₀ K L φ).2

end Lift

/-- The `L`-rational points of `(𝔸^ι ×_{k₀} 𝔸^ι) ×_{pr₂, 𝔸^ι, y} Spec K` are the pairs `(φ, x)`
of a `k₀`-embedding `φ : K ⟶ L` and a vector `x ∈ L^ι`: the point `(x, φ(y))` of
`𝔸^ι ×_{k₀} 𝔸^ι` over the point `φ` of `Spec K`. -/
noncomputable def affineSpacePair.sndFiber.fieldPointsEquiv (L : Type u) [Field L]
    [Algebra k₀ L] :
    (K →ₐ[k₀] L) × (ι → L) ≃
      (affineSpacePair.sndFiber y ↘ Spec (CommRingCat.of k₀)).fieldPoints L where
  toFun p := ⟨affineSpacePair.sndFiber.lift p.1 p.2, affineSpacePair.sndFiber.lift_over _ _⟩
  invFun w :=
    ((specOver.algHomEquivFieldPoints k₀ K L).symm
        ⟨w.1 ≫ affineSpacePair.sndFiber.snd y, (Category.assoc _ _ _).trans w.2⟩,
      AffineSpace.fieldPointsEquivPi ι k₀ L
        ⟨w.1 ≫ affineSpacePair.sndFiber.fst y ≫ affineSpacePair.fst ι k₀,
          by simpa only [Category.assoc, comp_over] using w.2⟩)
  left_inv p := by
    refine Prod.ext ((Equiv.symm_apply_eq _).2 (Subtype.ext ?_))
      ((Equiv.eq_symm_apply _).1 (Subtype.ext ?_))
    · exact affineSpacePair.sndFiber.lift_snd _ _
    · exact affineSpacePair.sndFiber.lift_fst_fst _ _
  right_inv w := by
    refine Subtype.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_)
    · rw [Category.assoc, Category.assoc]
      erw [affineSpacePair.sndFiber.lift_fst_fst]
      rw [Equiv.symm_apply_apply]
      rfl
    · rw [Category.assoc, Category.assoc]
      erw [affineSpacePair.sndFiber.lift_fst_snd]
      rw [Equiv.apply_symm_apply]
      exact (Category.assoc _ _ _).trans
        (congrArg (w.1 ≫ ·) (affineSpacePair.sndFiber.isPullback y).w).symm
    · erw [affineSpacePair.sndFiber.lift_snd]
      rw [Equiv.apply_symm_apply]
      rfl

end Fibre

namespace WeilComplex

variable {ι} {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The trace function of a Weil complex on the affine space `𝔸^ι` at level `n`, as a function
on `𝔽_{qⁿ}^ι`, through the identification `𝔸^ι(𝔽_{qⁿ}) ≃ 𝔽_{qⁿ}^ι`. -/
noncomputable def affineSpaceTraceFunction (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    (n : ℕ) (x : ι → FiniteField.galoisExtension k₀ n) : PadicAlgCl l :=
  K.traceFunction n ((AffineSpace.fieldPointsEquivPi ι k₀ _).symm x)

/-- The trace function of a Weil complex on `𝔸^ι` is invariant under the `k₀`-automorphisms of
`𝔽_{qⁿ}`, acting on the coordinates. -/
theorem affineSpaceTraceFunction_algEquiv (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    (n : ℕ) (σ : FiniteField.galoisExtension k₀ n ≃ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : ι → FiniteField.galoisExtension k₀ n) :
    K.affineSpaceTraceFunction n (fun i ↦ σ (x i)) = K.affineSpaceTraceFunction n x := by
  rw [affineSpaceTraceFunction, affineSpaceTraceFunction,
    ← traceFunction_fieldPointsCongr K n σ ((AffineSpace.fieldPointsEquivPi ι k₀ _).symm x)]
  congr 1
  rw [Equiv.symm_apply_eq, AffineSpace.fieldPointsEquivPi_fieldPointsCongr,
    Equiv.apply_symm_apply]

variable [Fintype ι]

/-- The Weil complex `pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ` on `𝔸^ι ×_{k₀} 𝔸^ι`, whose direct image with
compact support along `pr₂` is the Fourier–Deligne transform of `K` up to the shift `[r]`. -/
noncomputable abbrev affineSpaceFourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) :
    WeilComplex k₀ l (affineSpacePair ι k₀) :=
  (tensorLisse (affineSpaceFourierKernel ι ψ) (isLisse_affineSpaceFourierKernel ι ψ)).obj
    ((upperStar (affineSpacePair.fst ι k₀)).obj K)

/-- The trace function of `pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ` at the point `(x, φ(y))` of the fibre of
`pr₂` over `y` is `ψ(Tr⟨x, φ(y)⟩) t_K(x)`. -/
theorem traceFunction_upperStar_affineSpaceFourierIntegrand (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) {n : ℕ} (hn : n ≠ 0)
    (y : (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)).fieldPoints
      (FiniteField.galoisExtension k₀ n))
    (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n)
    (x : ι → FiniteField.galoisExtension k₀ n) :
    ((upperStar (affineSpacePair.sndFiber.fst y)).obj
        (affineSpaceFourierIntegrand ψ K)).traceFunction n
        (affineSpacePair.sndFiber.fieldPointsEquiv y _ (φ, x)) =
      ψ (Algebra.trace k₀ _ (∑ i, x i * φ (AffineSpace.fieldPointsEquivPi ι k₀ _ y i))) *
        K.affineSpaceTraceFunction n x := by
  rw [traceFunction_upperStar, traceFunction_tensorLisse, affineSpaceFourierKernel,
    WeilSheaf.traceFunction_upperStar, WeilSheaf.traceFunction_artinSchreier ψ 1 hn,
    traceFunction_upperStar, map_one, one_mul, affineSpaceTraceFunction]
  have hK : Scheme.Hom.mapFieldPoints (affineSpacePair.fst ι k₀) _
      (Scheme.Hom.mapFieldPoints (affineSpacePair.sndFiber.fst y) _
        (affineSpacePair.sndFiber.fieldPointsEquiv y _ (φ, x))) =
      (AffineSpace.fieldPointsEquivPi ι k₀ _).symm x :=
    Subtype.ext ((Category.assoc _ _ _).trans (affineSpacePair.sndFiber.lift_fst_fst φ x))
  have hμ : (Scheme.ΓSpecIso (.of _)).hom.hom
      ((Scheme.Hom.mapFieldPoints (affineSpacePair.pairing ι k₀) _
        (Scheme.Hom.mapFieldPoints (affineSpacePair.sndFiber.fst y) _
          (affineSpacePair.sndFiber.fieldPointsEquiv y _ (φ, x)))).1.appTop
            (AffineSpace.coord _ PUnit.unit)) =
      ∑ i, x i * φ (AffineSpace.fieldPointsEquivPi ι k₀ _ y i) := by
    rw [← affineSpacePair.sndFiber.ΓSpecIso_hom_appTop_lift_pairing φ x, ← Category.assoc]
    rfl
  rw [hK, hμ]

variable [DecidableEq ι]

/-- Summing the trace function of `pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ` over the `𝔽_{qⁿ}`-rational points
`(x, φ(y))` of the fibre of `pr₂` over `y` gives `n` times the classical Fourier transform of
`t_K` at `y`: by Galois invariance the `n` embeddings `φ` contribute the same sum. -/
theorem finsum_traceFunction_upperStar_affineSpaceFourierIntegrand
    (ψ : AddChar k₀ (PadicAlgCl l)) (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)))
    {n : ℕ} (hn : n ≠ 0) [Fintype (FiniteField.galoisExtension k₀ n)]
    (y : ι → FiniteField.galoisExtension k₀ n) :
    ∑ᶠ w, ((upperStar (affineSpacePair.sndFiber.fst
        ((AffineSpace.fieldPointsEquivPi ι k₀ _).symm y))).obj
        (affineSpaceFourierIntegrand ψ K)).traceFunction n w =
      n • FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
  have : Fintype (FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :=
    Fintype.ofFinite _
  rw [← finsum_comp_equiv (affineSpacePair.sndFiber.fieldPointsEquiv _ _),
    finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
  simp_rw [traceFunction_upperStar_affineSpaceFourierIntegrand ψ K hn, Equiv.apply_symm_apply]
  have h (φ : FiniteField.galoisExtension k₀ n →ₐ[k₀] FiniteField.galoisExtension k₀ n) :
      ∑ x : ι → FiniteField.galoisExtension k₀ n,
          ψ (Algebra.trace k₀ _ (∑ i, x i * φ (y i))) * K.affineSpaceTraceFunction n x =
        FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
    rw [← MulEquiv.apply_symm_apply (algEquivEquivAlgHom k₀ _) φ,
      ← Equiv.sum_comp (Equiv.piCongrRight fun _ ↦
        ((algEquivEquivAlgHom k₀ _).symm φ).toEquiv)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    set σ := (algEquivEquivAlgHom k₀ _).symm φ
    have hσ (i : ι) : algEquivEquivAlgHom k₀ _ σ (y i) = σ (y i) := rfl
    have hx : (Equiv.piCongrRight fun _ ↦ σ.toEquiv) x = fun i ↦ σ (x i) := rfl
    simp_rw [hx, hσ, ← map_mul, ← map_sum, Algebra.trace_eq_of_algEquiv,
      affineSpaceTraceFunction_algEquiv]
    exact mul_comm _ _
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteField.nat_card_algHom_galoisExtension k₀ hn]

/-- **The Fourier trace formula on `𝔸^ι`.** For an additive character `ψ` of `k₀`, a Weil complex
`K` on the affine space `𝔸^ι` with `r = #ι`, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}^ι`,

`t_{FT_ψ(K)}(y) = (-1)^r ∑_{x ∈ 𝔽_{qⁿ}^ι} t_K(x) ψ(Tr_{𝔽_{qⁿ}/k₀}⟨x, y⟩)`:

up to the sign coming from the shift `[r]`, the trace function of the transform is the
classical Fourier transform of the trace function of `K`.
(sketch blueprint: `thm-fd-fourier-trace`; blueprint: `thm-fd-fourier-trace`) -/
theorem traceFunction_affineSpaceFourierTransform (ψ : AddChar k₀ (PadicAlgCl l))
    (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] (y : ι → FiniteField.galoisExtension k₀ n) :
    ((affineSpaceFourierTransform ι ψ).obj K).affineSpaceTraceFunction n y =
      (-1) ^ Fintype.card ι *
        FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
  set yp := (AffineSpace.fieldPointsEquivPi ι k₀ _).symm y
  -- base change of `Rpr₂!` along the point `y : Spec 𝔽_{qⁿ} ⟶ 𝔸^ι`
  obtain ⟨e⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affineSpacePair.snd ι k₀) (specOver.homOfFieldPoint yp) (affineSpacePair.sndFiber.snd yp)
    (affineSpacePair.sndFiber.fst yp) (affineSpacePair.sndFiber.isPullback yp)
  have he := e.app (affineSpaceFourierIntegrand ψ K)
  dsimp only [Functor.comp_obj] at he
  have hτ : (specOver.homOfFieldPoint yp).mapFieldPoints _ (specOver.tautPoint k₀ _) = yp :=
    Subtype.ext (Category.id_comp _)
  -- `n t_{Rpr₂! M}(y)` is the sum of `t_{Rpr₂! M}` over the Galois conjugates of `y`, hence by
  -- Grothendieck–Lefschetz the sum of `t_M` over the fibre of `pr₂` over `y`
  have key : n • ((derivedLowerShriek k₀ l (affineSpacePair.snd ι k₀)).obj
      (affineSpaceFourierIntegrand ψ K)).traceFunction n yp =
      n • FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) y := by
    rw [← hτ, ← traceFunction_upperStar, traceFunction_congr he,
      ← specOver.finsum_fieldPoints_eq_nsmul k₀ hn _
        fun σ x ↦ traceFunction_fieldPointsCongr _ n σ x,
      finsum_traceFunction_derivedLowerShriek _ _ hn,
      finsum_traceFunction_upperStar_affineSpaceFourierIntegrand ψ K hn]
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  have h := traceFunction_shift ((derivedLowerShriek k₀ l (affineSpacePair.snd ι k₀)).obj
    (affineSpaceFourierIntegrand ψ K)) (Fintype.card ι) n yp
  rw [Int.coe_negOnePow_natCast, mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) key, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  exact h

/-- The `qⁿ` elements of `𝔽_{qⁿ}`, as a scalar. -/
private lemma card_galoisExtension_eq {n : ℕ} (hn : n ≠ 0)
    [Fintype (FiniteField.galoisExtension k₀ n)] :
    (Fintype.card (FiniteField.galoisExtension k₀ n) : ℕ) = Nat.card k₀ ^ n := by
  rw [← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k₀ n hn]

omit [DecidableEq ι] in
/-- **Trace-level Fourier inversion on `𝔸^ι`.** For a nontrivial additive character `ψ` of
`k₀`, a Weil complex `K` on `𝔸^ι` with `r = #ι`, `n ≥ 1` and `y ∈ 𝔽_{qⁿ}^ι`,

`t_{FT_{ψ⁻¹} FT_ψ(K)}(y) = q^{nr} t_K(y)`.

It is the Fourier trace formula applied twice, the signs `(-1)^r` cancelling, followed by
classical Fourier inversion (`FiniteField.fourierTransformPi_inv_fourierTransformPi`).
(sketch blueprint: `det-prop-double-trace`) -/
theorem traceFunction_affineSpaceFourierTransform_inv {ψ : AddChar k₀ (PadicAlgCl l)}
    (hψ : ψ ≠ 1) (K : WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀))) {n : ℕ} (hn : n ≠ 0)
    (y : ι → FiniteField.galoisExtension k₀ n) :
    ((affineSpaceFourierTransform ι ψ⁻¹).obj
        ((affineSpaceFourierTransform ι ψ).obj K)).affineSpaceTraceFunction n y =
      (Nat.card k₀ : PadicAlgCl l) ^ (n * Fintype.card ι) * K.affineSpaceTraceFunction n y := by
  classical
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  let := Fintype.ofFinite (FiniteField.galoisExtension k₀ n)
  have h : ((affineSpaceFourierTransform ι ψ).obj K).affineSpaceTraceFunction n =
      fun x ↦ (-1) ^ Fintype.card ι *
        FiniteField.fourierTransformPi ψ (K.affineSpaceTraceFunction n) x :=
    funext fun x ↦ traceFunction_affineSpaceFourierTransform ψ K hn x
  rw [traceFunction_affineSpaceFourierTransform ψ⁻¹ _ hn, h,
    FiniteField.fourierTransformPi_const_mul, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul, FiniteField.fourierTransformPi_inv_fourierTransformPi hψ,
    card_galoisExtension_eq hn, pow_mul]
  push_cast
  rfl

end WeilComplex

end AlgebraicGeometry
