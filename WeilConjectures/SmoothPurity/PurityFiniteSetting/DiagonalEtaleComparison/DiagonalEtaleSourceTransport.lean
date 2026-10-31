/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleNormalTransport

/-! # Source-section comparisons for etale diagonal correspondences

Source: diagonal-dualizing proof Steps 1--2 and orientation-charts proof Step 3.
(blueprint: def-pur-diagonal-etale-source-transport).

The source map uses only smooth base change and counit-normalized etale locality.
The normal transport remains the independently constructed Rees zero-fibre map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison

/-- The intermediate map W_U -> W_A times_A U, with no shrinking or frame choice.
Source: chart proof Step 1 (blueprint: def-pur-diagonal-etale-source-transport). -/
def sourceLift {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    (e : U ⟶ X)
    (w : e ≫ g = h) :=
  pullback.lift (selfMap d g h e w) (pullback.fst h h) (selfMap_fst d g h e w)

/-- The intermediate map is etale and takes the diagonal to the pulled-back section.
Restricting it to the specified neighbourhood O gives the Cartesian centre square.
Source: chart proof Steps 1--2 (blueprint: def-pur-diagonal-etale-source-transport).
Proof: identify W_A times_A U with U times_Y A. The map is 1 times e, a base change
of e, hence etale. Its separatedness and quasi-compactness follow by cancellation
from the first projection of the source self-product and the separated target projection.
The two projections identify its diagonal composite with the base-changed diagonal section. -/
theorem sourceLift_geometry {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g] (h : U ⟶ Y)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h) :
    Etale (sourceLift d g h e w) ∧ IsSeparated (sourceLift d g h e w) ∧
      QuasiCompact (sourceLift d g h e w) ∧
      pullback.diagonal h ≫ sourceLift d g h e w =
        Scheme.Hom.baseChangeSection
          (pullback.fst g
            g)
          (pullback.diagonal g)
          (pullback.diagonal_fst _) e := by
  have sq : IsPullback (sourceLift d g h e w) (pullback.snd h h)
      (pullback.fst (pullback.fst g g) e ≫ pullback.snd g g) e := by
    apply IsPullback.mk'
    · simp only [sourceLift, pullback.lift_fst_assoc, selfMap, pullback.lift_snd]
    · intro T a b hab hs
      apply pullback.hom_ext
      · simpa only [Category.assoc, sourceLift, pullback.lift_snd] using
          hab =≫ pullback.snd (pullback.fst g g) e
      · exact hs
    · intro T a b hab
      have hw : (a ≫ pullback.snd (pullback.fst g g) e) ≫ h = b ≫ h := by
        calc
          _ = (a ≫ pullback.snd (pullback.fst g g) e) ≫ e ≫ g := by rw [w]
          _ = (a ≫ pullback.fst (pullback.fst g g) e) ≫ pullback.fst g g ≫ g := by
            simp only [Category.assoc]
            rw [← pullback.condition_assoc]
          _ = (a ≫ pullback.fst (pullback.fst g g) e) ≫ pullback.snd g g ≫ g := by
            rw [pullback.condition]
          _ = b ≫ e ≫ g := by simpa only [Category.assoc] using hab =≫ g
          _ = b ≫ h := by rw [w]
      refine ⟨pullback.lift (a ≫ pullback.snd (pullback.fst g g) e) b hw, ?_,
        pullback.lift_snd _ _ _⟩
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, sourceLift, pullback.lift_fst, selfMap]
          rw [pullback.lift_fst_assoc]
          exact (congrArg (a ≫ ·)
            (pullback.condition (f := pullback.fst g g) (g := e))).symm
        · simpa only [Category.assoc, sourceLift, pullback.lift_fst, selfMap,
            pullback.lift_snd, pullback.lift_snd_assoc] using hab.symm
      · simp only [sourceLift, Category.assoc, pullback.lift_snd, pullback.lift_fst]
  have het : Etale (sourceLift d g h e w) :=
    MorphismProperty.of_isPullback sq.flip inferInstance
  have hov : sourceLift d g h e w ≫
      pullback.snd (pullback.fst g g) e = pullback.fst h h :=
    pullback.lift_snd _ _ _
  have hsep : IsSeparated (sourceLift d g h e w) := by
    have : IsSeparated (sourceLift d g h e w ≫
        pullback.snd (pullback.fst g g) e) := by rw [hov]; infer_instance
    exact IsSeparated.of_comp _ (pullback.snd (pullback.fst g g) e)
  have hqc : QuasiCompact (sourceLift d g h e w) := by
    have : QuasiCompact (sourceLift d g h e w ≫
        pullback.snd (pullback.fst g g) e) := by rw [hov]; infer_instance
    exact QuasiCompact.of_comp _ (pullback.snd (pullback.fst g g) e)
  refine ⟨het, hsep, hqc, ?_⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [sourceLift, selfMap, Scheme.Hom.baseChangeSection]
  · simp only [Category.assoc, sourceLift, pullback.lift_snd,
      pullback.diagonal_fst, Scheme.Hom.baseChangeSection, pullback.lift_snd]

/-- Canonical ordinary section comparison a, through etale locality and inverse smooth
base change. Locality composition shows it is exactly open restriction to O followed
by the exceptional comparison for (e times e)|O. Source: chart proof Step 3
(blueprint: def-pur-diagonal-etale-source-transport). -/
def sourceOrdinary (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := g
  let pA := pullback.fst p p
  let g₀ := pullback.snd pA e
  let s := Scheme.Hom.baseChangeSection pA (pullback.diagonal p)
    (pullback.diagonal_fst p) e
  letI := P.noetherian aY
  letI := P.noetherian (h ≫ aY)
  letI := P.noetherian (p ≫ aY)
  letI := P.noetherian (pA ≫ p ≫ aY)
  letI := P.noetherian (g₀ ≫ h ≫ aY)
  letI := P.noetherian (pullback.fst h h ≫ h ≫ aY)
  letI := (sourceLift_geometry d g h e w).1
  letI := (sourceLift_geometry d g h e w).2.1
  letI := (sourceLift_geometry d g h e w).2.2.1
  letI := Dnc.compactifiable P pA (p ≫ aY)
  letI := Dnc.compactifiable P g₀ (h ≫ aY)
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aY)
  letI := Dnc.invertibleExponent P (pA ≫ p ≫ aY)
  let t := sourceLift d g h e w
  let sU := pullback.diagonal h
  letI : HasCompactification (t ≫ g₀) :=
    HasCompactification.of_eq (pullback.lift_snd _ _ _).symm
  let unitCongr {q q' : pullback h h ⟶ U}
      [HasCompactification q] [HasCompactification q'] (he : q = q') :
      Etale.dualizingComplex P.Coefficient q =
        Etale.dualizingComplex P.Coefficient q' := by
    cases he
    rfl
  let restriction : Etale.sectionInvariant P.Coefficient g₀ s ≅
      Etale.sectionInvariant P.Coefficient (pullback.fst h h) sU :=
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) sU t s
      (sourceLift_geometry d g h e w).2.2.2.symm).app _ ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) sU).leftDerivedFunctor.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) t).app _ ≪≫
          (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N t g₀).app (𝟙_ _) ≪≫
          eqToIso (unitCongr (show t ≫ g₀ = pullback.fst h h from
            pullback.lift_snd _ _ _)))
  restriction.symm ≪≫
    (Dnc.sectionBaseChange P.Coefficient d pA (IsPullback.of_hasPullback pA e)
      (pullback.diagonal p) s (Scheme.Hom.baseChangeSection_fst pA
        (pullback.diagonal p) (pullback.diagonal_fst p) e)).symm

/-- The same specified a in the pro-etale section coordinates.
Source: chart proof Step 3 (blueprint: def-pur-diagonal-etale-source-transport). -/
def source (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e]
    (w : e ≫ g = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let p := g
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aY) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (sourceOrdinary P d g h aY e w N) ≪≫
    (Dnc.pullComparison P e (Dnc.sourceEtale P d (pullback.fst p p)
      (p ≫ aY) (pullback.diagonal p))).symm ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.mapIso
      (Dnc.sourceComparison P d (pullback.fst p p) (p ≫ aY) (pullback.diagonal p)).symm

/-- The source-section comparison through the common smooth source diagonal.
It uses only exceptional locality and smooth base change, with no DNC comparison.
Source: diagonal-dualizing proof Steps 1--2 and orientation-charts proof Step 3.
(blueprint: def-pur-diagonal-etale-source-transport). -/
def sourceTransport (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (K : P.AffineDiagonalGeometry g aY d V)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v]
    (w : v ≫ g = j ≫ f)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    (OrientationRefinement.pull P jO).obj
        (OrientationRefinement.source P f aY d V H) ≅
      (OrientationRefinement.pull P vO).obj
        (OrientationRefinement.source P g aY d V K) := by
  letI := H.smoothDimension
  letI := K.smoothDimension
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : QuasiCompact jO := inferInstance
  have : QuasiCompact vO := inferInstance
  have : SmoothOfRelativeDimension 0 jO :=
    (Etale.iff_smoothOfRelativeDimension_zero jO).mp inferInstance
  let h := jO ≫ (f ∣_ V.1)
  have hdim : SmoothOfRelativeDimension (0 + d) h :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + d) (jO ≫ (f ∣_ V.1)))
  have : SmoothOfRelativeDimension d h :=
    Eq.mp (congrArg (fun n => SmoothOfRelativeDimension n h) (Nat.zero_add d)) hdim
  have he : vO ≫ (g ∣_ V.1) = h := by
    apply (cancel_mono V.1.ι).mp
    dsimp only [h]
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  exact (source P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl N).symm ≪≫
    source P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he N

/-- The diagonal source-to-dualizing factor, before inverse deformation.
Source: diagonal-dualizing proof Steps 1--2.
(blueprint: def-pur-diagonal-etale-source-transport). -/
def sourceToDualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (H : P.AffineDiagonalGeometry f aY d V) :=
  OrientationRefinement.alpha P f aY d V H ≪≫
    (OrientationRefinement.rho P f aY d V H).symm ≪≫
    (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (OrientationCounit.unitChange P f))

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
