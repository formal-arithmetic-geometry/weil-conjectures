/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.PurityDiagonalSectionPastingData
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.SmoothExceptionalTensorPasting
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # The two diagonal restriction identifications

Source: latest blueprint, thm-pur-composition-coherence.proof.md, Step 1,
canonical twofold products and base-change restrictions
(blueprint: lem-pur-double-diagonal-section-identifications).

We reuse the published graph maps, gamma maps and specified alpha of DiagonalPasting.
Equalities are mapped to the actual small pro-etale derived category by SameProEtaleMap.
No orientation or Tate comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
  HomologicalComplex.monoidalCategory
universe u uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting.DiagonalPasting

attribute [local irreducible] Sheaf.monoidalCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

/-- The four Cartesian squares and every section identity used in the restrictions.
Source: latest blueprint, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-double-diagonal-section-identifications).
Proof: on arbitrary test schemes, the first square identifies pairs (x,x') over Z
with ((x,y),x') subject to y=f(x'). The second is the defining product Q.
The third imposes f(x')=f(x), and the fourth imposes y_1=f(x) in W_g.
These give inverse morphisms by the fibre-product universal property, not merely
bijections on geometric points. Compare both projections to obtain at=s, lt=1,
rs=f, ba=p_gf, i Delta_f=t, js=Delta_g f and li=p_2,f. -/
theorem doubleDiagonalGeometry {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (pullback.snd (f ≫ g) (f ≫ g)) (a f g) f
      (pullback.snd (f ≫ g) g) ∧
    IsPullback (pullback.snd (f ≫ g) g) (pullback.fst (f ≫ g) g) g (f ≫ g) ∧
    IsPullback (i f g) (pullback.fst f f) (a f g) (s f g) ∧
    IsPullback (j f g) (pullback.fst (f ≫ g) g) (pullback.fst g g) f ∧
    pullback.diagonal (f ≫ g) ≫ a f g = s f g ∧
    pullback.diagonal (f ≫ g) ≫ pullback.snd (f ≫ g) (f ≫ g) = 𝟙 X ∧
    s f g ≫ pullback.snd (f ≫ g) g = f ∧
    a f g ≫ pullback.fst (f ≫ g) g = pullback.fst (f ≫ g) (f ≫ g) ∧
    pullback.diagonal f ≫ i f g = pullback.diagonal (f ≫ g) ∧
    s f g ≫ j f g = f ≫ pullback.diagonal g ∧
    i f g ≫ pullback.snd (f ≫ g) (f ≫ g) = pullback.snd f f := by
  have ha : IsPullback (pullback.snd (f ≫ g) (f ≫ g)) (a f g) f
      (pullback.snd (f ≫ g) g) := by
    apply IsPullback.mk' (by simp [a])
    · intro T φ φ' h₁ h₂
      apply pullback.hom_ext
      · simpa [a] using congrArg (fun k ↦ k ≫ pullback.fst (f ≫ g) g) h₂
      · exact h₁
    · intro T x q h
      have hw : (q ≫ pullback.fst (f ≫ g) g) ≫ (f ≫ g) = x ≫ (f ≫ g) := by
        calc
          _ = (q ≫ pullback.snd (f ≫ g) g) ≫ g := by
            simp only [Category.assoc, pullback.condition]
          _ = _ := by rw [← h, Category.assoc]
      refine ⟨pullback.lift (q ≫ pullback.fst (f ≫ g) g) x hw, by simp, ?_⟩
      apply pullback.hom_ext <;> simp [a, ← h]
  have hi : IsPullback (i f g) (pullback.fst f f) (a f g) (s f g) := by
    apply IsPullback.mk' (by apply pullback.hom_ext <;> simp [i, a, s])
    · intro T φ φ' h₁ h₂
      apply pullback.hom_ext h₂
      simpa [i] using congrArg (fun k ↦ k ≫ pullback.snd (f ≫ g) (f ≫ g)) h₁
    · intro T q x h
      have hfst : q ≫ pullback.fst (f ≫ g) (f ≫ g) = x := by
        simpa [a, s] using congrArg (fun k ↦ k ≫ pullback.fst (f ≫ g) g) h
      have hsnd : (q ≫ pullback.snd (f ≫ g) (f ≫ g)) ≫ f = x ≫ f := by
        simpa [a, s] using congrArg (fun k ↦ k ≫ pullback.snd (f ≫ g) g) h
      refine ⟨pullback.lift x (q ≫ pullback.snd (f ≫ g) (f ≫ g)) hsnd.symm, ?_, by simp⟩
      apply pullback.hom_ext <;> simp [i, hfst]
  have hj : IsPullback (j f g) (pullback.fst (f ≫ g) g) (pullback.fst g g) f := by
    apply IsPullback.mk' (by simp [j])
    · intro T φ φ' h₁ h₂
      apply pullback.hom_ext h₂
      simpa [j] using congrArg (fun k ↦ k ≫ pullback.snd g g) h₁
    · intro T q x h
      have hw : x ≫ (f ≫ g) = (q ≫ pullback.snd g g) ≫ g := by
        rw [← Category.assoc, ← h]
        simp only [Category.assoc, pullback.condition]
      refine ⟨pullback.lift x (q ≫ pullback.snd g g) hw, ?_, by simp⟩
      apply pullback.hom_ext <;> simp [j, h]
  refine ⟨ha, (IsPullback.of_hasPullback (f ≫ g) g).flip, hi, hj, ?_,
    pullback.diagonal_snd _, ?_, ?_, ?_, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp [a, s]
  · simp [s]
  · simp [a]
  · apply pullback.hom_ext <;> simp [i]
  · apply pullback.hom_ext
    · dsimp only [s, j, pullback.map]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.diagonal_fst, Category.comp_id]
      exact Category.id_comp f
    · simp [s, j]
  · simp [i]

/-- The smooth separated finite-type tower has dimensions d,e,d+e.
Source: latest blueprint, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-double-diagonal-section-identifications).
Proof: the first two squares of doubleDiagonalGeometry exhibit a and b as base
changes of f and g. Apply lem-sbc-smooth-relative-dimension-permanence and
lem-pod-separated-finite-type-base-change. Composition gives dimension d+e
and preserves separatedness and finite type. This works also for empty schemes
and zero relative dimension. -/
theorem doubleDiagonalProperties {X Y Z : Scheme.{u}} (d e : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] :
    SmoothOfRelativeDimension d (a f g) ∧ IsSeparated (a f g) ∧
    LocallyOfFiniteType (a f g) ∧ QuasiCompact (a f g) ∧
    SmoothOfRelativeDimension e (pullback.fst (f ≫ g) g) ∧
    IsSeparated (pullback.fst (f ≫ g) g) ∧
    LocallyOfFiniteType (pullback.fst (f ≫ g) g) ∧
    QuasiCompact (pullback.fst (f ≫ g) g) ∧
    SmoothOfRelativeDimension (d + e) (a f g ≫ pullback.fst (f ≫ g) g) ∧
    IsSeparated (a f g ≫ pullback.fst (f ≫ g) g) ∧
    LocallyOfFiniteType (a f g ≫ pullback.fst (f ≫ g) g) ∧
    QuasiCompact (a f g ≫ pullback.fst (f ≫ g) g) ∧
    SmoothOfRelativeDimension (d + e) (f ≫ g) := by
  have hs := (doubleDiagonalGeometry f g).1
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d (a f g) :=
    MorphismProperty.of_isPullback hs inferInstance
  have : IsSeparated (a f g) := MorphismProperty.of_isPullback hs inferInstance
  have : LocallyOfFiniteType (a f g) := MorphismProperty.of_isPullback hs inferInstance
  have : QuasiCompact (a f g) := MorphismProperty.of_isPullback hs inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The specified three restriction equations. All compactifications and dimensions
are consequences of the given setting, rather than additional hypotheses.
Source: latest blueprint, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-double-diagonal-section-identifications).
The first right side is gamma_f followed by inverse t^*A and lt=1. The second is
gamma_g followed by inverse s^*B and rs=f. The third is inverse t^*D and lt=1.
The already published gammaF and gammaG are exactly pullbacks of T_f inverse and T_g,
including the canonical composition comparisons. -/
def doubleDiagonalRestrictionEquations (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] : Prop :=
  letI := P.finiteComparedInvertibleExponent (𝟙 (Spec (.of P.field.k)))
  letI := LocallyOfFiniteType.isLocallyNoetherian aZ
  letI := QuasiCompact.compactSpace_of_compactSpace aZ
  letI : IsNoetherian Z := ⟨⟩
  letI := LocallyOfFiniteType.isLocallyNoetherian g
  letI := QuasiCompact.compactSpace_of_compactSpace g
  letI : IsNoetherian Y := ⟨⟩
  letI := LocallyOfFiniteType.isLocallyNoetherian f
  letI := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := ⟨⟩
  let hgeom := doubleDiagonalProperties d e f g
  letI := hgeom.1
  letI := hgeom.2.1
  letI := hgeom.2.2.1
  letI := hgeom.2.2.2.1
  letI := hgeom.2.2.2.2.2.2.2.2.2.2.2.2
  SameProEtaleMap P.Coefficient P
    (alpha P.Coefficient P d f (f ≫ g ≫ aZ)).hom
    (gammaF P.Coefficient P d f g aZ ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (pullback.diagonal (f ≫ g))).leftDerivedFunctor.mapIso
          (beta P.Coefficient P d (doubleDiagonalGeometry f g).1 (f ≫ g ≫ aZ)).symm ≪≫
      (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} P.Coefficient)
        (pullback.diagonal (f ≫ g)) (pullback.snd (f ≫ g) (f ≫ g))
        (pullback.diagonal_snd (f ≫ g))).app _).hom ∧
  SameProEtaleMap P.Coefficient P
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (alpha P.Coefficient P e g (g ≫ aZ))).hom
    (gammaG P.Coefficient P e f g aZ ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (s f g)).leftDerivedFunctor.mapIso
        (beta P.Coefficient P e (IsPullback.of_hasPullback (f ≫ g) g).flip
          (g ≫ aZ)).symm ≪≫
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        (s f g) (pullback.snd (f ≫ g) g) f
        (doubleDiagonalGeometry f g).2.2.2.2.2.2.1.symm).app _).symm).hom ∧
  SameProEtaleMap P.Coefficient P
    (alpha P.Coefficient P (d + e) (f ≫ g) ((f ≫ g) ≫ aZ)).hom
    ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (pullback.diagonal (f ≫ g))).leftDerivedFunctor.mapIso
      (beta P.Coefficient P (d + e)
        (IsPullback.of_hasPullback (f ≫ g) (f ≫ g)).flip ((f ≫ g) ≫ aZ)).symm ≪≫
      (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} P.Coefficient)
        (pullback.diagonal (f ≫ g)) (pullback.snd (f ≫ g) (f ≫ g))
        (pullback.diagonal_snd (f ≫ g))).app _).hom

/-- Specialize the reviewed horizontal pasting clause to the unit and normalize its unit maps. -/
private theorem smoothDualizingBaseCompCongr
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X₂ X₁ X Y₂ Y₁ Y : Scheme.{u}}
    [X₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₂ ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₂ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (h₂ : X₂ ⟶ Y₂) [h₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₂] [LocallyOfFiniteType h₂] [QuasiCompact h₂]
    (u₁ : X₁ ⟶ X) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (u₂ : X₂ ⟶ X₁) [u₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₂] [LocallyOfFiniteType u₂] [QuasiCompact u₂]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : Y₂ ⟶ Y₁) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    [HasCompactification h] [HasCompactification h₁] [HasCompactification h₂]
    (sq : IsPullback u₁ h₁ h v) (sq₁ : IsPullback u₂ h₂ h₁ w)
    (d d₁ d₂ : ℕ) [SmoothOfRelativeDimension d h]
    [SmoothOfRelativeDimension d₁ h₁] [SmoothOfRelativeDimension d₂ h₂]
    (v₀ : Y₂ ⟶ Y) (u₀ : X₂ ⟶ X) (hv : v₀ = w ≫ v) (hu : u₀ = u₂ ≫ u₁)
    (sq₀ : IsPullback u₀ h₂ h v₀) :
    Etale.dualizingComplexBaseChangeMap P.Coefficient sq₀ =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) u₂ u₁ u₀ hu).hom.app
        (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h) ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) u₂).leftDerivedFunctor.map
        (Etale.dualizingComplexBaseChangeMap P.Coefficient sq) ≫
      Etale.dualizingComplexBaseChangeMap P.Coefficient sq₁ := by
  subst v₀
  subst u₀
  let A := ModuleCat.{u + 1} P.Coefficient
  have := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  have := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y₁ ↘ Spec (.of P.field.k))
  have := QuasiCompact.compactSpace_of_compactSpace (Y₁ ↘ Spec (.of P.field.k))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y₂ ↘ Spec (.of P.field.k))
  have := QuasiCompact.compactSpace_of_compactSpace (Y₂ ↘ Spec (.of P.field.k))
  have hc : ProEtale.SmoothExceptionalPasting.Ctf P.Coefficient Y (𝟙_ _) :=
    ProEtale.DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.constructibleFiniteTor_unit P.Coefficient)
  have hbase := ProEtale.SmoothExceptionalPasting.smoothExceptionalBasePasting P
    h h₁ h₂ u₁ u₂ v w sq sq₁ (𝟙_ _) d d₁ d₂ hc
  have hctf := Etale.constructibleFiniteTor_leftDerivedUpperStar A w
    (Etale.constructibleFiniteTor_leftDerivedUpperStar A v
      (Etale.constructibleFiniteTor_unit P.Coefficient))
  have hp := Etale.plus_rightDerivedUpperShriek_obj A h₂ _ hctf.1.1.1
  have he := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hp).1 hbase
  have hu : (Etale.leftDerivedUpperStarComp A w v).hom.app (𝟙_ _) ≫
      (Etale.upperStar A w).leftDerivedFunctor.map
        (Etale.leftDerivedUpperStarUnitIso A v).hom ≫
      (Etale.leftDerivedUpperStarUnitIso A w).hom =
        (Etale.leftDerivedUpperStarUnitIso A (w ≫ v)).hom := by
    simpa only [Etale.leftDerivedUpperStarOplaxMonoidal_η] using
      (Etale.leftDerivedUpperStarComp_hom_app_unit A w v (w ≫ v) rfl)
  have hn := (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq₁).naturality
    (Etale.leftDerivedUpperStarUnitIso A v).hom
  simp only [Functor.comp_map] at hn
  have hex : (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient
      (sq₁.paste_horiz sq)).app (𝟙_ _) =
    (Etale.leftDerivedUpperStarComp A u₂ u₁).hom.app
        ((Etale.rightDerivedUpperShriek A h).obj (𝟙_ _)) ≫
      (Etale.upperStar A u₂).leftDerivedFunctor.map
        ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app (𝟙_ _)) ≫
      (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq₁).app
        ((Etale.upperStar A v).leftDerivedFunctor.obj (𝟙_ _)) ≫
      (Etale.rightDerivedUpperShriek A h₂).map
        ((Etale.leftDerivedUpperStarComp A w v).inv.app (𝟙_ _)) := by
    apply (cancel_mono ((Etale.rightDerivedUpperShriek A h₂).map
      ((Etale.leftDerivedUpperStarComp A w v).hom.app (𝟙_ _)))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact he
  unfold Etale.dualizingComplexBaseChangeMap Etale.dualizingComplex
  rw [hex]
  simp only [Category.assoc, Functor.map_comp]
  erw [reassoc_of% hn]
  rw [← hu]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Section coherence for a diagonal followed by the map between the two products. -/
private theorem sectionComp
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {B V W : Scheme.{u}} (δ : B ⟶ V) (i' : V ⟶ W) (l : W ⟶ B)
    (t : B ⟶ W) (l' : V ⟶ B) (ht : t = δ ≫ i') (hl : l' = i' ≫ l)
    (hδ : δ ≫ l' = 𝟙 B) (htl : t ≫ l = 𝟙 B)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)) :
    (Etale.upperStar A δ).leftDerivedFunctor.map
        ((Etale.leftDerivedUpperStarComp A i' l l' hl).inv.app K) ≫
      (Etale.leftDerivedUpperStarCompSectionIso A δ l' hδ).hom.app K =
    (Etale.leftDerivedUpperStarComp A δ i' t ht).inv.app
        ((Etale.upperStar A l).leftDerivedFunctor.obj K) ≫
      (Etale.leftDerivedUpperStarCompSectionIso A t l htl).hom.app K := by
  have ha := Etale.leftDerivedUpperStarComp_assoc'_app A
    δ i' l t l' (𝟙 B) ht hl htl.symm K
  have he :
      (Etale.leftDerivedUpperStarComp A δ l' (𝟙 B) hδ.symm).app K ≪≫
        (Etale.upperStar A δ).leftDerivedFunctor.mapIso
          ((Etale.leftDerivedUpperStarComp A i' l l' hl).app K) =
      (Etale.leftDerivedUpperStarComp A t l (𝟙 B) htl.symm).app K ≪≫
        (Etale.leftDerivedUpperStarComp A δ i' t ht).app _ := by
    apply Iso.ext
    exact ha
  have hi := congrArg (fun E ↦ E.inv ≫ (Etale.leftDerivedUpperStarId
    A B).hom.app K) he
  simpa only [Etale.leftDerivedUpperStarCompSectionIso, Iso.trans_inv,
    Iso.app_inv, Functor.mapIso_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] using hi

/-- Section coherence after changing the base of a diagonal. -/
private theorem sectionBaseComp
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {B B' V W : Scheme.{u}} (f : B' ⟶ B) (δ : B ⟶ V) (s' : B' ⟶ W)
    (j' : W ⟶ V) (l : V ⟶ B) (r : W ⟶ B)
    (hδ : δ ≫ l = 𝟙 B) (hj : f ≫ δ = s' ≫ j')
    (hr : r = j' ≫ l) (hs : f = s' ≫ r)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A)) :
    (Etale.leftDerivedUpperStarComp A s' j' (f ≫ δ) hj).hom.app
        ((Etale.upperStar A l).leftDerivedFunctor.obj K) ≫
      (Etale.upperStar A s').leftDerivedFunctor.map
        ((Etale.leftDerivedUpperStarComp A j' l r hr).inv.app K) ≫
      (Etale.leftDerivedUpperStarComp A s' r f hs).inv.app K =
    (Etale.leftDerivedUpperStarComp A f δ).hom.app
        ((Etale.upperStar A l).leftDerivedFunctor.obj K) ≫
      (Etale.upperStar A f).leftDerivedFunctor.map
        ((Etale.leftDerivedUpperStarCompSectionIso A δ l hδ).hom.app K) := by
  have ht : f = (f ≫ δ) ≫ l := by simp [Category.assoc, hδ]
  have h1 := Etale.leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    A s' j' l (f ≫ δ) r f hj hr ht K
  have h2 := Etale.leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    A f δ l (f ≫ δ) (𝟙 B) f rfl hδ.symm
      ht K
  rw [reassoc_of% h1]
  simp only [Iso.hom_inv_id_app, Category.comp_id]
  symm
  simp only [Etale.leftDerivedUpperStarCompSectionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, ← Category.assoc]
  rw [h2]
  simp only [Category.assoc, Etale.leftDerivedUpperStarComp_id_right_hom_app,
    Category.comp_id]

/-- Invert the first pasted beta identity and restrict along the diagonal. -/
private theorem restrictionComp
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {B V W : Scheme.{u}} (δ : B ⟶ V) (i' : V ⟶ W) (l : W ⟶ B)
    (t : B ⟶ W) (l' : V ⟶ B) (ht : t = δ ≫ i') (hl : l' = i' ≫ l)
    (hδ : δ ≫ l' = 𝟙 B) (htl : t ≫ l = 𝟙 B)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A))
    (H : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf V.smallEtaleTopology A))
    (E : (Etale.upperStar A l').leftDerivedFunctor.obj K ≅ M)
    (β : (Etale.upperStar A l).leftDerivedFunctor.obj K ≅ H)
    (T : (Etale.upperStar A i').leftDerivedFunctor.obj H ≅ M)
    (he : E = (Etale.leftDerivedUpperStarComp A i' l l' hl).app K ≪≫
      (Etale.upperStar A i').leftDerivedFunctor.mapIso β ≪≫ T) :
    (Etale.upperStar A δ).leftDerivedFunctor.map E.inv ≫
      (Etale.leftDerivedUpperStarCompSectionIso A δ l' hδ).hom.app K =
    (Etale.upperStar A δ).leftDerivedFunctor.map T.inv ≫
      (Etale.leftDerivedUpperStarComp A δ i' t ht).inv.app H ≫
      (Etale.upperStar A t).leftDerivedFunctor.map β.inv ≫
      (Etale.leftDerivedUpperStarCompSectionIso A t l htl).hom.app K := by
  rw [he]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp, Category.assoc]
  apply congrArg (fun z ↦
    (Etale.upperStar A δ).leftDerivedFunctor.map T.inv ≫ z)
  rw [sectionComp A δ i' l t l' ht hl hδ htl K]
  have hn := (Etale.leftDerivedUpperStarComp A δ i' t ht).inv.naturality
    β.inv
  simp only [Functor.comp_map] at hn
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
    (Etale.leftDerivedUpperStarCompSectionIso A t l htl).hom.app K) hn

/-- Restrict the second pasted beta identity and cancel its middle beta. -/
private theorem restrictionBaseComp
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {B B' V W : Scheme.{u}} (f : B' ⟶ B) (δ : B ⟶ V) (s' : B' ⟶ W)
    (j' : W ⟶ V) (l : V ⟶ B) (r : W ⟶ B)
    (hδ : δ ≫ l = 𝟙 B) (hj : f ≫ δ = s' ≫ j')
    (hr : r = j' ≫ l) (hs : f = s' ≫ r)
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology A))
    (H : _root_.DerivedCategory (Sheaf V.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    (E : (Etale.upperStar A l).leftDerivedFunctor.obj K ≅ H)
    (β : (Etale.upperStar A r).leftDerivedFunctor.obj K ≅ M)
    (T : (Etale.upperStar A j').leftDerivedFunctor.obj H ≅ M)
    (he : β = (Etale.leftDerivedUpperStarComp A j' l r hr).app K ≪≫
      (Etale.upperStar A j').leftDerivedFunctor.mapIso E ≪≫ T) :
    (Etale.upperStar A f).leftDerivedFunctor.map
      ((Etale.upperStar A δ).leftDerivedFunctor.map E.inv ≫
        (Etale.leftDerivedUpperStarCompSectionIso A δ l hδ).hom.app K) =
    (Etale.leftDerivedUpperStarComp A f δ).inv.app H ≫
      (Etale.leftDerivedUpperStarComp A s' j' (f ≫ δ) hj).hom.app H ≫
      (Etale.upperStar A s').leftDerivedFunctor.map T.hom ≫
      (Etale.upperStar A s').leftDerivedFunctor.map β.inv ≫
      (Etale.leftDerivedUpperStarComp A s' r f hs).inv.app K := by
  rw [he]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hn₁ := (Etale.leftDerivedUpperStarComp A s' j'
    (f ≫ δ) hj).hom.naturality E.inv
  have hn₂ := (Etale.leftDerivedUpperStarComp A f δ).inv.naturality E.inv
  simp only [Functor.comp_map] at hn₁ hn₂
  symm
  rw [← reassoc_of% hn₁, ← reassoc_of% hn₂]
  rw [sectionBaseComp A f δ s' j' l r hδ hj hr hs K]
  simp only [Iso.inv_hom_id_app_assoc]


/-- The specified orientation-free diagonal restrictions through the two squares.
Source: latest blueprint, thm-pur-composition-coherence, proof Step 1
(blueprint: lem-pur-double-diagonal-section-identifications).
Proof: doubleDiagonalGeometry gives the four Cartesian squares and section identities;
doubleDiagonalProperties gives smoothness, dimensions and separated finite type.
Smooth cohomological duality makes A,B,D,T_f,T_g invertible. The etale-origin
witness of each dualizing object puts the compact-support exchange on its stated
domain. Write E_f=beta_(f,f) and E_g=beta_(g,g). Diagonal base change defines
alpha_h as the inverse pullback of E_h followed by the section comparison.
Horizontal counit-mate pasting (lem-pur-smooth-exceptional-tensor-pasting), first
for (f,r) then (a,s), gives E_f=T_f after i^*A. Pull along Delta_f, use i Delta_f=t
and invert to obtain alpha_f=(t^*A)^(-1) gamma_f. Pasting (g,g) then (p_g,f) gives
B=T_g after j^*E_g. Pull along s, use js=Delta_g f and invert to obtain
f^*alpha_g=(s^*B)^(-1) gamma_g. For gf, D=E_gf and t=Delta_gf, so its equation
is the defining diagonal restriction itself. Pullback composition and identity
comparisons are the canonical derived ones throughout. No twist is used. -/
theorem doubleDiagonalSectionIdentifications (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    doubleDiagonalRestrictionEquations P d e f g aZ := by
  have := P.finiteComparedInvertibleExponent (𝟙 (Spec (.of P.field.k)))
  have := LocallyOfFiniteType.isLocallyNoetherian aZ
  have := QuasiCompact.compactSpace_of_compactSpace aZ
  have : IsNoetherian Z := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Y := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hg := doubleDiagonalProperties d e f g
  have := hg.1
  have := hg.2.1
  have := hg.2.2.1
  have := hg.2.2.2.1
  have := hg.2.2.2.2.2.2.2.2.2.2.2.2
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (f ≫ g) g)
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (f ≫ g) g)
  have : IsNoetherian (pullback (f ≫ g) g) := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (f ≫ g) (f ≫ g))
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (f ≫ g) (f ≫ g))
  have : IsNoetherian (pullback (f ≫ g) (f ≫ g)) := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f)
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  have : IsNoetherian (pullback f f) := ⟨⟩
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g g)
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst g g)
  have : IsNoetherian (pullback g g) := ⟨⟩
  let : Z.Over (Spec (.of P.field.k)) := ⟨aZ⟩
  let : Y.Over (Spec (.of P.field.k)) := ⟨g ≫ aZ⟩
  let : X.Over (Spec (.of P.field.k)) := ⟨f ≫ g ≫ aZ⟩
  let : (pullback (f ≫ g) g).Over (Spec (.of P.field.k)) :=
    ⟨pullback.snd (f ≫ g) g ≫ g ≫ aZ⟩
  let : (pullback (f ≫ g) (f ≫ g)).Over (Spec (.of P.field.k)) :=
    ⟨pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ⟩
  let : (pullback f f).Over (Spec (.of P.field.k)) :=
    ⟨pullback.snd f f ≫ f ≫ g ≫ aZ⟩
  let : (pullback g g).Over (Spec (.of P.field.k)) :=
    ⟨pullback.snd g g ≫ g ≫ aZ⟩
  have : IsClosedImmersion (s f g) := by dsimp only [s]; infer_instance
  have : IsClosedImmersion (i f g) :=
    MorphismProperty.of_isPullback (geometry f g).1.flip inferInstance
  have : IsSeparated (j f g) :=
    MorphismProperty.of_isPullback (geometry f g).2.1.flip inferInstance
  have : LocallyOfFiniteType (j f g) :=
    MorphismProperty.of_isPullback (geometry f g).2.1.flip inferInstance
  have : QuasiCompact (j f g) :=
    MorphismProperty.of_isPullback (geometry f g).2.1.flip inferInstance
  have : (f).IsOver (Spec (.of P.field.k)) := by
    constructor
    change f ≫ (g ≫ aZ) = f ≫ g ≫ aZ
    exact rfl
  have : (g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change g ≫ aZ = g ≫ aZ
    exact rfl
  have : (a f g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change a f g ≫ (pullback.snd (f ≫ g) g ≫ g ≫ aZ) =
      pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ
    exact by simp [a]
  have : (pullback.fst f f).IsOver (Spec (.of P.field.k)) := by
    constructor
    change pullback.fst f f ≫ (f ≫ g ≫ aZ) = pullback.snd f f ≫ f ≫ g ≫ aZ
    exact by rw [← Category.assoc, pullback.condition]; simp only [Category.assoc]
  have : (pullback.fst g g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change pullback.fst g g ≫ (g ≫ aZ) = pullback.snd g g ≫ g ≫ aZ
    exact by rw [← Category.assoc, pullback.condition]; simp only [Category.assoc]
  have : (pullback.snd g g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change pullback.snd g g ≫ (g ≫ aZ) = pullback.snd g g ≫ g ≫ aZ
    exact rfl
  have : (pullback.fst (f ≫ g) g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change pullback.fst (f ≫ g) g ≫ (f ≫ g ≫ aZ) =
      pullback.snd (f ≫ g) g ≫ g ≫ aZ
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ aZ) (pullback.condition (f := f ≫ g) (g := g))
  have : (pullback.snd (f ≫ g) (f ≫ g)).IsOver (Spec (.of P.field.k)) := by
    constructor
    change pullback.snd (f ≫ g) (f ≫ g) ≫ (f ≫ g ≫ aZ) =
      pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ
    exact rfl
  have : (pullback.snd (f ≫ g) g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change pullback.snd (f ≫ g) g ≫ (g ≫ aZ) =
      pullback.snd (f ≫ g) g ≫ g ≫ aZ
    exact rfl
  have : (i f g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change i f g ≫ (pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ) =
      pullback.snd f f ≫ f ≫ g ≫ aZ
    exact by simp [i]
  have : (s f g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change s f g ≫ (pullback.snd (f ≫ g) g ≫ g ≫ aZ) = f ≫ g ≫ aZ
    exact by simp [s]
  have : (j f g).IsOver (Spec (.of P.field.k)) := by
    constructor
    change j f g ≫ (pullback.snd g g ≫ g ≫ aZ) =
      pullback.snd (f ≫ g) g ≫ g ≫ aZ
    exact by simp [j]
  have : LocallyOfFiniteType ((Z) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (aZ))
  have : QuasiCompact ((Z) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (aZ))
  have : LocallyOfFiniteType ((Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g ≫ aZ))
  have : QuasiCompact ((Y) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g ≫ aZ))
  have : LocallyOfFiniteType ((X) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ g ≫ aZ))
  have : QuasiCompact ((X) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (f ≫ g ≫ aZ))
  have : LocallyOfFiniteType ((pullback (f ≫ g) g) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (f ≫ g) g ≫ g ≫ aZ))
  have : QuasiCompact ((pullback (f ≫ g) g) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd (f ≫ g) g ≫ g ≫ aZ))
  have : LocallyOfFiniteType ((pullback (f ≫ g) (f ≫ g)) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ))
  have : QuasiCompact ((pullback (f ≫ g) (f ≫ g)) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd (f ≫ g) (f ≫ g) ≫ f ≫ g ≫ aZ))
  have : LocallyOfFiniteType ((pullback f f) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f f ≫ f ≫ g ≫ aZ))
  have : QuasiCompact ((pullback f f) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd f f ≫ f ≫ g ≫ aZ))
  have : LocallyOfFiniteType ((pullback g g) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd g g ≫ g ≫ aZ))
  have : QuasiCompact ((pullback g g) ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd g g ≫ g ≫ aZ))
  have hli : pullback.snd f f = i f g ≫ pullback.snd (f ≫ g) (f ≫ g) :=
    (doubleDiagonalGeometry f g).2.2.2.2.2.2.2.2.2.2.symm
  have hsr : f = s f g ≫ pullback.snd (f ≫ g) g :=
    (doubleDiagonalGeometry f g).2.2.2.2.2.2.1.symm
  have hjl : pullback.snd (f ≫ g) g = j f g ≫ pullback.snd g g := by simp [j]
  dsimp only [doubleDiagonalRestrictionEquations]
  refine ⟨?_, ?_, ?_⟩
  · apply congrArg _
    let A := ModuleCat.{u + 1} P.Coefficient
    let E := beta P.Coefficient P d (IsPullback.of_hasPullback f f).flip
      (f ≫ g ≫ aZ)
    let B := beta P.Coefficient P d (doubleDiagonalGeometry f g).1 (f ≫ g ≫ aZ)
    let T := beta P.Coefficient P d (geometry f g).1
      (pullback.fst (f ≫ g) (f ≫ g) ≫ (f ≫ g) ≫ aZ)
    let c := (Etale.leftDerivedUpperStarComp A (i f g)
      (pullback.snd (f ≫ g) (f ≫ g)) (pullback.snd f f) hli).app
        (Etale.dualizingComplex A f)
    have he : E = c ≪≫ (Etale.upperStar A (i f g)).leftDerivedFunctor.mapIso B ≪≫ T := by
      apply Iso.ext
      exact smoothDualizingBaseCompCongr P f (a f g) (pullback.fst f f)
        (pullback.snd (f ≫ g) (f ≫ g)) (i f g) (pullback.snd (f ≫ g) g) (s f g)
        (doubleDiagonalGeometry f g).1 (geometry f g).1 d d d f (pullback.snd f f)
        hsr hli
        (IsPullback.of_hasPullback f f).flip
    change (Etale.upperStar A (pullback.diagonal f)).leftDerivedFunctor.map E.inv ≫
      (Etale.leftDerivedUpperStarCompSectionIso A (pullback.diagonal f)
        (pullback.snd f f) (pullback.diagonal_snd f)).hom.app _ = _
    dsimp only [gammaF, diagonalSection, Etale.sectionInvariant]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Category.assoc]
    exact restrictionComp A (pullback.diagonal f) (i f g)
      (pullback.snd (f ≫ g) (f ≫ g)) (pullback.diagonal (f ≫ g))
      (pullback.snd f f) (geometry f g).2.2.2.2.1.symm hli
      (pullback.diagonal_snd f) (pullback.diagonal_snd (f ≫ g)) _ _ _ E B T he
  · apply congrArg _
    let A := ModuleCat.{u + 1} P.Coefficient
    let E := beta P.Coefficient P e (IsPullback.of_hasPullback g g).flip (g ≫ aZ)
    let B := beta P.Coefficient P e (IsPullback.of_hasPullback (f ≫ g) g).flip (g ≫ aZ)
    let T := beta P.Coefficient P e (geometry f g).2.1 (pullback.fst g g ≫ g ≫ aZ)
    let c := (Etale.leftDerivedUpperStarComp A (j f g) (pullback.snd g g)
      (pullback.snd (f ≫ g) g) hjl).app (Etale.dualizingComplex A g)
    have he : B = c ≪≫ (Etale.upperStar A (j f g)).leftDerivedFunctor.mapIso E ≪≫ T := by
      apply Iso.ext
      exact smoothDualizingBaseCompCongr P g (pullback.fst g g)
        (pullback.fst (f ≫ g) g) (pullback.snd g g) (j f g) g f
        (IsPullback.of_hasPullback g g).flip (geometry f g).2.1 e e e (f ≫ g)
        (pullback.snd (f ≫ g) g) rfl hjl
        (IsPullback.of_hasPullback (f ≫ g) g).flip
    change _ = (gammaG P.Coefficient P e f g aZ ≪≫
      (Etale.upperStar A (s f g)).leftDerivedFunctor.mapIso B.symm ≪≫ _).hom
    dsimp only [gammaG, alpha, finiteDiagonalRestriction, diagonalSection, Etale.sectionInvariant]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
      Category.assoc]
    exact restrictionBaseComp A f (pullback.diagonal g) (s f g) (j f g)
      (pullback.snd g g) (pullback.snd (f ≫ g) g) (pullback.diagonal_snd g)
      (geometry f g).2.2.2.2.2.symm hjl hsr _ _ _ E B T he
  · rfl

end WeilConjectures.PurityFiniteSetting.DiagonalPasting
