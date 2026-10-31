/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.ProperBaseChange.LocalizeRingedSiteMorphismGeneral
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization

/-! # Graph summands for arbitrary inverse systems of rings

Source: Stacks Project, Tags 0F4L, 0F4Y, 0GKM and 09AF; blueprint main-20261015,
`det-sp-tower-gluing`, Local pairs and Levels. Index n denotes the source level n+1
(blueprint: lem-sp-varying-ring-graph-summand).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRingGraph

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Composition with the etale structure map, retaining the index.
Source: Stacks 03DI and 09AE (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev sumSite {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (𝟭 ℕ).prod (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))

private theorem sequence_sheaf_of_slices {D : Type*} [Category* D]
    (J : GrothendieckTopology D)
    (P : (ℕ × D)ᵒᵖ ⥤ Type*)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n D).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 D).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 D)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 D).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 D).map g₁) ((Prod.sectR X.1 D).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 D).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 D).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 D).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 D).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 D).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 D).map f) hf

/-- Continuity of the localization inclusion on the vertical sequence site.
Source: Stacks 03DI, 09AE (blueprint: lem-sp-varying-ring-graph-summand).
Proof: composition with e preserves the fpqc covering condition, since the underlying
covering maps and covered schemes are unchanged. The sequence topology tests covers
on one vertical slice, where this is precisely continuity of composition. -/
theorem sumSite_continuous {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (sumSite e).IsContinuous (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology T)) := by
  constructor
  intro P
  apply sequence_sheaf_of_slices
  intro n
  have : (Prod.sectR n T.ProEt).IsContinuous (ProEt.topology T)
      (coefficientSequenceTopology (ProEt.topology T)) :=
    SemilinearSections.evaluationContinuous.{u + 1, u, u + 1} (ProEt.topology T) n
  let Q : Sheaf (ProEt.topology T) (Type (u + 1)) :=
    ⟨(Prod.sectR n T.ProEt).op ⋙ P.obj,
      (Prod.sectR n T.ProEt).op_comp_isSheaf _ _ P⟩
  exact (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).op_comp_isSheaf_of_types
    (ProEt.topology U) (ProEt.topology T) Q

attribute [instance] sumSite_continuous

/-- Canonical restriction of the constant ring, induced by the sheafification unit.
Source: Stacks 00XZ, 0H7J (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelCoefficientMap {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :
    SemilinearProperOpen.coefficients C U n ⟶
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).sheafPushforwardContinuous
        CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).obj
          (SemilinearProperOpen.coefficients C T n) :=
  ((sheafificationAdjunction (ProEt.topology U) CommRingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).op
      (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (C n))))

private theorem levelCoefficientMap_naturality {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] {m n : ℕ} (a : C m ⟶ C n) :
    (constantSheaf (ProEt.topology U) CommRingCat.{u + 1}).map a ≫
        levelCoefficientMap C e n =
      levelCoefficientMap C e m ≫
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).sheafPushforwardContinuous
          CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).map
          ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction (ProEt.topology U) CommRingCat.{u + 1}).homEquiv
    ((Functor.const U.ProEtᵒᵖ).obj (C m)) _).injective
  change ((sheafificationAdjunction (ProEt.topology U) CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf (ProEt.topology U) CommRingCat.{u + 1}).map
      ((Functor.const U.ProEtᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [levelCoefficientMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext W
  exact congrArg (fun f ↦ f.app
    ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).op.obj W))
      ((toSheafification (ProEt.topology T) CommRingCat.{u + 1}).naturality
        ((Functor.const T.ProEtᵒᵖ).map a))

/-- Restricting constant coefficients respects all horizontal and vertical arrows.
Source: Stacks 00XZ; Zheng Construction 4.1
(blueprint: lem-sp-varying-ring-graph-summand).
Proof: vertical naturality is that of levelCoefficientMap. For a horizontal arrow,
use naturality of the sheafification adjunction in C_n and the given transition.
Their composites agree on constant sections, which determine a constant-sheaf map. -/
theorem coefficientMap_naturality {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    {X Y : (ℕ × U.ProEt)ᵒᵖ} (f : X ⟶ Y) :
    (SemilinearProperOpen.ringSystem C τ U).obj.map f ≫
        (levelCoefficientMap C e Y.unop.1).hom.app (op Y.unop.2) =
      (levelCoefficientMap C e X.unop.1).hom.app (op X.unop.2) ≫
        (SemilinearProperOpen.ringSystem C τ T).obj.map ((sumSite e).op.map f) := by
  let δ : rings (ProEt.topology U) (SemilinearProperOpen.coefficients C U)
      (SemilinearProperOpen.transition C τ U) ⟶
      rings (ProEt.topology T) (SemilinearProperOpen.coefficients C T)
        (SemilinearProperOpen.transition C τ T) ⋙
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).sheafPushforwardContinuous
            CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology T) :=
    NatTrans.ofOpSequence (fun n ↦ levelCoefficientMap C e n) (by
      intro n
      dsimp only [rings, Functor.comp_map]
      simp only [Functor.ofOpSequence_map_homOfLE_succ]
      exact levelCoefficientMap_naturality C e (τ n))
  let ε := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := U.ProEt)).functor
    (Functor.uncurry.map
      (Functor.whiskerRight δ (sheafToPresheaf (ProEt.topology U) CommRingCat.{u + 1})))
  exact ε.naturality f

/-- The actual coefficient map on sequence sites, with no choice of scalar actions.
Source: Stacks 03DI, 00XZ (blueprint: lem-sp-varying-ring-graph-summand). -/
def sumCoefficientMap {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    SemilinearProperOpen.ringSystem C τ U ⟶
      ((sumSite e).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology U))
        (coefficientSequenceTopology (ProEt.topology T))).obj
          (SemilinearProperOpen.ringSystem C τ T) :=
  ⟨{ app X := (levelCoefficientMap C e X.unop.1).hom.app (op X.unop.2)
     naturality _ _ f := coefficientMap_naturality C τ e f }⟩

private theorem levelCoefficientMap_unit {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] (n : ℕ) (W : U.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj (C n))).app W ≫
        (levelCoefficientMap C e n).hom.app W =
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (C n))).app
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).op.obj W) := by
  have h := ((sheafificationAdjunction (ProEt.topology U)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const U.ProEtᵒᵖ).obj (C n))
      (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).sheafPushforwardContinuous
        CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).obj
          (SemilinearProperOpen.coefficients C T n))).apply_symm_apply
      (Functor.whiskerLeft
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).op
        (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj (C n))))
  exact congrArg (fun f ↦ f.app W) h

private theorem levelDirectCoefficientMap_unit {U T : Scheme.{u}}
    (e : U ⟶ T) (n : ℕ) (V : T.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (C n))).app V ≫
        (proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (C n)).hom.app V =
      (toSheafify (ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (C n))).app ((proEtaleBaseChange e).op.obj V) := by
  have h := ((sheafificationAdjunction (ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const T.ProEtᵒᵖ).obj (C n))
      ((proEtaleSheafDirectImage e CommRingCat.{u + 1}).obj
        (SemilinearProperOpen.coefficients C U n))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange e).op
        (toSheafify (ProEt.topology U) ((Functor.const U.ProEtᵒᵖ).obj (C n))))
  exact congrArg (fun f ↦ f.app V) h

private theorem levelCoefficientMap_counit {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] (n : ℕ) :
    Functor.whiskerRight (NatTrans.op
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
        (inferInstance : WeaklyEtale e) trivial).counit)
          (SemilinearProperOpen.coefficients C T n).obj =
      (proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (C n)).hom ≫
        (proEtaleBaseChange e).op.whiskerLeft (levelCoefficientMap C e n).hom := by
  let Q := ((proEtaleBaseChange e).sheafPushforwardContinuous CommRingCat.{u + 1}
    (ProEt.topology T) (ProEt.topology U)).obj
      (((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).sheafPushforwardContinuous
        CommRingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).obj
          (SemilinearProperOpen.coefficients C T n))
  apply sheafify_hom_ext (ProEt.topology T) _ _ Q.property
  apply NatTrans.ext
  funext V
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, levelDirectCoefficientMap_unit]
  erw [levelCoefficientMap_unit]
  have h := (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (C n))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
        (inferInstance : WeaklyEtale e) trivial).counit.app V.unop).op
  simpa [SemilinearProperOpen.coefficients, constantSheaf, proEtaleBaseChange] using h.symm

private theorem levelCoefficientMap_triangle {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] (n : ℕ) :
    (levelCoefficientMap C e n).hom ≫
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).op.whiskerLeft
        (proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (C n)).hom ≫
      Functor.whiskerRight (NatTrans.op
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
          (inferInstance : WeaklyEtale e) trivial).unit)
            (SemilinearProperOpen.coefficients C U n).obj = 𝟙 _ := by
  apply sheafify_hom_ext (ProEt.topology U) _ _
    (SemilinearProperOpen.coefficients C U n).property
  apply NatTrans.ext
  funext W
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app]
  rw [← Category.assoc, ← Category.assoc, levelCoefficientMap_unit]
  erw [levelDirectCoefficientMap_unit]
  have h := (toSheafify (ProEt.topology U)
    ((Functor.const U.ProEtᵒᵖ).obj (C n))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
        (inferInstance : WeaklyEtale e) trivial).unit.app W.unop).op
  simpa [SemilinearProperOpen.coefficients, constantSheaf, proEtaleBaseChange] using h.symm

private theorem ringSystem_vertical_map (X : Scheme.{u}) (n : ℕ)
    {V W : X.ProEt} (a : V ⟶ W) :
    (SemilinearProperOpen.ringSystem C τ X).obj.map (Prod.mkHom (𝟙 n) a).op =
      (SemilinearProperOpen.coefficients C X n).obj.map a.op := by
  change ((rings (ProEt.topology X) (SemilinearProperOpen.coefficients C X)
      (SemilinearProperOpen.transition C τ X)).map (𝟙 (op n))).hom.app (op W) ≫
    (SemilinearProperOpen.coefficients C X n).obj.map a.op = _
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- Restriction to the localization, including the semilinear transition maps.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev sumRestriction {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    SemilinearProperOpen.Modules C τ T ⥤ SemilinearProperOpen.Modules C τ U :=
  letI := sumSite_continuous e
  SheafOfModules.pushforward (F := sumSite e)
    (J := coefficientSequenceTopology (ProEt.topology U))
    (K := coefficientSequenceTopology (ProEt.topology T))
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (sumCoefficientMap C τ e))

/-- Module Kan extension followed by sheafification exists at the original site sizes.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand).
Proof: the localization identifies the source with the slice at e. At every index,
the extension presheaf is the direct sum over lifts to e. Its summand universal
property and module sheafification give the left adjoint simultaneously on systems.
The construction stays in u+1; the Hom universe of the site remains u. -/
theorem sumRestriction_isRightAdjoint {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (sumRestriction C τ e).IsRightAdjoint := by
  have := sumSite_continuous e
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
    (J := coefficientSequenceTopology (ProEt.topology U))
    (K := coefficientSequenceTopology (ProEt.topology T)) (U := sumSite e)
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (SemilinearProperOpen.ringSystem C τ U))
    (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (SemilinearProperOpen.ringSystem C τ T))
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (sumCoefficientMap C τ e))

attribute [instance] sumRestriction_isRightAdjoint

/-- Sheafified module left Kan extension along the localization inclusion. Its adjunction
uniquely determines it up to the unit-preserving isomorphism, as for Mathlib's pullback.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev sum {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (sumRestriction C τ e).leftAdjoint

/-- The actual module-sheafification adjunction, with its summand unit.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
def sumAdjunction {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    sum C τ e ⊣ sumRestriction C τ e := Adjunction.ofIsRightAdjoint _

/-- Exactness of the sheafified direct-sum extension for arbitrary transition homomorphisms.
Source: Stacks 03DI--03DJ; Zheng 4.1
(blueprint: lem-sp-varying-ring-graph-summand).
Proof: localized extension is exact at each coefficient ring. Kernels and sheafified
cokernels of strict systems are componentwise, by semilinearDerivedSections. This
proves exactness on systems without assuming coefficient transitions flat. -/
theorem sum_exact {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (sum C τ e).Additive ∧ PreservesFiniteLimits (sum C τ e) ∧
      PreservesFiniteColimits (sum C τ e) := by
  have : (sumRestriction C τ e).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have : (sum C τ e).Additive := (sumAdjunction C τ e).left_adjoint_additive
  refine ⟨inferInstance, ?_⟩
  obtain ⟨D⟩ := semilinearDerivedSections.{u + 1, u, u + 1}
    (ProEt.topology T) (SemilinearProperOpen.coefficients C T)
      (SemilinearProperOpen.transition C τ T)
  exact VaryingRing.exact_of_componentwise
    (A := SemilinearProperOpen.Modules C τ U)
    (B := SemilinearProperOpen.Modules C τ T)
    (C := fun n ↦ StrictTower.Modules (C n) U)
    (D := fun n ↦ StrictTower.Modules (C n) T)
    (sum C τ e) (ev C τ T) (ev C τ U) (fun n ↦ levelSum (C n) e)
    D.systems.componentwise
    (fun n ↦ (@asIso _ _ _ _ (sumEvaluationInv C τ e n)
      (sumEvaluationInv_isIso C τ e n)).symm)

/-- Additive structure supplied by the exact sum extension.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
instance sum_additive {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (sum C τ e).Additive := (sum_exact C τ e).1

/-- Exactness component of sum extension.
Source: Stacks 03DJ (blueprint: lem-sp-varying-ring-graph-summand). -/
instance sum_limits {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteLimits (sum C τ e) := (sum_exact C τ e).2.1

/-- Exactness component of sum extension.
Source: Stacks 03DJ (blueprint: lem-sp-varying-ring-graph-summand). -/
instance sum_colimits {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    PreservesFiniteColimits (sum C τ e) := (sum_exact C τ e).2.2

/-- The underlying section identification for localization restriction.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
def restrictionSections {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (M : SemilinearProperOpen.Modules C τ T) (n : ℕ) (W : U.ProEt) :
    ((sumRestriction C τ e).obj M).val.obj (op (n, W)) ≃
      M.val.obj (op ((sumSite e).obj (n, W))) :=
  Equiv.cast (show _ = _ from rfl)

/-- The underlying section identification for system direct image.
Source: Stacks 03D7 (blueprint: lem-sp-varying-ring-graph-summand). -/
def pushSections {U T : Scheme.{u}} (f : U ⟶ T)
    (M : SemilinearProperOpen.Modules C τ U) (n : ℕ) (V : T.ProEt) :
    ((SemilinearProperOpen.push C τ f).obj M).val.obj (op (n, V)) ≃
      M.val.obj (op (n, (proEtaleBaseChange f).obj V)) :=
  Equiv.cast (show _ = _ from rfl)

/-- Inclusion of the summand of a lift, via the Kan-extension/sheafification unit.
Source: Stacks 03DI and 0F4L (blueprint: lem-sp-varying-ring-graph-summand). -/
def generator {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (M : SemilinearProperOpen.Modules C τ U) (n : ℕ) (W : U.ProEt)
    (m : M.val.obj (op (n, W))) :
    ((sum C τ e).obj M).val.obj (op ((sumSite e).obj (n, W))) :=
  restrictionSections C τ e ((sum C τ e).obj M) n W
    (((sumAdjunction C τ e).unit.app M).val.app (op (n, W)) m)

set_option maxHeartbeats 800000 in
-- Elaborate the product-site coefficient identities and their module adjunction together.
/-- The localization/direct-image adjunction is fixed by restriction along the
site adjunction counit; this normalization does not identify abstract section carriers.
Source: Stacks 09AE, 00XZ (blueprint: lem-route-restriction-push-adjunction-exists-unique).
Proof: composition with e is left adjoint to base change on pro-etale objects.
The sectionwise Hom correspondence for precomposition gives the sheaf adjunction.
Both scalar maps preserve constant sections, so the correspondence is module-linear
and commutes with horizontal transitions. The displayed unit determines it uniquely. -/
theorem restrictionPushAdjunction_existsUnique {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    ∃! a : sumRestriction C τ e ⊣ SemilinearProperOpen.push C τ e,
      ∀ (M : SemilinearProperOpen.Modules C τ T) (n : ℕ) (V : T.ProEt)
        (x : M.val.obj (op (n, V))),
        pushSections C τ e ((sumRestriction C τ e).obj M) n V
          ((a.unit.app M).val.app (op (n, V)) x) =
        (restrictionSections C τ e M n ((proEtaleBaseChange e).obj V)).symm
          (M.val.presheaf.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
              (inferInstance : WeaklyEtale e) trivial).counit.app V)).op x) := by
  let := sumSite_continuous e
  let := SemilinearProperOpen.siteMap_continuous e
  let a₀ := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
    (inferInstance : WeaklyEtale e) trivial
  let adj : sumSite e ⊣ SemilinearProperOpen.siteMap e :=
    { unit :=
        { app := fun X ↦ Prod.mkHom (𝟙 X.1) (a₀.unit.app X.2)
          naturality := by
            intro X Y f
            apply Prod.hom_ext
            · simp
            · exact a₀.unit.naturality f.2 }
      counit :=
        { app := fun X ↦ Prod.mkHom (𝟙 X.1) (a₀.counit.app X.2)
          naturality := by
            intro X Y f
            apply Prod.hom_ext
            · simp
            · exact a₀.counit.naturality f.2 }
      left_triangle_components := by
        intro X
        apply Prod.hom_ext
        · simp
        · exact a₀.left_triangle_components X.2
      right_triangle_components := by
        intro X
        apply Prod.hom_ext
        · simp
        · exact a₀.right_triangle_components X.2 }
  let φ : ((sheafCompose (coefficientSequenceTopology (ProEt.topology U))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (SemilinearProperOpen.ringSystem C τ U)) ⟶
      ((sumSite e).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology U))
        (coefficientSequenceTopology (ProEt.topology T))).obj
          ((sheafCompose (coefficientSequenceTopology (ProEt.topology T))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (SemilinearProperOpen.ringSystem C τ T)) :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (sumCoefficientMap C τ e)
  let ψ : ((sheafCompose (coefficientSequenceTopology (ProEt.topology T))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (SemilinearProperOpen.ringSystem C τ T)) ⟶
      ((SemilinearProperOpen.siteMap e).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
        (coefficientSequenceTopology (ProEt.topology U))).obj
          ((sheafCompose (coefficientSequenceTopology (ProEt.topology U))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (SemilinearProperOpen.ringSystem C τ U)) :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (SemilinearProperOpen.coefficientMap C τ e)
  have hψ (X : (ℕ × T.ProEt)ᵒᵖ) :
      (SemilinearProperOpen.coefficientMap C τ e).hom.app X =
        (proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (C X.unop.1)).hom.app
          (op X.unop.2) :=
    eq_of_heq ((SemilinearProperOpen.coefficientMap_existsUnique C τ e).choose_spec.1
      X.unop.1 X.unop.2)
  have h₁ : Functor.whiskerRight (NatTrans.op adj.counit)
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (SemilinearProperOpen.ringSystem C τ T)).obj =
      ψ.hom ≫ (SemilinearProperOpen.siteMap e).op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map _ =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((SemilinearProperOpen.coefficientMap C τ e).hom.app X) ≫ _
    rw [hψ]
    change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((SemilinearProperOpen.ringSystem C τ T).obj.map
        (Prod.mkHom (𝟙 X.unop.1) (a₀.counit.app X.unop.2)).op) = _
    erw [ringSystem_vertical_map]
    exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (t.app (op X.unop.2))) (levelCoefficientMap_counit C e X.unop.1)
  have h₂ : φ.hom ≫ (sumSite e).op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit)
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (SemilinearProperOpen.ringSystem C τ U)).obj = 𝟙 _ := by
    apply NatTrans.ext
    funext X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.id_app]
    change _ ≫ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((SemilinearProperOpen.coefficientMap C τ e).hom.app ((sumSite e).op.obj X)) ≫ _ = _
    rw [hψ]
    change _ ≫ _ ≫ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((SemilinearProperOpen.ringSystem C τ U).obj.map
        (Prod.mkHom (𝟙 X.unop.1) (a₀.unit.app X.unop.2)).op) = _
    erw [ringSystem_vertical_map]
    exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (t.app (op X.unop.2))) (levelCoefficientMap_triangle C e X.unop.1)
  let a := SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψ h₁ h₂
  refine ⟨a, ?_, ?_⟩
  · intro M n V x
    rfl
  · intro b hb
    apply Adjunction.ext
    ext M V x
    exact hb M V.unop.1 V.unop.2 x

/-- The section-normalized ordinary localization adjunction.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-graph-summand). -/
def restrictionPushAdjunction {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (restrictionPushAdjunction_existsUnique C τ e).exists.choose

/-- The unique adjunction-preserving identification with geometric inverse image.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-graph-summand). -/
def restrictionComparison {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :=
  (SemilinearProperOpen.ordinaryAdj C τ e).leftAdjointUniq
    (restrictionPushAdjunction C τ e)

/-- Sum extension adjoint to the existing geometric inverse image.
Source: Stacks 03DI, 09AE (blueprint: lem-sp-varying-ring-graph-summand). -/
def geometricSumAdjunction {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    sum C τ e ⊣ SemilinearProperOpen.pull C τ e :=
  (sumAdjunction C τ e).ofNatIsoRight (restrictionComparison C τ e).symm

/-- The compactified graph of a lift, in the variable-first fibre-product convention.
Source: Stacks 0F4L (blueprint: lem-sp-varying-ring-graph-summand). -/
def graph {U T : Scheme.{u}} {e : U ⟶ T} (c : Compactification e)
    (V : T.ProEt) (t : V.left ⟶ U) (ht : t ≫ e = V.hom) :
    V.left ⟶ ((proEtaleBaseChange c.g).obj V).left :=
  pullback.lift (𝟙 V.left) (t ≫ c.i)
    ((Category.id_comp V.hom).trans (ht.symm.trans
      ((congrArg (fun f ↦ t ≫ f) c.comm).trans (Category.assoc t c.i c.g).symm)))

/-- The graph as a morphism on the compactification's small pro-etale site.
Source: Stacks 0F4L (blueprint: lem-sp-varying-ring-graph-summand). -/
def graphArrow {U T : Scheme.{u}} {e : U ⟶ T} [Etale e] (c : Compactification e)
    (W : U.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale c.i)).obj W ⟶
      (proEtaleBaseChange c.g).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).obj W) :=
  MorphismProperty.Over.homMk
    (graph c ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).obj W)
      W.hom rfl) (pullback.lift_snd _ _ _)

/-- The graph restrictions uniquely specify the natural module-sheaf map.
Source: Stacks 0F4L, 0F4Y (blueprint: lem-sp-varying-ring-graph-summand).
Proof: the graph and its complement are a disjoint open cover. Glue the image of m
under the open-extension unit on the graph and zero on the complement. The sheaf
condition gives existence and uniqueness. This construction is additive and linear in
the scalar map for each lift. Sum the extensions on the direct-sum presheaf, then
use module sheafification. Graphs pull back to graphs, so the maps commute with all
site restrictions. Uniqueness also makes them commute with sheaf morphisms and
with every semilinear transition, without flatness. The summand units generate
locally, so these restrictions determine the entire natural transformation. -/
theorem graphMap_existsUnique {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    ∃! γ : sum C τ e ⟶
      SemilinearProperOpen.extension C τ c.i ⋙ SemilinearProperOpen.push C τ c.g,
      ∀ (M : SemilinearProperOpen.Modules C τ U) (n : ℕ) (W : U.ProEt)
        (m : M.val.obj (op (n, W))),
      ((SemilinearProperOpen.extension C τ c.i).obj M).val.presheaf.map
          (Prod.mkHom (𝟙 n) (graphArrow c W)).op
          (pushSections C τ c.g ((SemilinearProperOpen.extension C τ c.i).obj M) n
            ((sumSite e).obj (n, W)).2
            ((γ.app M).val.app (op ((sumSite e).obj (n, W)))
              (generator C τ e M n W m))) =
        restrictionSections C τ c.i ((SemilinearProperOpen.extension C τ c.i).obj M) n W
          ((((SemilinearProperOpen.ordinaryOpenAdj C τ c.i).unit.app M ≫
            (restrictionComparison C τ c.i).hom.app
              ((SemilinearProperOpen.extension C τ c.i).obj M)).val.app (op (n, W))) m) ∧
      ∀ (Z : c.Z.ProEt)
        (a : Z ⟶ (proEtaleBaseChange c.g).obj ((sumSite e).obj (n, W)).2),
        Set.range a.left ⊆ (Set.range (graphArrow c W).left)ᶜ →
        ((SemilinearProperOpen.extension C τ c.i).obj M).val.presheaf.map
          (Prod.mkHom (𝟙 n) a).op
          (pushSections C τ c.g ((SemilinearProperOpen.extension C τ c.i).obj M) n
            ((sumSite e).obj (n, W)).2
            ((γ.app M).val.app (op ((sumSite e).obj (n, W)))
              (generator C τ e M n W m))) = 0 := by
  sorry

/-- The canonical graph map, selected by its unique clopen-gluing characterization.
Source: Stacks 0F4L (blueprint: lem-sp-varying-ring-graph-summand). -/
def graphMap {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :=
  (graphMap_existsUnique C τ e c).exists.choose

/-- The specified representative word: apply the graph map degreewise, then the
right-derived direct-image comparison. It is defined on unbounded homotopy representatives.
Source: Stacks 0GKM; Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def onHomotopy {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (K : HomotopyCategory (SemilinearProperOpen.Modules C τ U) (.up ℤ)) :
    (sum C τ e).mapDerivedCategory.obj (DerivedCategory.Qh.obj K) ⟶
      (SemilinearProperOpen.J C τ c.i ⋙ SemilinearProperOpen.R C τ c.g).obj
        (DerivedCategory.Qh.obj K) :=
  (sum C τ e).mapDerivedCategoryFactorsh.hom.app K ≫
    DerivedCategory.Qh.map (((graphMap C τ e c).mapHomotopyCategory (.up ℤ)).app K) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) ≫
    (SemilinearProperOpen.push C τ c.g).rightDerivedFunctorUnit.app
      (((SemilinearProperOpen.extension C τ c.i).mapHomotopyCategory (.up ℤ)).obj K) ≫
    (SemilinearProperOpen.push C τ c.g).rightDerivedFunctor.map
      ((SemilinearProperOpen.extension C τ c.i).mapDerivedCategoryFactorsh.inv.app K)

/-- The representative graph word descends uniquely to the ordinary derived category.
Source: Stacks 0GKM; Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand).
Proof: exact sum extension descends termwise, as does open extension. The unit to
the total right derived direct image is natural. Composing with the degreewise
graph map gives onHomotopy, which respects quasi-isomorphisms in its source by
exactness. The localization universal property gives the transformation and its
uniqueness. There is no claim that arbitrary derived maps are detected by levels. -/
theorem theta_existsUnique {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    ∃! θ : (sum C τ e).mapDerivedCategory ⟶
      SemilinearProperOpen.J C τ c.i ⋙ SemilinearProperOpen.R C τ c.g,
      ∀ K : HomotopyCategory (SemilinearProperOpen.Modules C τ U) (.up ℤ),
        θ.app (DerivedCategory.Qh.obj K) = onHomotopy C τ e c K := by
  let α :=
    (sum C τ e).mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight ((graphMap C τ e c).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv
        DerivedCategory.Qh ≫
      Functor.whiskerLeft ((SemilinearProperOpen.extension C τ c.i).mapHomotopyCategory (.up ℤ))
        (SemilinearProperOpen.push C τ c.g).rightDerivedFunctorUnit ≫
      Functor.whiskerRight (SemilinearProperOpen.extension C τ c.i).mapDerivedCategoryFactorsh.inv
        (SemilinearProperOpen.push C τ c.g).rightDerivedFunctor
  have := Localization.full_whiskeringLeft
    (DerivedCategory.Qh (C := SemilinearProperOpen.Modules C τ U))
    (HomotopyCategory.quasiIso (SemilinearProperOpen.Modules C τ U) (.up ℤ))
    (DerivedCategory (SemilinearProperOpen.Modules C τ T))
  let θ : (sum C τ e).mapDerivedCategory ⟶
      SemilinearProperOpen.J C τ c.i ⋙ SemilinearProperOpen.R C τ c.g :=
    ((Functor.whiskeringLeft _ _ (DerivedCategory (SemilinearProperOpen.Modules C τ T))).obj
      (DerivedCategory.Qh (C := SemilinearProperOpen.Modules C τ U))).preimage α
  have hθ : Functor.whiskerLeft DerivedCategory.Qh θ = α :=
    ((Functor.whiskeringLeft _ _ (DerivedCategory (SemilinearProperOpen.Modules C τ T))).obj
      (DerivedCategory.Qh (C := SemilinearProperOpen.Modules C τ U))).map_preimage
        (X := (sum C τ e).mapDerivedCategory)
        (Y := SemilinearProperOpen.J C τ c.i ⋙ SemilinearProperOpen.R C τ c.g) α
  refine ⟨θ, ?_, ?_⟩
  · intro K
    exact congr_app hθ K
  · intro θ' hθ'
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ))
    intro K
    exact (hθ' K).trans (congr_app hθ K).symm

/-- The uniquely representative-normalized graph natural transformation.
Source: Stacks 0GKM (blueprint: lem-sp-varying-ring-graph-summand). -/
def theta {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :=
  (theta_existsUnique C τ e c).exists.choose

/-- Continuity of the etale localization inclusion at every auxiliary sheaf universe.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-graph-summand).
Proof: the localization equivalence preserves covers; forgetting its slice structure
therefore preserves the sheaf condition, with values in any category of types. -/
theorem levelSite_continuous {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).IsContinuous
      (ProEt.topology U) (ProEt.topology T) := by
  exact ProEt.isContinuous_overMap (inferInstance : WeaklyEtale e)

attribute [instance] levelSite_continuous

/-- The single-ring localization restriction with its canonical coefficient map.
Source: Stacks 03DI, 09AE (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev levelRestriction (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    StrictTower.Modules A T ⥤ StrictTower.Modules A U :=
  letI := levelSite_continuous e
  SheafOfModules.pushforward (F := MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale e)) (J := ProEt.topology U) (K := ProEt.topology T)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (levelCoefficientMap (fun _ : ℕ ↦ CommRingCat.of A) e 0))

/-- Underlying sections of single-ring localization restriction.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelRestrictionSections (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (M : StrictTower.Modules A T) (W : U.ProEt) :
    ((levelRestriction A e).obj M).val.obj (op W) ≃
      M.val.obj (op ((MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale e)).obj W)) :=
  Equiv.cast (show _ = _ from rfl)

/-- Underlying sections of single-ring direct image.
Source: Stacks 03D7 (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelPushSections (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (f : U ⟶ T) (M : StrictTower.Modules A U) (V : T.ProEt) :
    ((StrictTower.moduleDirectImage A f).obj M).val.obj (op V) ≃
      M.val.obj (op ((proEtaleBaseChange f).obj V)) :=
  Equiv.cast (show _ = _ from rfl)

/-- The single-ring localization adjunction is uniquely fixed by section restriction.
Source: Stacks 09AE, 00XZ (blueprint: lem-sp-graph-level-restriction-adjunction).
Proof: the site adjunction between composition and base change gives this Hom
bijection by precomposition. Its unit is restriction along the site counit.
Constant sections identify both scalar maps, giving module-linearity. Section
components determine the unit and hence the adjunction uniquely. -/
theorem levelRestrictionAdjunction_existsUnique (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    ∃! a : levelRestriction A e ⊣ StrictTower.moduleDirectImage A e,
      ∀ (M : StrictTower.Modules A T) (V : T.ProEt) (x : M.val.obj (op V)),
        levelPushSections A e ((levelRestriction A e).obj M) V
          ((a.unit.app M).val.app (op V) x) =
        (levelRestrictionSections A e M ((proEtaleBaseChange e).obj V)).symm
          (M.val.presheaf.map
            ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
              (inferInstance : WeaklyEtale e) trivial).counit.app V).op x) := by
  let D := fun _ : ℕ ↦ CommRingCat.of A
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
    (inferInstance : WeaklyEtale e) trivial
  let φ : ((sheafCompose (ProEt.topology U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (StrictTower.coefficients A U)) ⟶
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology U) (ProEt.topology T)).obj
          ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (StrictTower.coefficients A T)) :=
    ⟨Functor.whiskerRight (levelCoefficientMap D e 0).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (StrictTower.coefficients A T)) ⟶
      ((proEtaleBaseChange e).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology T) (ProEt.topology U)).obj
          ((sheafCompose (ProEt.topology U)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (StrictTower.coefficients A U)) :=
    ⟨Functor.whiskerRight
      (proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (CommRingCat.of A)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hψ : proEtaleRingDirectImageMap e (StrictTower.coefficients A T)
      (StrictTower.coefficients A U) (StrictTower.constantRingIso A e) =
      proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (CommRingCat.of A) := by
    exact Equiv.apply_symm_apply ((proEtaleSheafAdjunction e
      CommRingCat.{u + 1}).homEquiv _ _)
      (proEtaleConstantDirectImageMap e CommRingCat.{u + 1} (CommRingCat.of A))
  let ψ' := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (proEtaleRingDirectImageMap e (StrictTower.coefficients A T)
      (StrictTower.coefficients A U) (StrictTower.constantRingIso A e))
  have hψ' : ψ' = ψ := by
    dsimp only [ψ']
    rw [hψ]
    rfl
  let a := SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψ'
    (by rw [hψ']; exact congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) (levelCoefficientMap_counit D e 0))
    (by rw [hψ']; exact congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) (levelCoefficientMap_triangle D e 0))
  refine ⟨a, ?_, ?_⟩
  · intro M V x
    rfl
  · intro b hb
    apply Adjunction.ext
    ext M V x
    exact hb M V.unop x

/-- The normalized identification of geometric inverse image with localization restriction.
Source: Stacks 09AE (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelRestrictionComparison (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    StrictTower.modulePullback A e ≅ levelRestriction A e :=
  (proEtaleRingModuleAdjunction e (StrictTower.coefficients A T)
    (StrictTower.coefficients A U) (StrictTower.constantRingIso A e)).leftAdjointUniq
      (levelRestrictionAdjunction_existsUnique A e).exists.choose

set_option maxHeartbeats 800000 in
-- Relate the large constant-coefficient sheaf carriers to the localized module adjunction.
/-- At a single coefficient ring, inverse image has the sheafified-sum left adjoint.
Source: Stacks 03DI, 09AE (blueprint: lem-sp-varying-ring-graph-summand).
Proof: weakly-etale localization identifies inverse image with slice restriction.
Transport the actual localizedSystemExtension and its normalized summand adjunction. -/
theorem levelPull_isRightAdjoint (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (StrictTower.modulePullback A e).IsRightAdjoint := by
  have : MorphismProperty.IsStableUnderComposition
      (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).IsContinuous
      (ProEt.topology U) (ProEt.topology T) := levelSite_continuous e
  have h :=
    SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
      (J := ProEt.topology U) (K := ProEt.topology T)
      (U := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (SemilinearProperOpen.coefficients (fun _ : ℕ ↦ CommRingCat.of A) U 0))
      (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (SemilinearProperOpen.coefficients (fun _ : ℕ ↦ CommRingCat.of A) T 0))
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (levelCoefficientMap (fun _ : ℕ ↦ CommRingCat.of A) e 0))
  have : (levelRestriction A e).IsRightAdjoint := h
  exact Functor.isRightAdjoint_of_iso (levelRestrictionComparison A e).symm

attribute [instance] levelPull_isRightAdjoint

/-- The single-ring sum extension, by its localized module-sheafification universal property.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev levelSum (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}} (e : U ⟶ T)
    [Etale e] := (StrictTower.modulePullback A e).leftAdjoint

/-- The normalized single-ring sum adjunction.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelSumAdjunction (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] : levelSum A e ⊣ StrictTower.modulePullback A e :=
  Adjunction.ofIsRightAdjoint _

/-- Exactness at one ring, with no finiteness or Noetherian assumption on that ring.
Source: Stacks 03DI--03DJ (blueprint: lem-sp-varying-ring-graph-summand).
Proof: identify levelSum with localizedSystemExtension by their normalized adjunctions.
The exactness statement localizedSystemExact transports along that isomorphism. -/
theorem levelSum_exact (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] :
    (levelSum A e).Additive ∧ PreservesFiniteLimits (levelSum A e) ∧
      PreservesFiniteColimits (levelSum A e) := by
  let W : T.ProEt := MorphismProperty.Over.mk ⊤ e (inferInstance : WeaklyEtale e)
  let G := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)
  let : G.IsContinuous (ProEt.topology U) (ProEt.topology T) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale e)
  let : G.IsCocontinuous (ProEt.topology U) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale e)
  let B := StrictTower.coefficients A T
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let S := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (StrictTower.coefficients A U)
  let c₀ := (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology U) (ProEt.topology T)).app
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))
  have hc : c₀.hom = levelCoefficientMap (fun _ : ℕ ↦ CommRingCat.of A) e 0 := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology U) _ _
      ((G.sheafPushforwardContinuous CommRingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology T)).obj B).property
    apply NatTrans.ext
    funext V
    have h := congrArg (fun f ↦ f.app V)
      (G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
        (ProEt.topology U) (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A)))
    exact h.trans (levelCoefficientMap_unit (fun _ : ℕ ↦ CommRingCat.of A) e 0 V).symm
  let c : S ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U) (ProEt.topology T)).obj R :=
    (sheafCompose (ProEt.topology U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c₀
  let hd : (ProEt.sliceEquiv T W).inverse.IsDenseSubsite
      (ProEt.topology U) ((ProEt.topology T).over W) := by
    exact ProEt.sliceDense T W
  obtain ⟨q, hq⟩ := ProEt.module_transport ((ProEt.topology T).over W)
    (ProEt.topology U) (ProEt.sliceEquiv T W) (R.over W) S c
  let t : SheafOfModules.overFunctor.{u + 1} R W ⋙ q.functor ≅
      levelRestriction A e :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget S) (eqToIso (by
      change SheafOfModules.overFunctor R W ⋙
        (q.functor ⋙ SheafOfModules.forget S) = _
      rw [hq]
      dsimp only [levelRestriction]
      rw [← hc]
      rfl))
  obtain ⟨ha, hl, hcol, _⟩ := SheafOfModules.localizedSystemExact.{u + 1, u, u + 1} B W
  let := ha
  let := hl
  let := hcol
  let a := ((q.symm.toAdjunction).comp
    (SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1} B W)).ofNatIsoRight t
  let b := (levelSumAdjunction A e).ofNatIsoRight (levelRestrictionComparison A e)
  let d := a.leftAdjointUniq b
  have : PreservesFiniteLimits (levelSum A e) := preservesFiniteLimits_of_natIso d
  have : PreservesFiniteColimits (levelSum A e) := preservesFiniteColimits_of_natIso d
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of single-ring sum extension.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
instance levelSum_additive (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] : (levelSum A e).Additive := (levelSum_exact A e).1

/-- Left exactness of single-ring sum extension.
Source: Stacks 03DJ (blueprint: lem-sp-varying-ring-graph-summand). -/
instance levelSum_limits (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] : PreservesFiniteLimits (levelSum A e) := (levelSum_exact A e).2.1

/-- Right exactness of single-ring sum extension.
Source: Stacks 03DJ (blueprint: lem-sp-varying-ring-graph-summand). -/
instance levelSum_colimits (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] : PreservesFiniteColimits (levelSum A e) := (levelSum_exact A e).2.2

/-- A lift summand at a single ring, in the fixed geometric inverse-image coordinates.
Source: Stacks 03DI (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelGenerator (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (M : StrictTower.Modules A U) (W : U.ProEt) (m : M.val.obj (op W)) :
    ((levelSum A e).obj M).val.obj (op ((MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale e)).obj W)) :=
  levelRestrictionSections A e ((levelSum A e).obj M) W
    ((((levelSumAdjunction A e).unit.app M ≫
      (levelRestrictionComparison A e).hom.app ((levelSum A e).obj M)).val.app (op W)) m)

/-- Unique single-ring graph map, fixed on all lift summands by clopen gluing.
Source: Stacks 0F4L, 0F4Y (blueprint: lem-sp-varying-ring-graph-summand).
Proof: glue the open-extension unit section on the graph and zero on its complement.
The clopen sheaf decomposition makes this unique and linear. Summing over lifts
and sheafifying gives the map from the localized sum. Graph pullback and uniqueness
give naturality in test objects and module sheaves. The summands generate locally,
which proves uniqueness of the natural transformation. -/
theorem levelGraphMap_existsUnique (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    ∃! γ : levelSum A e ⟶ StrictTower.moduleJ A c.i ⋙ StrictTower.moduleDirectImage A c.g,
      ∀ (M : StrictTower.Modules A U) (W : U.ProEt) (m : M.val.obj (op W)),
      ((StrictTower.moduleJ A c.i).obj M).val.presheaf.map (graphArrow c W).op
        (levelPushSections A c.g ((StrictTower.moduleJ A c.i).obj M)
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).obj W)
          ((γ.app M).val.app (op ((MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale e)).obj W)) (levelGenerator A e M W m))) =
        levelRestrictionSections A c.i ((StrictTower.moduleJ A c.i).obj M) W
          ((((StrictTower.moduleJAdj A c.i).unit.app M ≫
            (levelRestrictionComparison A c.i).hom.app
              ((StrictTower.moduleJ A c.i).obj M)).val.app (op W)) m) ∧
      ∀ (Z : c.Z.ProEt) (a : Z ⟶ (proEtaleBaseChange c.g).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).obj W)),
        Set.range a.left ⊆ (Set.range (graphArrow c W).left)ᶜ →
        ((StrictTower.moduleJ A c.i).obj M).val.presheaf.map a.op
          (levelPushSections A c.g ((StrictTower.moduleJ A c.i).obj M)
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e)).obj W)
            ((γ.app M).val.app (op ((MorphismProperty.Over.map ⊤
              (inferInstance : WeaklyEtale e)).obj W)) (levelGenerator A e M W m))) = 0 := by
  sorry

/-- The uniquely graph-normalized single-ring natural transformation.
Source: Stacks 0F4L (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelGraphMap (A : Type (u + 1)) [CommRing A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :=
  (levelGraphMap_existsUnique A e c).exists.choose

/-- The single-ring degreewise graph word followed by the derived direct-image unit.
Source: Stacks 0GKM (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelOnHomotopy (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e)
    (K : HomotopyCategory (StrictTower.Modules A U) (.up ℤ)) :
    (levelSum A e).mapDerivedCategory.obj (DerivedCategory.Qh.obj K) ⟶
      ((StrictTower.moduleJ A c.i).mapDerivedCategory ⋙
        (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor).obj
          (DerivedCategory.Qh.obj K) :=
  (levelSum A e).mapDerivedCategoryFactorsh.hom.app K ≫
    DerivedCategory.Qh.map (((levelGraphMap A e c).mapHomotopyCategory (.up ℤ)).app K) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K) ≫
    (StrictTower.moduleDirectImage A c.g).rightDerivedFunctorUnit.app
      (((StrictTower.moduleJ A c.i).mapHomotopyCategory (.up ℤ)).obj K) ≫
    (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor.map
      ((StrictTower.moduleJ A c.i).mapDerivedCategoryFactorsh.inv.app K)

/-- The single-ring graph transformation is uniquely fixed on all homotopy representatives.
Source: Stacks 0GKM (blueprint: lem-sp-varying-ring-graph-summand).
Proof: apply localization uniqueness to the degreewise graph map followed by the total
right-derived unit. Sum and open extension are exact, so their source descends termwise. -/
theorem levelTheta_existsUnique (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e) :
    ∃! θ : (levelSum A e).mapDerivedCategory ⟶
      (StrictTower.moduleJ A c.i).mapDerivedCategory ⋙
        (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor,
      ∀ K : HomotopyCategory (StrictTower.Modules A U) (.up ℤ),
        θ.app (DerivedCategory.Qh.obj K) = levelOnHomotopy A e c K := by
  let α :=
    (levelSum A e).mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight ((levelGraphMap A e c).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv
        DerivedCategory.Qh ≫
      Functor.whiskerLeft ((StrictTower.moduleJ A c.i).mapHomotopyCategory (.up ℤ))
        (StrictTower.moduleDirectImage A c.g).rightDerivedFunctorUnit ≫
      Functor.whiskerRight (StrictTower.moduleJ A c.i).mapDerivedCategoryFactorsh.inv
        (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor
  have := Localization.full_whiskeringLeft (DerivedCategory.Qh (C := StrictTower.Modules A U))
    (HomotopyCategory.quasiIso (StrictTower.Modules A U) (.up ℤ))
    (DerivedCategory (StrictTower.Modules A T))
  let θ : (levelSum A e).mapDerivedCategory ⟶
      (StrictTower.moduleJ A c.i).mapDerivedCategory ⋙
      (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor :=
    ((Functor.whiskeringLeft _ _ (DerivedCategory (StrictTower.Modules A T))).obj
      (DerivedCategory.Qh (C := StrictTower.Modules A U))).preimage α
  have hθ : Functor.whiskerLeft DerivedCategory.Qh θ = α :=
    ((Functor.whiskeringLeft _ _ (DerivedCategory (StrictTower.Modules A T))).obj
      (DerivedCategory.Qh (C := StrictTower.Modules A U))).map_preimage
        (X := (levelSum A e).mapDerivedCategory)
        (Y := (StrictTower.moduleJ A c.i).mapDerivedCategory ⋙
          (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor) α
  refine ⟨θ, ?_, ?_⟩
  · intro K
    exact congr_app hθ K
  · intro θ' hθ'
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ))
    intro K
    exact (hθ' K).trans (congr_app hθ K).symm

/-- The unique single-ring graph natural transformation.
Source: Stacks 0GKM (blueprint: lem-sp-varying-ring-graph-summand). -/
def levelTheta (A : Type (u + 1)) [CommRing A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e) := (levelTheta_existsUnique A e c).exists.choose

/-- Ordinary evaluation of strict systems at n, in the existing constant-ring coordinates.
Source: Zheng 4.1 (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev ev (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    (ProEt.topology X) (SemilinearProperOpen.coefficients C X)
      (SemilinearProperOpen.transition C τ X) n

/-- Exact derived evaluation, in the ordinary derived category of modules at C_n.
Source: Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev Ev (X : Scheme.{u}) (n : ℕ) := (ev C τ X n).mapDerivedCategory

/-- Ordinary inverse-image evaluation, obtained from the published normalized comparison
by evaluating its constant diagram at zero; this recovers the single module category.
Source: Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def ordinaryPullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    SemilinearProperOpen.pull C τ f ⋙ ev C τ X n ≅
      ev C τ Y n ⋙ StrictTower.modulePullback (C n) f :=
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (SemilinearProperOpen.evalPullInv C τ n f)
      (SemilinearProperOpen.evalPullInv_isIso C τ n f)).symm
    ((evaluation ℕᵒᵖ (StrictTower.Modules (C n) X)).obj (op 0))

/-- The ordinary sum-evaluation comparison is the inverse mate of inverse-image evaluation.
Source: Stacks 03DI; Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def sumEvaluationInv {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :
    ev C τ U n ⋙ levelSum (C n) e ⟶ sum C τ e ⋙ ev C τ T n :=
  (mateEquiv (geometricSumAdjunction C τ e) (levelSumAdjunction (C n) e)).symm
    (ordinaryPullEvaluation C τ e n).hom

private theorem inverse_mate_right_transport
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R R' : B ⥤ A} {l : D ⥤ E} {r r' : E ⥤ D}
    {F : A ⥤ D} {G : B ⥤ E}
    (a : L ⊣ R) (b : l ⊣ r) (i : R ≅ R') (j : r ≅ r')
    (d : R' ⋙ F ⟶ G ⋙ r) :
    ((mateEquiv (a.ofNatIsoRight i) b).symm d).natTrans =
      ((mateEquiv a (b.ofNatIsoRight j)).symm
        (Functor.whiskerRight i.hom F ≫ d ≫ Functor.whiskerLeft G j.hom)).natTrans := by
  ext X
  simp only [mateEquiv_symm_apply, TwoSquare.mk, TwoSquare.natTrans,
    Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Functor.comp_map, Category.id_comp, Category.assoc,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  rw [← l.map_comp_assoc (j.hom.app _) (j.inv.app _), Iso.hom_inv_id_app,
    l.map_id, Category.id_comp]

/-- Sum extension commutes with evaluation by its summand units.
Source: Stacks 03DI; Zheng 4.10
(blueprint: lem-sp-graph-sum-evaluation-mate-invertible).
Proof: apply the sequence-site evaluation theorem to the canonical localization
restrictions and their chosen left adjoints. Transport their right adjoints by
restrictionComparison and levelRestrictionComparison. Expanding the inverse-mate
formula cancels the latter comparison with its inverse, yielding sumEvaluationInv. -/
theorem sumEvaluationInv_isIso {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :
    IsIso (sumEvaluationInv C τ e n) := by
  have := levelSite_continuous e
  have : ((𝟭 ℕ).prod (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale e))).IsContinuous
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceTopology (ProEt.topology T)) := sumSite_continuous e
  let i := (restrictionComparison C τ e).symm
  let j := levelRestrictionComparison (C n) e
  let d := Functor.isoWhiskerRight i (ev C τ U n) ≪≫
    ordinaryPullEvaluation C τ e n ≪≫ Functor.isoWhiskerLeft (ev C τ T n) j
  have h := WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
    (ProEt.topology U) (ProEt.topology T)
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology U))
      (SemilinearProperOpen.ringSystem C τ U))
    (ring.{u + 1, u, u + 1} (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearProperOpen.ringSystem C τ T)) n
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (sumCoefficientMap C τ e))
    (ring.{u + 1, u, u + 1} (ProEt.topology U)
      (SemilinearProperOpen.coefficients C U n))
    (ring.{u + 1, u, u + 1} (ProEt.topology T)
      (SemilinearProperOpen.coefficients C T n))
    (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology U)
      (SemilinearProperOpen.coefficients C U) (SemilinearProperOpen.transition C τ U) n)
    (evaluation_ring.{u + 1, u, u + 1} (ProEt.topology T)
      (SemilinearProperOpen.coefficients C T) (SemilinearProperOpen.transition C τ T) n)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (levelCoefficientMap C e n))
    (sum C τ e) (levelSum (C n) e) (sumAdjunction C τ e)
    ((levelSumAdjunction (C n) e).ofNatIsoRight j) d
  change IsIso ((mateEquiv ((sumAdjunction C τ e).ofNatIsoRight i)
    (levelSumAdjunction (C n) e)).symm (ordinaryPullEvaluation C τ e n).hom).natTrans
  rw [inverse_mate_right_transport (sumAdjunction C τ e)
    (levelSumAdjunction (C n) e) i j]
  exact h

set_option backward.isDefEq.respectTransparency true in
/-- Ordinary open-evaluation inverse comparison, preserving both open adjunctions.
Source: Stacks 03DI; Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def openEvaluationInv {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    ev C τ U n ⋙ StrictTower.moduleJ (C n) j ⟶
      SemilinearProperOpen.extension C τ j ⋙ ev C τ T n :=
  (mateEquiv (SemilinearProperOpen.ordinaryOpenAdj C τ j)
    (StrictTower.moduleJAdj (C n) j)).symm (ordinaryPullEvaluation C τ j n).hom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 64 in
set_option maxHeartbeats 800000 in
-- Compare the chosen adjoints and normalized constant-diagram square before taking its mate.
private theorem ordinary_open_eval_aux {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ)
    (F : SemilinearProperOpen.Modules C τ U ⥤ SemilinearProperOpen.Modules C τ T)
    [F.IsRightAdjoint] [F.leftAdjoint.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ j)
    (d : SemilinearProperOpen.levelTower C τ n U ⋙ StrictTower.towerDirectImage (C n) j ≅
      F ⋙ SemilinearProperOpen.levelTower C τ n T)
    (hd : ∀ (M : SemilinearProperOpen.Modules C τ U) (m : ℕ) (V : T.ProEt),
      HEq (fun x ↦ ((d.hom.app M).app (op m)).val.app (op V) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange j).obj V)) ↦ x)) :
    let s := (mateEquiv (Adjunction.ofIsRightAdjoint F)
      ((proEtaleRingModuleAdjunction j (StrictTower.coefficients (C n) T)
        (StrictTower.coefficients (C n) U)
        (StrictTower.constantRingIso (C n) j)).whiskerRight ℕᵒᵖ)).symm d.inv
    ∀ hs : IsIso s,
    IsIso ((mateEquiv (G := ev C τ U n) (H := ev C τ T n)
      (Adjunction.ofIsRightAdjoint F.leftAdjoint) (StrictTower.moduleJAdj (C n) j)).symm
      (Functor.whiskerRight (@asIso _ _ _ _ s hs).inv
        ((evaluation ℕᵒᵖ (StrictTower.Modules (C n) U)).obj (op 0)))) := by
  subst F
  intro s hs
  have he : s = (_root_.constant_diagram_square
      (VaryingRing.pull C τ j) (VaryingRing.eval C τ U n) (VaryingRing.eval C τ T n)
      (StrictTower.modulePullback (C n) j) (VaryingRing.moduleEvalG C τ j n)).inv :=
    SemilinearProperOpen.eval_pull_mate_normalization C τ n j d hd
  have hi : @asIso _ _ _ _ s hs = (_root_.constant_diagram_square
      (VaryingRing.pull C τ j) (VaryingRing.eval C τ U n) (VaryingRing.eval C τ T n)
      (StrictTower.modulePullback (C n) j) (VaryingRing.moduleEvalG C τ j n)).symm :=
    Iso.ext he
  rw [hi]
  change IsIso ((mateEquiv (VaryingRing.moduleJAdj C τ j)
    (StrictTower.moduleJAdj (C n) j)).symm (VaryingRing.moduleEvalG C τ j n).hom)
  exact VaryingRing.ordinaryOpenMateIso C τ j n

/-- The open-evaluation comparison is invertible before derivation.
Source: Stacks 03DI; Zheng 4.10 (blueprint: lem-sp-graph-open-evaluation-mate-invertible).
Proof: restriction, its summand extension and sheafification are componentwise.
Both adjunction units are the same single-lift inclusion. Thus their mate identifies
the same extension on every section, with inverse from that localization identification. -/
theorem openEvaluationInv_isIso {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) : IsIso (openEvaluationInv C τ j n) := by
  exact ordinary_open_eval_aux C τ j n (SemilinearProperOpen.push C τ j)
    (SemilinearProperOpen.push_eq C τ j)
    (SemilinearProperOpen.evalPushOrdinary_existsUnique C τ n j).choose
    (SemilinearProperOpen.evalPushOrdinary_existsUnique C τ n j).choose_spec.1
    (SemilinearProperOpen.evalPullInv_isIso C τ n j)

/-- Exact derived evaluation of open extension, retaining the ordinary normalization.
Source: Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def openEvaluation {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    SemilinearProperOpen.J C τ j ⋙ Ev C τ T n ≅
      Ev C τ U n ⋙ (StrictTower.moduleJ (C n) j).mapDerivedCategory :=
  letI : (StrictTower.moduleJ (C n) j).Additive := StrictTower.moduleJ_additive (C n) j
  letI : PreservesFiniteLimits (StrictTower.moduleJ (C n) j) :=
    StrictTower.moduleJ_finiteLimits (C n) j
  letI : PreservesFiniteColimits (StrictTower.moduleJ (C n) j) :=
    StrictTower.moduleJ_finiteColimits (C n) j
  (Functor.mapDerivedCategoryCompIso (SemilinearProperOpen.extension C τ j) (ev C τ T n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (openEvaluationInv C τ j n)
        (openEvaluationInv_isIso C τ j n)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (ev C τ U n) (StrictTower.moduleJ (C n) j)

/-- Derived inverse-image evaluation, by termwise localization of the ordinary comparison.
Source: Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def pullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    SemilinearProperOpen.P C τ f ⋙ Ev C τ X n ≅
      Ev C τ Y n ⋙ (StrictTower.modulePullback (C n) f).mapDerivedCategory :=
  letI : (StrictTower.modulePullback (C n) f).Additive :=
    StrictTower.modulePullback_additive (C n) f
  letI : PreservesFiniteLimits (StrictTower.modulePullback (C n) f) :=
    StrictTower.modulePullback_finiteLimits (C n) f
  letI : PreservesFiniteColimits (StrictTower.modulePullback (C n) f) :=
    StrictTower.modulePullback_finiteColimits (C n) f
  (Functor.mapDerivedCategoryCompIso (SemilinearProperOpen.pull C τ f) (ev C τ X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryPullEvaluation C τ f n) ≪≫
      Functor.mapDerivedCategoryCompIso (ev C τ Y n) (StrictTower.modulePullback (C n) f)

/-- Derived direct-image evaluation is its specified derived-adjunction mate.
Source: Zheng 4.10 (blueprint: lem-sp-varying-ring-graph-summand). -/
def pushEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    SemilinearProperOpen.R C τ f ⋙ Ev C τ Y n ⟶
      Ev C τ X n ⋙ (StrictTower.moduleDirectImage (C n) f).rightDerivedFunctor :=
  mateEquiv (SemilinearProperOpen.adj C τ f)
    (proEtaleRingModuleAdjunction f (StrictTower.coefficients (C n) Y)
      (StrictTower.coefficients (C n) X)
      (StrictTower.constantRingIso (C n) f)).mapDerivedCategoryRightDerivedAdjunction
    (pullEvaluation C τ f n).inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 64 in
set_option maxHeartbeats 800000 in
-- Transport the exact derived square, retaining its chosen adjoints and composition maps.
section Finite

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A]

/-- The prescribed etale comparison, with the identity coefficient realization.
Source: Stacks 099R (blueprint: lem-sp-varying-ring-graph-summand). -/
abbrev sitePull (X : Scheme.{u}) := StrictTower.H A X A (RingHom.id A)

/-- The inverse sum/site comparison is the mate of the inverse canonical pullback square.
This fixes the adjunction normalization; no unrelated isomorphism is selected.
Source: Stacks 04J0, 09AF (blueprint: lem-sp-varying-ring-graph-summand). -/
def siteSumInv {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    sitePull A U ⋙ levelSum A e ⟶
      Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙ sitePull A T :=
  (mateEquiv (Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance) (levelSumAdjunction A e)).symm
    (@inv _ _ _ _ (StrictTower.hPullbackInv A e A (RingHom.id A))
      (StrictTower.hPullbackInv_isIso A e A (RingHom.id A)))

/-- The localized right-adjoint identification makes this particular sum mate invertible.
Source: Stacks 04J0, 09AF (blueprint: lem-sp-varying-ring-graph-summand).
Proof: apply localize_ringed_site_morphism_general to the site comparison and U.
Its direct-image comparison is the identity on every etale test object. Thus both
sum/site composites are left adjoint to the same right adjoint. Their unit-preserving
comparison is invertible. Mate pasting identifies it with siteSumInv. On a summand
(t,m), its inverse retains t and applies the comparison unit to m. -/
theorem siteSumInv_isIso {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    IsIso (siteSumInv A e) := by
  sorry

/-- Exact derived descent of the adjunction-preserving sum/site comparison.
Source: Stacks 09AF (blueprint: lem-sp-varying-ring-graph-summand). -/
def siteSumComparison {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        (sitePull A T).mapDerivedCategory ≅
      (sitePull A U).mapDerivedCategory ⋙ (levelSum A e).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (siteSumInv A e) (siteSumInv_isIso A e)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified compact-support site comparison in intrinsic constant-ring coordinates.
The word uses exactly hR (the derived counit mate) followed by hJ (open extension),
including the canonical bounded-below inclusion comparisons. These are the proper
counit mate and open comparison specifying compactSupportSiteComparison.inv,
expressed after the identity-coefficient realization.
Source: Stacks 099R, 09AF; coefficient-compatibility compact-support comparison
(blueprint: lem-sp-varying-ring-graph-summand). -/
def finiteSupportComparison {U T : Scheme.{u}} {e : U ⟶ T} (c : Compactification e)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (sitePull A T).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          L.obj) ⟶
      ((StrictTower.moduleJ A c.i).mapDerivedCategory ⋙
        (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor).obj
          ((sitePull A U).mapDerivedCategory.obj L.obj) :=
  (sitePull A T).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).inv.app L) ≫
    (sitePull A T).mapDerivedCategoryPlusCompatibility.inv.app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L) ≫
    (StrictTower.hR A c.g A (RingHom.id A)).app
      (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus).obj
        L) ≫
    (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor.map
      ((StrictTower.hJ A c.i A (RingHom.id A)).hom.app L) ≫
    (StrictTower.moduleDirectImage A c.g).rightDerivedFunctor.map
      ((StrictTower.moduleJ A c.i).mapDerivedCategory.map
        ((sitePull A U).mapDerivedCategoryPlusCompatibility.hom.app L))

/-- Finite evaluation is the inverse of the specified etale sum normalization, transported
through the canonical compact-support comparison and the adjunction-preserving sum square.
Source: Stacks 0F4L, 0F4Y, 0GKM, 09AF; blueprint Local pairs and Levels
(blueprint: lem-sp-varying-ring-graph-summand).
Proof:
1. The localized site comparison fixes the sum square on generators: it sends (t,m)
to (t,eta(m)). Its right-adjoint comparison is the identity on etale test objects.
2. The ordinary pro-etale graph map after this square equals the etale graph map
followed by the underived proper counit mate and the open comparison. Transpose to
etale sheaves and test each summand. Both restrictions give eta(m) on the same graph
and zero on the complement. Sheafification extends that equality to all sheaves.
3. For a bounded-below complex P, the transpose of the direct-image comparison gamma
is the localized ordinary counit, by the canonical derived Hom formula. The mate
identity therefore gives b_p nu*(gamma_et) = gamma_pro Q(d_p), degree by degree.
This uses no preservation of injectives by site pullback and never inverts gamma.
4. Choose a bounded representative of the bounded constructible finite-Tor input L.
Apply step 2 termwise and then gamma_pro. Its naturality for the open comparison,
followed by step 3, identifies the result with finiteSupportComparison followed by
the etale inverse normalization. The latter is exactly the graph-normalized inverse
of lem-pur-etale-support-map-compatibility. Localization uniqueness descends the
identity. The finite-type schemes are Noetherian, and the proper factor is qcqs,
so lem-sp-et-proet-coefficient-compatibility uses these very comparisons. The field
need not be finite; arbitrary unbounded pro-etale inputs are not asserted invertible. -/
theorem finite_normalization (p ell : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hne : ell ≠ p)
    (_hA : ∃ q : ℕ, ∀ x : A, (ell ^ q) • x = 0)
    (k : Type u) [Field k] [CharP k p]
    {U T : Scheme.{u}} [U.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (e : U ⟶ T) [e.IsOver (Spec (.of k))] [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    [QuasiCompact c.i]
    [c.Z.Over (Spec (.of k))] [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (N : Etale.EtaleCompactSupportNormalization A)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hL : AdjunctionTransfer.etaleProperty A U L.obj) :
    (siteSumComparison A e).hom.app L.obj ≫
        (levelTheta A e c).app ((sitePull A U).mapDerivedCategory.obj L.obj) =
      (sitePull A T).mapDerivedCategory.map
        ((CoefficientCompatibility.normalizedSumComparison A k N e c).inv.app L.obj) ≫
      finiteSupportComparison A c L := by
  sorry

end Finite
end AlgebraicGeometry.ProEtale.VaryingRingGraph
