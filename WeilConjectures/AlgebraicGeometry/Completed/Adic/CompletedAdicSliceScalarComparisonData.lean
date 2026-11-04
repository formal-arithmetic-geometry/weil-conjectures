/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-! # Universal data for the completed adic slice comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{t}) Ab.{t + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

set_option linter.defProp false in
/-- The canonical scalar adjunction on the slice for the pulled-back condensed map.
Source: det-def-sfb-coefficient-change, det-def-sfb-change-of-scalars.
(blueprint: def-weil-pbc-completed-adic-slice-scalar-extension). -/
def completedAdicSliceChangeData (X : Scheme.{t}) (U : X.ProEt)
    (a : Λ ⟶ Λ') [IsMonHom a] :=
  Mod.extendRestrictAdjunction (coefficientMap a U.left)

/-- Ordinary extension of scalars along `a_U : Λ_U ⟶ Λ'_U`.
Source: det-def-sfb-coefficient-change, det-def-sfb-change-of-scalars.
(blueprint: def-weil-pbc-completed-adic-slice-scalar-extension). -/
abbrev completedAdicSliceChange (X : Scheme.{t}) (U : X.ProEt)
    (a : Λ ⟶ Λ') [IsMonHom a] :=
  Mod.extendScalars (coefficientMap a U.left)

/-- The ordinary slice scalar extension is additive, as a left adjoint between
preadditive module categories. Source: det-def-sfb-change-of-scalars.
(blueprint: def-weil-pbc-completed-adic-slice-scalar-extension-additive). -/
instance completedAdicSliceChange_additive (X : Scheme.{t}) (U : X.ProEt)
    (a : Λ ⟶ Λ') [IsMonHom a] : (completedAdicSliceChange X U a).Additive :=
  inferInstanceAs (Mod.extendScalars (coefficientMap a U.left)).Additive

/-- Total left derived extension along the actual condensed coefficient map on `U`.
Source: det-def-sfb-derived-extension-of-scalars.
(blueprint: def-weil-pbc-completed-adic-slice-scalar-extension). -/
abbrev completedAdicSliceDerivedChange (X : Scheme.{t}) (U : X.ProEt)
    (a : Λ ⟶ Λ') [IsMonHom a] :=
  (completedAdicSliceChange X U a).leftDerivedFunctor

attribute [local irreducible] completedAdicChangeData completedAdicSliceChangeData

universe u₀ v₀ r₀ m₀

-- The module-sheafification comparison of LocalizedSiteTensorRestriction,
-- used here before introducing any monoidal structure.
section SheafificationComparison

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m₀}]
  [HasWeakSheafify J AddCommGrpCat.{m₀}]
  (R : Sheaf J RingCat.{r₀}) (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m₀}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m₀}]

private noncomputable def overSheafificationMap (P : PresheafOfModules.{m₀} R.obj) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).obj
      ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P) ⟶
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))

private lemma overSheafificationMap_unit (P : PresheafOfModules.{m₀} R.obj) :
    toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val =
      whiskerLeft (Over.forget U).op (toSheafify J P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv (R := R.over U) (𝟙 _)
    (P := (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P)
    (F := ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U)).apply_symm_apply
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (R.over U).obj).map) h

private lemma overSheafificationMap_isIso (P : PresheafOfModules.{m₀} R.obj) :
    IsIso (overSheafificationMap R U P) := by
  let a := toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val
  have hi : Presheaf.IsLocallyInjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have hs : Presheaf.IsLocallySurjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  have hi' : Presheaf.IsLocallyInjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

private lemma overSheafificationMap_naturality {P Q : PresheafOfModules.{m₀} R.obj}
    (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).map
        ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map f) ≫
        overSheafificationMap R U Q =
      overSheafificationMap R U P ≫
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).map f).over U := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := R.over U) (𝟙 _)
  let push := PresheafOfModules.pushforward (F := Over.forget U) (𝟙 (R.over U).obj)
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [adj, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    overSheafificationMap, Equiv.apply_symm_apply]
  change push.map f ≫ push.map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app Q) =
    push.map ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P) ≫
      push.map (((SheafOfModules.forget R) ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)).map
          ((PresheafOfModules.sheafification (R := R) (𝟙 _)).map f))
  rw [← push.map_comp, ← push.map_comp]
  exact congrArg push.map
    ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.naturality f)

end SheafificationComparison

private abbrev sliceCoefficientMap (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)

private def scalarPresheafMap
    {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
    [HasWeakSheafify J AddCommGrpCat.{r₀}]
    {R S : Sheaf J CommRingCat.{r₀}} (f : R ⟶ S)
    {M N : SheafOfModules.{r₀}
      ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj R)}
    (a : M ⟶ N) :
    SheafOfModules.changeOfRingsPresheaf.{v₀, u₀, r₀} f M ⟶
      SheafOfModules.changeOfRingsPresheaf.{v₀, u₀, r₀} f N :=
  { app := fun V ↦ (ModuleCat.extendScalars (f.hom.app V).hom).map (a.val.app V)
    naturality := SheafOfModules.changeOfRingsHom_naturality f M a }

section ScalarNormalization

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [HasWeakSheafify J AddCommGrpCat.{r₀}]
  {R S : Sheaf J CommRingCat.{r₀}} (f : R ⟶ S)

private def scalarPresheafFunctor :
    SheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj R) ⥤
      PresheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj S).obj where
  obj := SheafOfModules.changeOfRingsPresheaf f
  map := scalarPresheafMap f
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro V
    simp [scalarPresheafMap]
    rfl
  map_comp a b := by
    apply PresheafOfModules.hom_ext
    intro V
    simp [scalarPresheafMap]

private def scalarNormalizationIso
    (E : SheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj R) ⥤
      SheafOfModules.{r₀}
        ((sheafCompose J (forget₂ CommRingCat.{r₀} RingCat.{r₀})).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings f M)
    (hm : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom f M a ≫ eqToHom (h N).symm) :
    E ≅ scalarPresheafFunctor f ⋙ PresheafOfModules.sheafification (𝟙 _) :=
  NatIso.ofComponents (fun M ↦ eqToIso (h M)) (by
    intro M N a
    change E.map a ≫ eqToHom (h N) =
      eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom f M a
    rw [hm]
    simp)

end ScalarNormalization

private def scalarOverPresheafIso (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (M : SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} (sliceCoefficientMap X U f) (M.over U) ≅
      (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} f M) := by
  refine PresheafOfModules.isoMk (fun V ↦ Iso.refl _) ?_
  intro V W g
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    change SheafOfModules.changeOfRingsMap.{t, t + 1, t + 1}
        (sliceCoefficientMap X U f) (M.over U) g (s ⊗ₜ m) =
      SheafOfModules.changeOfRingsMap.{t, t + 1, t + 1}
        f M ((Over.forget U).op.map g) (s ⊗ₜ m)
    exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1}
      (sliceCoefficientMap X U f) (M.over U) g) s m).trans
      (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{t, t + 1, t + 1}
        f M ((Over.forget U).op.map g)) s m).symm
  | add x y hx hy => simpa only [_root_.map_add] using congrArg₂ (· + ·) hx hy

private theorem globalCounit_isIso (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S)
    (P : CochainComplex (reductionModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsIso ((reductionDerivedCounit X f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (reductionDerivedExistence X f).choose_spec.choose_spec.2.2 P hP

/-- Ordinary scalar extension commutes with inverse image to the pro-etale slice.
Source: sk-prop-sfb-cartesian-coefficients, det-def-sfb-coefficient-change.
Proof: the coefficient square commutes by naturality of inverse image from the point.
Restriction of scalars therefore commutes with direct image. Conjugating this
isomorphism under the two scalar adjunctions and the two geometric adjunctions
produces the displayed isomorphism; this is the published ordinary `pullIso`.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-underived). -/
theorem completedAdic_slice_scalarComparison_underived (X : Scheme.{t}) (U : X.ProEt)
    (a : Λ ⟶ Λ') [IsMonHom a] :
    Nonempty
      ((CondensedRing.upperStar Λ U.hom ⋙ completedAdicSliceChange X U a) ≅
        (Mod.extendScalars (coefficientMap a X) ⋙ CondensedRing.upperStar Λ' U.hom)) :=
  ⟨CondensedRing.pullIso a U.hom⟩

private theorem leftDerived_of_resolving
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory B)
    [G.CommShift ℤ] [G.IsTriangulated]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ L ⟶ G)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hα : ∀ X : HomotopyCategory A (.up ℤ), X ∈ P → IsIso (α.app X)) :
    L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let Q := DerivedCategory.Qh (C := A)
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have hinv (X Y : HomotopyCategory A (.up ℤ)) (s : X ⟶ Y)
      (hX : X ∈ P) (hY : Y ∈ P) (hs : W s) : IsIso (G.map s) := by
    have := hα X hX
    have := hα Y hY
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have he := α.naturality s
    have : IsIso (α.app X ≫ G.map s) := by
      rw [← he]
      change IsIso (L.map (Q.map s) ≫ α.app Y)
      infer_instance
    exact IsIso.of_isIso_comp_left (α.app X) (G.map s)
  obtain ⟨_, L₀, α₀, hL₀, _, h₀⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) G P hres hinv
  have := hL₀
  let τ := L₀.leftDerivedLift α₀ W L α
  have ht (X : HomotopyCategory A (.up ℤ)) (hX : X ∈ P) :
      IsIso (τ.app (Q.obj X)) := by
    have := h₀ X hX
    have := hα X hX
    have : IsIso (τ.app (Q.obj X) ≫ α₀.app X) := by
      rw [Functor.leftDerived_fac_app]
      exact hα X hX
    exact IsIso.of_isIso_comp_right (τ.app (Q.obj X)) (α₀.app X)
  have (X : HomotopyCategory A (.up ℤ)) : IsIso ((whiskerLeft Q τ).app X) := by
    obtain ⟨Y, s, hY, hs⟩ := hres X
    have := ht Y hY
    have : IsIso (Q.map s) := Localization.inverts Q W s hs
    have : IsIso (L.map (Q.map s) ≫ τ.app (Q.obj X)) := by
      rw [τ.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.map (Q.map s)) (τ.app (Q.obj X))
  have : IsIso (whiskerLeft Q τ) := NatIso.isIso_of_isIso_app _
  have := Localization.full_whiskeringLeft Q W (DerivedCategory B)
  have := Localization.faithful_whiskeringLeft Q W (DerivedCategory B)
  have : IsIso (((whiskeringLeft _ _ (DerivedCategory B)).obj Q).map τ) :=
    inferInstanceAs (IsIso (whiskerLeft Q τ))
  have : IsIso τ := isIso_of_reflects_iso τ
    ((whiskeringLeft _ _ (DerivedCategory B)).obj Q)
  exact (L₀.isLeftDerivedFunctor_iff_isIso_leftDerivedLift α₀ W L α).2 this

private theorem scalarDerived_composites
    {A B AU BU : Type*} [Category A] [Category B] [Category AU] [Category BU]
    [Abelian A] [Abelian B] [Abelian AU] [Abelian BU]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory AU] [HasDerivedCategory BU]
    (E : A ⥤ B) (EU : AU ⥤ BU) (ER : A ⥤ AU) (ES : B ⥤ BU)
    [E.Additive] [EU.Additive] [ER.Additive] [ES.Additive]
    [PreservesFiniteLimits ER] [PreservesFiniteColimits ER]
    [PreservesFiniteLimits ES] [PreservesFiniteColimits ES]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    (FU : DerivedCategory AU ⥤ DerivedCategory BU)
    (ε : DerivedCategory.Qh ⋙ F ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εU : DerivedCategory.Qh ⋙ FU ⟶ EU.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : Set (HomotopyCategory A (.up ℤ)))
    (hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K),
        K' ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s)
    (hε : ∀ K ∈ P, IsIso (ε.app K))
    (hεU : ∀ K ∈ P, IsIso (εU.app ((ER.mapHomotopyCategory (.up ℤ)).obj K))) :
    ∃ (αU : DerivedCategory.Qh ⋙ (ER.mapDerivedCategory ⋙ FU) ⟶
        (ER ⋙ EU).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (α : DerivedCategory.Qh ⋙ (F ⋙ ES.mapDerivedCategory) ⟶
        (E ⋙ ES).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      (ER.mapDerivedCategory ⋙ FU).IsLeftDerivedFunctor αU
          (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        (F ⋙ ES.mapDerivedCategory).IsLeftDerivedFunctor α
          (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let αU : DerivedCategory.Qh ⋙ (ER.mapDerivedCategory ⋙ FU) ⟶
      (ER ⋙ EU).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight ER.mapDerivedCategoryFactorsh.hom FU ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (ER.mapHomotopyCategory (.up ℤ)) εU ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (ER ⋙ EU)) (.up ℤ)).hom
        DerivedCategory.Qh
  let α : DerivedCategory.Qh ⋙ (F ⋙ ES.mapDerivedCategory) ⟶
      (E ⋙ ES).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight ε ES.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft (E.mapHomotopyCategory (.up ℤ)) ES.mapDerivedCategoryFactorsh.hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ ES)) (.up ℤ)).hom
        DerivedCategory.Qh
  refine ⟨αU, α, ?_, ?_⟩
  · apply leftDerived_of_resolving _ _ _ P hres
    intro K hK
    have := hεU K hK
    dsimp only [αU, NatTrans.comp_app, associator_inv_app, associator_hom_app,
      whiskerLeft_app, whiskerRight_app]
    infer_instance
  · apply leftDerived_of_resolving _ _ _ P hres
    intro K hK
    have := hε K hK
    dsimp only [α, NatTrans.comp_app, associator_inv_app, associator_hom_app,
      whiskerLeft_app, whiskerRight_app]
    infer_instance

set_option maxHeartbeats 400000 in
-- reason: derived category instance unification on module objects
/-- Both composites on condensed module objects derive the corresponding ordinary
composites. No flatness of the coefficient change is required.
Source: sk-prop-sfb-cartesian-coefficients; Stacks Tags 06YY and 0D6D.
Proof: scalar extension followed by the exact inverse image carries the usual
composite counit and is universal by exact postcomposition. The published arbitrary
coefficient-change theorem identifies it with inverse image followed by derived
scalar extension. Transport the first counit's universal property along that
isomorphism and the ordinary scalar comparison to obtain the second counit.
Transport of the universal property is precisely invariance of right Kan extensions
under isomorphisms, so both counits are universal on the entire unbounded category.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison-derived-data). -/
theorem completedAdic_slice_scalarComparison_derived_data (X : Scheme.{t}) (U : X.ProEt)
    (a : Λ ⟶ Λ') [IsMonHom a] :
    let A := Mod (Sheaf (ProEt.topology X) Ab.{t + 1}) (condensedRingObj Λ X)
    let ER := CondensedRing.upperStar Λ U.hom
    let ES := CondensedRing.upperStar Λ' U.hom
    let E := Mod.extendScalars (coefficientMap a X)
    let EU := completedAdicSliceChange X U a
    let LU := ER.mapDerivedCategory ⋙ completedAdicSliceDerivedChange X U a
    let L := E.leftDerivedFunctor ⋙ ES.mapDerivedCategory
    let GU := (ER ⋙ EU).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
    let G := (E ⋙ ES).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
    ∃ (αU : DerivedCategory.Qh (C := A) ⋙ LU ⟶ GU)
      (α : DerivedCategory.Qh (C := A) ⋙ L ⟶ G),
      LU.IsLeftDerivedFunctor αU (HomotopyCategory.quasiIso A (.up ℤ)) ∧
        L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let ER := CondensedRing.upperStar Λ U.hom
  let ES := CondensedRing.upperStar Λ' U.hom
  let E := Mod.extendScalars (coefficientMap a X)
  let EU := completedAdicSliceChange X U a
  let α := Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit E ES
  let d : ER.mapDerivedCategory ⋙ EU.leftDerivedFunctor ≅
      E.leftDerivedFunctor ⋙ ES.mapDerivedCategory :=
    Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ U.hom).symm _ ≪≫
    CondensedRing.derivedUpperStarExtendScalarsIso a U.hom ≪≫
    Functor.isoWhiskerLeft _
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' U.hom)
  obtain ⟨e₀⟩ := completedAdic_slice_scalarComparison_underived X U a
  let e := Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory e₀.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e₀.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, e₀.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] } DerivedCategory.Qh
  let αU := Functor.whiskerLeft DerivedCategory.Qh d.hom ≫ α ≫ e.inv
  refine ⟨αU, α, ?_, inferInstance⟩
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  apply (Functor.isRightKanExtension_iff_of_iso₂ αU α e d ?_).2
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ α
      (HomotopyCategory.quasiIso _ (.up ℤ)))
  simp [αU]

end AlgebraicGeometry.Scheme
