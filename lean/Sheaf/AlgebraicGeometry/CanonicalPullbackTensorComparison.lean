/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Mathlib.Algebra.Homology.Monoidal
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatResolution

/-! # Canonical tensor comparison for derived pullback

Source: Stacks Project, Cohomology, Tag 079U; perfect.tex, Tag 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison).
The comparison is the unique family satisfying `IsCanonicalPullbackTensorComparison`:
it is pinned by the actual module pullback tensor map and the shared left-derived
counit on K-flat representatives. Statements bind the comparison together with this
uniquely characterising predicate; no monoidal structure on pullback is chosen
arbitrarily and no data is chosen from a theorem.
-/

@[expose] public section

universe uTC wTC
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry

/-- The total tensor complex used in the coordinate equation below.
Source: Stacks, 079U (blueprint: def-pc-derived-pullback-tensor-comparison). -/
def pullbackTensorTotal (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  CochainComplex.mapBifunctor P N (curriedTensor _)

/-- The canonical localization tensor map, invertible on K-flat coordinates.
It is the upstream lax monoidal map of Q for the recorded derived tensor.
Source: Stacks, 06YH and 079U
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
def pullbackTensorModelMap (X : Scheme.{uTC})
    [HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj N ⟶
      DerivedCategory.Q.obj (pullbackTensorTotal X P N) := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  haveI : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  haveI : IsGrothendieckAbelian.{uTC} (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI : CategoryTheory.Limits.HasColimitsOfSize.{0,0}
      (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0,0,uTC,uTC} _
  haveI := schemeModule_hasFunctorialFlatResolution X
  haveI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))
  haveI (A B : GradedObject ℤ (SheafOfModules.{uTC} (moduleRings X.toRingedSpace))) :
      GradedObject.HasTensor A B := inferInstance
  letI := HomologicalComplex.monoidalCategory
    (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) (.up ℤ)
  haveI : (DerivedCategory.Q
      (C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace))).LaxMonoidal := inferInstance
  exact Functor.LaxMonoidal.μ (DerivedCategory.Q
    (C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace))) P N

variable [∀ Y : Scheme.{uTC},
  HasDerivedCategory.{wTC} (SheafOfModules.{uTC} (moduleRings Y.toRingedSpace))]

/-- The canonical tensor comparison is characterized on every pair of K-flat
representatives by the left-derived counits, the localization tensor maps and
termwise module pullback. The degreewise equation pins the chain isomorphism to
the canonical module tensor map on each summand, including its signs.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
def IsCanonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X)
    (τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.monoidalCategory T.sheaf
  letI := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI := Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf
  (∀ P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ,
    P.IsKFlat → N.IsKFlat →
    ∃ φ : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P N) ≅
      pullbackTensorTotal T
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N),
      (∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback g).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor
              (SheafOfModules.{uTC} (moduleRings T.toRingedSpace))) (.up ℤ) p q n h) ∧
      (derivedPullback g).map (pullbackTensorModelMap X P N) ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P N)) ≫
          DerivedCategory.Q.map φ.hom =
        τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) ≫
          ((SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
            (SingleComplexBaseChange.counit g).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
          pullbackTensorModelMap T
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ∧
    ∀ (E E' K K' : schemeDerivedCategory X) (a : E ⟶ E') (b : K ⟶ K'),
      (derivedPullback g).map (a ⊗ₘ b) ≫ τ E' K' =
        τ E K ≫ ((derivedPullback g).map a ⊗ₘ (derivedPullback g).map b)

private theorem counit_isIso {T X : Scheme.{uTC}} (g : T ⟶ X)
    (P : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) :
    IsIso ((SingleComplexBaseChange.counit g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, hε, _, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback.{uTC, wTC} g)
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  change (derivedPullback g).IsLeftDerivedFunctor ε
    (HomotopyCategory.quasiIso _ (.up ℤ)) at hε
  have hshared :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{uTC, wTC})) g
  change (derivedPullback g).IsLeftDerivedFunctor (SingleComplexBaseChange.counit g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) at hshared
  have := hshared
  have hfac := Functor.leftDerivedNatTrans_app
    (derivedPullback g) (derivedPullback g) ε (SingleComplexBaseChange.counit g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have hεP := hK P hP
  have hiso : IsIso (Functor.leftDerivedNatTrans
      (derivedPullback g) (derivedPullback g) ε (SingleComplexBaseChange.counit g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)) :=
    (Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε
      (SingleComplexBaseChange.counit g) (HomotopyCategory.quasiIso _ (.up ℤ))).isIso_hom
  have hcomp : IsIso ((Functor.leftDerivedNatTrans
      (derivedPullback g) (derivedPullback g) ε (SingleComplexBaseChange.counit g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
    rw [hfac]
    simpa using hεP
  exact IsIso.of_isIso_comp_left
    ((Functor.leftDerivedNatTrans
      (derivedPullback g) (derivedPullback g) ε (SingleComplexBaseChange.counit g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) _

private theorem modelMap_isIso (X : Scheme.{uTC})
    (P N : CochainComplex (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) : IsIso (pullbackTensorModelMap X P N) := by
  let C := SheafOfModules.{uTC} (moduleRings X.toRingedSpace)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{uTC} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, uTC, uTC} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C := inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
    inferInstance
  have hk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro M hM
    obtain ⟨M, rfl⟩ := M.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hM
    have hr : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj M ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj P) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP M hM)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj N)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ)) _ _ hk
  change IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) P N)
  change IsIso (_ ≫ _ ≫ _)
  change IsIso (_ ≫ (_ ≫ _) ≫ _)
  infer_instance

/-- Transport a verified core-monoidal model to the canonical comparison predicate.
The model supplies the counit and K-flat coordinate equations; the transport is the
standard descent argument through K-flat resolutions.
Proof: identify the model's module functor with the actual tensor pullback by
functor extensionality. The left-derived universal property gives a natural
isomorphism delta from the model counit to the shared counit, satisfying
`delta ≫ shared counit = model counit`. Conjugate the inverse model tensorator
by delta inverse on the tensor input and by the tensor of delta on the outputs.
Naturality follows from naturality of delta and the tensorator. Substituting
the counit comparison into the model coordinate equation gives the required
canonical equation; the model's degreewise equation pins the same chain map.
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison-model-transport). -/
theorem exists_canonical_from_model {T X : Scheme.{uTC}} (g : T ⟶ X)
    (m : (derivedPullback g).CoreMonoidal)
    (hm : IsDerivedPullbackMonoidalModel g m) :
    ∃ τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K,
      IsCanonicalPullbackTensorComparison g τ := by
  sorry

/-- Existence of the canonical derived tensor comparison.
Proof: choose K-flat representatives of both inputs (lem-pc-kflat-resolution).
Their tensor and pullbacks are K-flat (lem-pc-kflat-tensor-product and
lem-pc-kflat-pullback-preservation), so the localization tensor maps and the
left-derived counits are invertible. Form the chain tensor isomorphism from
lem-weil-pbc-module-pullback-tensor on every summand; naturality makes it commute
with differentials. Transport it through the counits and localization tensor
maps to obtain τ. Comparisons between K-flat resolutions and the universal
left-derived property show independence of representatives, giving the displayed
equation for every P,N (lem-pc-derived-pullback-tensor-product).
Source: Stacks, 079U; perfect.tex, 0DJA(1)
(blueprint: def-pc-derived-pullback-tensor-comparison). -/
theorem exists_canonicalPullbackTensorComparison {T X : Scheme.{uTC}} (g : T ⟶ X) :
    ∃ τ : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K,
      IsCanonicalPullbackTensorComparison g τ := by
  obtain ⟨m, hm⟩ := exists_derivedPullbackMonoidalModel g
  exact exists_canonical_from_model g m hm

/-- The canonical derived tensor comparison is unique: two families satisfying the
characterising predicate agree.
Proof: on K-flat representatives P, N the counits at P and N and the localization
tensor map at the K-flat pullbacks are invertible, and the chain isomorphism is pinned
on every summand, so the coordinate equation determines the value at (Q P, Q N).
Every derived object is isomorphic to Q of a K-flat complex (lem-pc-kflat-resolution),
and naturality in both inputs transports the value along these isomorphisms.
Source: Stacks, 079U (blueprint: def-pc-derived-pullback-tensor-comparison). -/
theorem IsCanonicalPullbackTensorComparison.unique {T X : Scheme.{uTC}} {g : T ⟶ X}
    {τ τ' : ∀ E K : schemeDerivedCategory X,
      (derivedPullback g).obj (E ⊗ K) ⟶
        (derivedPullback g).obj E ⊗ (derivedPullback g).obj K}
    (h : IsCanonicalPullbackTensorComparison g τ)
    (h' : IsCanonicalPullbackTensorComparison g τ') : τ = τ' := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.monoidalCategory T.sheaf
  have : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  have : MonoidalPreadditive (SheafOfModules.{uTC} (moduleRings T.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
  dsimp only [IsCanonicalPullbackTensorComparison] at h h'
  have hflat (P N : CochainComplex
      (SheafOfModules.{uTC} (moduleRings X.toRingedSpace)) ℤ)
      (hP : P.IsKFlat) (hN : N.IsKFlat) :
      τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) =
        τ' (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) := by
    obtain ⟨φ, hφ, heq⟩ := h.1 P N hP hN
    obtain ⟨ψ, hψ, heq'⟩ := h'.1 P N hP hN
    have hφψ : φ.inv ≫ ψ.hom = 𝟙 _ := by
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      apply (cancel_epi
        (((Classical.choose (Scheme.Modules.module_pullback_tensor g))
          (P.X p) (N.X q)).hom)).1
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ← Category.assoc]
      rw [← hφ p q n hpq]
      have hid : φ.hom.f n ≫ φ.inv.f n = 𝟙 _ :=
        congrArg (fun a ↦ a.f n) φ.hom_inv_id
      simp only [Category.assoc, hid]
      exact (hψ p q n hpq).trans (hφ p q n hpq).symm
    have hhom : φ.hom = ψ.hom := by
      calc
        φ.hom = φ.hom ≫ (φ.inv ≫ ψ.hom) := by rw [hφψ, Category.comp_id]
        _ = ψ.hom := by simp only [← Category.assoc, φ.hom_inv_id, Category.id_comp]
    have hPull : CochainComplex.IsKFlat (R := T.sheaf)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) := by
      convert CochainComplex.isKFlat_pullback g.base T.sheaf X.sheaf ⟨g.c⟩ P hP using 1
      rfl
    have := counit_isIso g P hP
    have := counit_isIso g N hN
    have := modelMap_isIso T
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N) hPull
    apply (cancel_mono
      (((SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit g).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap T
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N))).1
    rw [← heq, ← heq', hhom]
  funext E K
  obtain ⟨c⟩ := SingleComplexBaseChange.nonempty_coordinates g E
    ((derivedPullback g).obj E) (𝟙 _)
  obtain ⟨d⟩ := SingleComplexBaseChange.nonempty_coordinates g K
    ((derivedPullback g).obj K) (𝟙 _)
  have hnat := h.2 _ _ _ _ c.e.hom d.e.hom
  have hnat' := h'.2 _ _ _ _ c.e.hom d.e.hom
  apply (cancel_epi ((derivedPullback g).map (c.e.hom ⊗ₘ d.e.hom))).1
  rw [hnat, hnat', hflat c.P d.P c.isKFlat d.isKFlat]


end AlgebraicGeometry
end
