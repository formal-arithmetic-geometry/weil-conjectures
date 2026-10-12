/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

/-! # Changing the derived-to-ordinary comparison on a single module

Source: Stacks Project, Tags 06YJ and 08HY; the degree-zero truncation argument
in Step 4 of `lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem rightExact_homology_zero_isIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    {K L : CochainComplex A ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (s : K ⟶ L) [QuasiIso s] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) 0) := by
  have hK : (K.sc 0).g = 0 := by
    change K.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [CochainComplex.next]
    exact (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have hL : (L.sc 0).g = 0 := by
    change L.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [CochainComplex.next]
    exact (L.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  have : F.PreservesLeftHomologyOf (K.sc 0) := F.preservesLeftHomology_of_zero_g _ hK
  have : F.PreservesLeftHomologyOf (L.sc 0) := F.preservesLeftHomology_of_zero_g _ hL
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).map s) F
  have : IsIso (F.map (HomologicalComplex.homologyMap s 0)) := inferInstance
  have hcomp : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s) 0 ≫
        ((L.sc 0).mapHomologyIso F).hom) := by
    erw [hn]
    change IsIso (((K.sc 0).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap s 0))
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((L.sc 0).mapHomologyIso F).hom

/-- Every witnessing left-derived pullback comparison is invertible on zeroth homology.
Source: Stacks Project, Tag 06YJ, and the degree-zero tensor calculation in Step 1 of
lem-pc-module-pullback-comparison-target-automorphism.

Proof: Choose a flat resolution of G supported in degrees at most zero, augmented to
G[0]. Tensor pullback preserves its support. Its zeroth homology is the cokernel of
the pulled-back differential in degrees -1 and 0. Right exactness of tensor pullback
identifies this cokernel with a*G. The standard left-derived counit induces precisely
this identification. For any other witnessing counit, uniqueness of the right Kan
extension supplies an invertible natural transformation of the derived pullback whose
composition with the standard counit is the given counit. Evaluating at G[0] and
applying H0 expresses the given map as a composite of isomorphisms. The final
single-complex identification is also an isomorphism. No flatness of G is required;
for the zero module or empty scheme the same cokernel argument applies. -/
private theorem modulePullbackComparison_homology_zero_isIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules)
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc : IsDerivedModulePullbackComparison a G c) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map c) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  obtain ⟨ε, hε, rfl⟩ := hc
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let F : A ⥤ B := Scheme.Modules.tensorPullback a
  let H := DerivedCategory.homologyFunctor B 0
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let K := (CochainComplex.singleFunctor A 0).obj G
  let Pbound : ObjectProperty (CochainComplex A ℤ) :=
    fun P ↦ ∀ i : ℤ, 0 < i → IsZero (P.X i)
  let K' : Pbound.FullSubcategory := ⟨K, fun i hi ↦ K.isZero_of_isStrictlyLE 0 i hi⟩
  obtain ⟨R, π, hR⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology Y) Y.sheaf 0
  obtain ⟨hflat, hbound, _, hs⟩ := hR K'
  let P := R.obj K'
  let s : P ⟶ K := π.app K'
  have : QuasiIso s := hs
  have : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff P 0).2 hbound
  have hP := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    Y.toRingedSpace P ⟨0, hbound⟩ hflat
  obtain ⟨I, hI, hImap, _, _, _, _, E, hE, hEmap, hEadd, ε₀, hL, _, hKflat⟩ :=
    Classical.choose_spec (exists_derivedPullback a)
  have he : E = F := CategoryTheory.Functor.ext hE (fun M N f ↦ hEmap f)
  subst E
  have : (derivedPullback a).IsLeftDerivedFunctor ε₀
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hL
  have : (derivedPullback a).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := hε
  let e := Functor.leftDerivedUnique (derivedPullback a) (derivedPullback a) ε ε₀
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hfac : e.hom.app (DerivedCategory.Qh.obj (q.obj P)) ≫ ε₀.app (q.obj P) =
      ε.app (q.obj P) := by
    simp [e, Functor.leftDerivedUnique]
  have : IsIso (ε₀.app (q.obj P)) := hKflat P hP
  have : IsIso (ε.app (q.obj P)) := by rw [← hfac]; infer_instance
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  have : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesFiniteColimits F := inferInstance
  have : K.IsStrictlyLE 0 := by dsimp [K]; infer_instance
  have hm := rightExact_homology_zero_isIso F s
  let η := Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙ H) ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso B) H ≪≫
        DerivedCategory.homologyFunctorFactors B 0)
  have hmap : IsIso (H.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map s)))) :=
    (NatIso.isIso_map_iff η s).2 hm
  have : IsIso (DerivedCategory.Qh.map (q.map s)) := by
    apply Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  have hn := ε.naturality (q.map s)
  have hn' := H.congr_map hn
  simp only [Functor.map_comp, Functor.comp_map] at hn'
  have hcomp : IsIso (H.map ((derivedPullback a).map
      (DerivedCategory.Qh.map (q.map s))) ≫ H.map (ε.app (q.obj K))) := by
    rw [hn']
    infer_instance
  have : IsIso (H.map (ε.app (q.obj K))) :=
    IsIso.of_isIso_comp_left (H.map ((derivedPullback a).map
      (DerivedCategory.Qh.map (q.map s)))) (H.map (ε.app (q.obj K)))
  let j := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app G
  have hj : IsIso (H.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map j.hom))) :=
    inferInstanceAs (IsIso (H.mapIso (DerivedCategory.Qh.mapIso
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapIso j))).hom)
  change IsIso (H.map (ε.app (q.obj K) ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map j.hom)))
  rw [H.map_comp]
  infer_instance


private theorem modulePullback_single_isLE
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) (G : Y.Modules) :
    ((derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G)).IsLE 0 := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let K := (CochainComplex.singleFunctor A 0).obj G
  let B : ObjectProperty (CochainComplex A ℤ) :=
    fun F ↦ ∀ i : ℤ, 0 < i → IsZero (F.X i)
  let K' : B.FullSubcategory := ⟨K, fun i hi ↦ K.isZero_of_isStrictlyLE 0 i hi⟩
  obtain ⟨R, ε, hR⟩ := CochainComplex.exists_functorial_boundedAbove_flat_replacement
    (Opens.grothendieckTopology Y) Y.sheaf 0
  obtain ⟨hflat, hbound, _, hq⟩ := hR K'
  let P := R.obj K'
  let s : P ⟶ K := ε.app K'
  have : QuasiIso s := hq
  have : IsIso (DerivedCategory.Q.map s) :=
    by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  obtain ⟨F, _, _, hAdd, _, _, e, _⟩ :=
    flatComplexDerivedPullback a P ⟨0, hbound⟩ hflat
  have : F.Additive := hAdd
  have : P.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff P 0).2 hbound
  let e' := e ≪≫ (derivedPullback a).mapIso (asIso (DerivedCategory.Q.map s))
  have : CochainComplex.IsStrictlyLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) 0 :=
    inferInstance
  have hLE : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).IsLE 0 := inferInstance
  let eF := (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).symm.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).symm.app P)
  exact DerivedCategory.TStructure.t.isLE_of_iso (eF ≪≫ e') 0

/-- Two left-derived counits on a single module differ by an automorphism of its
ordinary pullback. There is no cover, direct image or base-change square in this lemma.
Source: Stacks Project, Tags 06YJ and 08HY; Step 4 of the affine alternating model
factorization proof (the truncation argument is written out here).
(blueprint: lem-pc-module-pullback-comparison-target-automorphism).

Proof: Right Kan extension uniqueness gives an automorphism of the derived pullback
functor relating the two witnessing counits. Derived tensor of a degree-zero module
is nonpositive: resolve it by a bounded-above complex of flat modules in degrees at
most zero. Right exactness identifies degree-zero homology of that tensor complex
with ordinary tensor pullback, and the counit induces this identification. Thus both
counits induce isomorphisms on H0. A map from this nonpositive object to a module in
degree zero factors uniquely through its H0 truncation: in the truncation triangle,
both Hom from the negative truncation and Hom from its shift by one vanish by the
standard t-structure orthogonality. Apply this to both comparisons. Compose the
inverse of H0(c0) with H0(c), and transport through the single-module H0 isomorphism,
to obtain a module automorphism alpha. Full faithfulness of the single functor and
uniqueness of the truncation factorization give c = c0 followed by alpha[0].
This includes the zero module and the empty scheme; no flatness of G is used. -/
theorem modulePullbackComparison_target_automorphism
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules)
    (c₀ c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc₀ : IsDerivedModulePullbackComparison a G c₀)
    (hc : IsDerivedModulePullbackComparison a G c) :
    ∃ α : (Scheme.Modules.tensorPullback a).obj G ≅
        (Scheme.Modules.tensorPullback a).obj G,
      c = c₀ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map α.hom := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := DerivedCategory.singleFunctor C 0
  let H := DerivedCategory.homologyFunctor C 0
  let M := (Scheme.Modules.tensorPullback a).obj G
  have : IsIso (H.map c₀) := modulePullbackComparison_homology_zero_isIso a G c₀ hc₀
  have : IsIso (H.map c) := modulePullbackComparison_homology_zero_isIso a G c hc
  let e : H.obj (S.obj M) ≅ M :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app M
  let α : M ≅ M := e.symm ≪≫ (asIso (H.map c₀)).symm ≪≫ asIso (H.map c) ≪≫ e
  refine ⟨α, ?_⟩
  have : ((derivedPullback a).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G)).IsLE 0 :=
    modulePullback_single_isLE a G
  apply (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0).1
  change H.map c = H.map (c₀ ≫ S.map α.hom)
  rw [H.map_comp]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality
    α.hom
  change H.map (S.map α.hom) ≫ e.hom = e.hom ≫ α.hom at hn
  apply (cancel_mono e.hom).1
  rw [Category.assoc, hn]
  simp [α, e]


end AlgebraicGeometry
