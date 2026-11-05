/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # The single-complex stalkwise base-change condition

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8, and Tag 0DJ9
(blueprint: def-pc-single-complex-base-change-stalk-condition).

K-flat coordinates express the canonical tensor-cohomology comparison, followed by
the given derived map. Every choice is tied to the actual stalk maps or to a
localization equation. Invertibility is independent of representative coordinates.
-/

@[expose] public section

universe uSC wSC
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{uSC},
  HasDerivedCategory.{wSC} (SheafOfModules.{uSC} (moduleRings Y.toRingedSpace))]

/-- Additivity of termwise tensor pullback, from the existing composition construction.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
instance tensorPullbackAdditive {Y Z : Scheme.{uSC}} (k : Y ⟶ Z) :
    (Scheme.Modules.tensorPullback k).Additive :=
  (Classical.choose exists_derivedPullbackComposition) k

/-- The universal counit of the recorded derived tensor pullback, on homotopy categories.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def counit {Y Z : Scheme.{uSC}} (k : Y ⟶ Z) :
    DerivedCategory.Qh (C := SheafOfModules.{uSC} (moduleRings Z.toRingedSpace)) ⋙
      derivedPullback k ⟶
      (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{uSC} (moduleRings Y.toRingedSpace)) :=
  (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k

variable {X X' S S' : Scheme.{uSC}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- K-flat coordinates for the given derived morphism. P represents K, N represents
K', and t represents phi through the specified left-derived counit and the two
representative isomorphisms. No arbitrary stalk comparison is included.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
structure Coordinates (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') where
  P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ
  N : CochainComplex (SheafOfModules.{uSC} (moduleRings X'.toRingedSpace)) ℤ
  e : DerivedCategory.Q.obj P ≅ K
  e' : DerivedCategory.Q.obj N ≅ K'
  isKFlat : P.IsKFlatTensor
  counit_isIso : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  t : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P ⟶ N
  represents : (counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    (DerivedCategory.Q (C := SheafOfModules.{uSC} (moduleRings X'.toRingedSpace))).map t ≫
      e'.hom = (derivedPullback g').map e.hom ≫ φ

private theorem counit_isIso_of_isKFlat
    (P : CochainComplex (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) :
    IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      (derivedPullback_spec g')
  have h : E = Scheme.Modules.tensorPullback g' :=
    CategoryTheory.Functor.ext hE (fun M N a => hEmap a)
  subst E
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : (derivedPullback g').IsLeftDerivedFunctor ε W := hL
  have hc : (derivedPullback g').IsLeftDerivedFunctor (counit g') W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g'
  have : IsIso ((derivedPullback g').leftDerivedLift ε W
      (derivedPullback g') (counit g')) :=
    ((derivedPullback g').isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      ε W (derivedPullback g') (counit g')).mp hc
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hK P hP
  rw [← Functor.leftDerived_fac_app (derivedPullback g') ε W
    (derivedPullback g') (counit g')]
  infer_instance

private theorem derived_map_surjective
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (M N : CochainComplex D ℤ) [N.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (M ⟶ N) → _) := by
  have _derived : ∀ Y : Scheme.{uSC},
      HasDerivedCategory.{wSC} (SheafOfModules.{uSC} (moduleRings Y.toRingedSpace)) :=
    inferInstance
  intro φ
  let e := DerivedCategory.quotientCompQhIso D
  obtain ⟨t, ht⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj M) N).surjective
      (e.hom.app M ≫ φ ≫ e.inv.app N)
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective t
  refine ⟨t, ?_⟩
  apply (cancel_mono (e.inv.app N)).1
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, ht]
  simp [e]

set_option maxHeartbeats 800000 in
-- Elaborating the two sheaf resolutions and their localization maps needs this budget.
/-- Every derived morphism has these K-flat coordinates.
Proof: choose a complex representing K and a K-flat resolution P (lem-pc-kflat-resolution).
Choose a K-injective representative N of K' (prop-pur-kinjective-resolutions-exist).
The universal left-derived counit computes pullback on P, so is invertible there.
Compose its inverse with the pullback of e and phi, and then e' inverse. Since N
is K-injective, the localization Hom bijection lifts this derived morphism to a
homotopy class of chain maps from termwise pullback of P to N. Choose a chain-map
representative t. The localization equation is exactly the represents field.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
theorem nonempty_coordinates (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') : Nonempty (Coordinates g' K K' φ) := by
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology X') X'.sheaf
  let M := DerivedCategory.Q.objPreimage K'
  let N := I.obj M
  have : QuasiIso (η.app M) := (hI M).1
  have : N.IsKInjective := (hI M).2.1
  let e' : DerivedCategory.Q.obj N ≅ K' :=
    (asIso (DerivedCategory.Q.map (η.app M))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K'
  have hc := counit_isIso_of_isKFlat g' P hP
  let q := (HomotopyCategory.quotient _ (.up ℤ)).obj P
  obtain ⟨t, ht⟩ := derived_map_surjective
    (D := SheafOfModules.{uSC} (moduleRings X'.toRingedSpace))
    (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) N
    (inv ((counit g').app q) ≫ (derivedPullback g').map e.hom ≫ φ ≫ e'.inv)
  refine ⟨⟨P, N, e, e', hP, hc, t, ?_⟩⟩
  rw [ht]
  simp only [q, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    IsIso.hom_inv_id_assoc]

end AlgebraicGeometry.SingleComplexBaseChange
