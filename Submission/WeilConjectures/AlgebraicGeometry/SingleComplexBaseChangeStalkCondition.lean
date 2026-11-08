/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import Submission.WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- The base stalk ring O_{S,f(g' z)}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev R (z : X') := S.presheaf.stalk (f (g' z))
/-- The original scheme stalk ring O_{X,g' z}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev A (z : X') := X.presheaf.stalk (g' z)
/-- The new base stalk ring O_{S',f' z}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev B (z : X') := S'.presheaf.stalk (f' z)
/-- The base-changed scheme stalk ring O_{X',z}.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev C (z : X') := X'.presheaf.stalk z

/-- The R-algebra structure on A is the stalk map of f.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev leftAlgebra (z : X') : Algebra (R f g' z) (A g' z) :=
  (f.stalkMap (g' z)).hom.toAlgebra

/-- The R-algebra structure on B transports the stalk map of g along the square.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
abbrev rightAlgebra (z : X') : Algebra (R f g' z) (B f' z) :=
  ((S.presheaf.stalkCongr (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom ≫
    g.stalkMap (f' z)).hom.toAlgebra

/-- The two stalk projection maps form compatible algebra maps over the base stalk.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-single-complex-stalk-algebra-maps). -/
theorem exists_stalk_algebra_maps (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (f.stalkMap (g' z) ≫ g'.stalkMap z).hom.toAlgebra
    ∃ l : A g' z →ₐ[R f g' z] C z,
      ∃ r : B f' z →ₐ[R f g' z] C z,
        (∀ a, l a = (g'.stalkMap z).hom a) ∧
        (∀ b, r b = (f'.stalkMap z).hom b) ∧
        ∀ a b, Commute (l a) (r b) := by
  have _derived : HasDerivedCategory.{wSC}
      (SheafOfModules.{uSC} (moduleRings X.toRingedSpace)) := inferInstance
  let _ := leftAlgebra f g' z
  let _ := rightAlgebra f f' g g' sq z
  let _ := (f.stalkMap (g' z) ≫ g'.stalkMap z).hom.toAlgebra
  have hsq : f.stalkMap (g' z) ≫ g'.stalkMap z =
      (S.presheaf.stalkCongr
        (.of_eq (congrArg (fun k : X' ⟶ S => k z) sq.w))).hom ≫
          g.stalkMap (f' z) ≫ f'.stalkMap z := by
    rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp]
    exact Scheme.Hom.stalkMap_congr_hom _ _ sq.w z
  let l : A g' z →ₐ[R f g' z] C z :=
    { (g'.stalkMap z).hom with commutes' := fun _ => rfl }
  let r : B f' z →ₐ[R f g' z] C z :=
    { (f'.stalkMap z).hom with
      commutes' := fun a => (congrArg (fun k => k.hom a) hsq).symm }
  exact ⟨l, r, fun _ => rfl, fun _ => rfl, fun _ _ => Commute.all _ _⟩

/-- Existence of the tensor-to-stalk map with its two specified restrictions.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
theorem exists_tensorMap (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    ∃ a : A g' z ⊗[R f g' z] B f' z →+* C z,
      a.comp (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z)) =
        (g'.stalkMap z).hom ∧
      a.comp Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap z).hom := by
  let _ := leftAlgebra f g' z
  let _ := rightAlgebra f f' g g' sq z
  let _ := (f.stalkMap (g' z) ≫ g'.stalkMap z).hom.toAlgebra
  obtain ⟨l, r, hl, hr, hcomm⟩ := exists_stalk_algebra_maps f f' g g' sq z
  let a : A g' z ⊗[R f g' z] B f' z →ₐ[R f g' z] C z :=
    Algebra.TensorProduct.lift l r hcomm
  refine ⟨a.toRingHom, ?_, ?_⟩
  · ext x
    simp [a, hl]
  · ext y
    simp [a, hr]

/-- The canonical tensor-to-stalk map, chosen from its universal property.
Source: Stacks Project, perfect.tex, Tag 0DJ8, equation-bc; Tag 0DJ9.
(blueprint: def-pc-single-complex-base-change-stalk-condition). -/
def tensorMap (z : X') :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    A g' z ⊗[R f g' z] B f' z →+* C z :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  Classical.choose (exists_tensorMap f f' g g' sq z)

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
  represents : cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
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
  simp only [cast_eq, q, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    IsIso.hom_inv_id_assoc]

end AlgebraicGeometry.SingleComplexBaseChange
