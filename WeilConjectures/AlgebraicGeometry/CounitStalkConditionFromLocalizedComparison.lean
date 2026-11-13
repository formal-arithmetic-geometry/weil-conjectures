/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.LocalizedComparisonQuasiIsoSquare
import WeilConjectures.AlgebraicGeometry.StalkComparisonCoordinateInvariance

/-! # Stalk condition of the universal pullback counit

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem resolution_counit_isIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) :
    IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      (derivedPullback_spec g')
  have h : E = Scheme.Modules.tensorPullback g' :=
    CategoryTheory.Functor.ext hE (fun M N a => hEmap a)
  subst E
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
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

/-- The localized tensor comparison on the original complex suffices for the
coordinate-independent stalk condition of its universal pullback counit.

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8. -/
theorem counit_stalkCondition_of_localizedComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (h : ∀ z : X',
      letI := leftAlgebra f g' z
      letI := rightAlgebra f f' g g' sq z
      letI := (tensorMap f f' g g' sq z).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
      ∀ i : ℤ, IsIso ((cohomologyModel f f' g g' sq z G).localizedComparison i)) :
    StalkCondition f f' g g' sq (DerivedCategory.Q.obj G)
      (DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj G))
      (cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj G))) := by
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) G
  have : QuasiIso s := hs
  let E := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
  let c : Coordinates g' (DerivedCategory.Q.obj G) (DerivedCategory.Q.obj (E.obj G))
      (cast (by rfl) ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj G))) :=
    { P := P
      N := E.obj G
      e := asIso (DerivedCategory.Q.map s)
      e' := Iso.refl _
      isKFlat := hP
      counit_isIso := resolution_counit_isIso g' P hP
      t := E.map s
      represents := by
        simp only [Iso.refl_hom, Category.comp_id, asIso_hom, cast_eq]
        exact ((counit g').naturality
          ((HomotopyCategory.quotient _ (.up ℤ)).map s)).symm }
  intro d z i
  apply (isIso_stalkComparison_iff_coordinates f f' g g' sq d c z i).mpr
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  obtain ⟨e, he⟩ := exists_localizedComparison_quasiIso_square f f' g g' sq P G s hs z i
  change IsIso ((cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
      HomologicalComplex.homologyMap
        (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
          (.up ℤ)).map (E.map s)) i)
  rw [he]
  have := h z i
  infer_instance

end AlgebraicGeometry.SingleComplexBaseChange
