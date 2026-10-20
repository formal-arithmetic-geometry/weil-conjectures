/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffine
import Sheaf.AlgebraicGeometry.FiniteAlgebraHomExact
import Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift

/-! # FiniteDualityDegreeZeroCounitAction

Source: Stacks Project, finite duality and affine cohomology
(blueprint: lem-sc-finite-duality-degree-zero-counit-action). -/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

set_option maxHeartbeats 500000 in
-- The sectionwise action calculation unfolds scalar restriction and internal Hom.
/-- Descend finite duality's counit and algebra action to a quasi-coherent degree-zero
representative. The final evaluation-at-an-arbitrary-section identity is not asserted.

Source: Stacks Project, Duality for Schemes, Tags 0AX2 and 0AX3; Discriminants
and Differents, Tag 0FKW
(blueprint: lem-sc-finite-duality-degree-zero-counit-action).

Proof:
1. Use the affine derived sheaf-Hom adjunction to model restriction's right adjoint
   by Hom(A,-), with A acting by precomposition with multiplication. Since A is
   finite locally free, its dual is finite locally free. The evaluation
   `dual_tensor_hom_iso` identifies Hom(A,-) with tensor by that dual, and
   `finiteLocallyFree_tensorLeft_exact` makes it exact. Forgetting the A-action
   is exact and conservative, so the A-valued Hom functor is exact too.
   Its derived value on L[0] is the actual A-module Hom(A,L) in degree zero.
2. Finite duality identifies the given right adjoint a with that derived A-module
   construction, using `finite_affine_derived_equivalence` and uniqueness of
   right adjoints. Choose the comparison from the exact Hom model in step 1,
   with the unit-Hom identification given by actual evaluation; an arbitrary
   isomorphism from `finiteLocallyFree_derivedInternalHom_single` need not do this.
   The identification preserves counits: this is the second equation of
   `finite_duality_derived_hom`. Its first
   equation identifies the restriction counit with derived evaluation at one.
3. Apply the canonical affine single-pushforward comparison to the quasi-coherent
   representative M. Naturality of the right-derived unit identifies the composite
   through e0 with the pushforward of the derived identification of step 2.
   Degree-zero full faithfulness in the A-module category lifts the A-linear
   isomorphism; after restricting scalars this is e. Its counit lifts to epsilon.
   The derived counit equation gives the displayed
   equality of singleFunctor images.
4. The underived sheaf-Hom adjunction evaluates its counit at one. Because step 1
   used the exact sheaf-Hom functor, its degree-zero identification preserves that
   evaluation, yielding the sectionwise epsilon formula. The A-linear identification
   gives Phi(a omega)(b) = Phi(omega)(a b) on each open. Restriction compatibility
   follows from multiplication's compatibility with restrictions. These calculations
   include a = 0, b = 0, rank zero, and the empty open without cancellation. -/
theorem finiteDuality_degreeZero_counit_action
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (L : Y.Modules) [L.IsInvertible]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (K : schemeDerivedQCohCategory Y)
    (eL : K.obj ≅ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L)
    (M : X.Modules) (_hM : M.IsQuasicoherent)
    (e₀ : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M ≅ (a.obj K).obj)
    (c : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      ((Scheme.Modules.pushforward f).obj M) ≅
      (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))
    (_hc : c.hom = DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).inv.app M) ≫
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M))) :
    ∃ (e : (Scheme.Modules.pushforward f).obj M ≅
      SheafOfModules.homObj (R := Y.toRingedSpace.sheaf)
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) L),
    ∃ (ε : (Scheme.Modules.pushforward f).obj M ⟶ L),
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map ε =
        c.hom ≫ (schemeDerivedDirectImage f).map e₀.hom ≫
          comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom ≫ eL.hom ∧
      (∀ (U : Y.Opens)
        (ω : ((Scheme.Modules.pushforward f).obj M).presheaf.obj (Opposite.op U)),
        ε.app U ω =
          (PresheafOfModules.homObjEvalId
            ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
            L.val U ((Scheme.Modules.Hom.app e.hom U) ω))
              (1 : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))) ∧
      (∀ (U : Y.Opens) (a₁ b : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))
        (ω : M.val.obj (Opposite.op (f ⁻¹ᵁ U))),
        (PresheafOfModules.homObjEvalId
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
          L.val U ((Scheme.Modules.Hom.app e.hom U) (a₁ • ω))) b =
        (PresheafOfModules.homObjEvalId
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
          L.val U ((Scheme.Modules.Hom.app e.hom U) ω)) (a₁ * b)) := by
  obtain ⟨H, iH, adjH, haction, heval, _⟩ := sheafHom_affine_rightAdjoint f
  obtain ⟨hlim, hcolim⟩ := finite_algebraHom_exact f H iH
  let := hlim
  let := hcolim
  obtain ⟨j, hj⟩ := finite_exactHom_degreeZero_lift f L R comparison a adj K eL M _hM
    e₀ c _hc H iH adjH
  let T := SheafOfModules.restrictScalars f.toRingCatSheafHom
  let e := T.mapIso j ≪≫ iH.app L
  let ε := T.map j.hom ≫ adjH.counit.app L
  refine ⟨e, ε, hj, ?_, ?_⟩
  · intro U ω
    exact heval L U ((j.hom.val.app (op U)).hom ω)
  · intro U a₁ b ω
    have hlin := (j.hom.val.app (op U)).hom.map_smul a₁ ω
    have h := haction L U a₁ ((j.hom.val.app (op U)).hom ω) (Over.mk (𝟙 U)) b
    change ((((iH.hom.app L).val.app (op U)).hom
      ((j.hom.val.app (op U)).hom (a₁ • ω))).app (op (Over.mk (𝟙 U)))).hom b =
      ((((iH.hom.app L).val.app (op U)).hom
        ((j.hom.val.app (op U)).hom ω)).app (op (Over.mk (𝟙 U)))).hom (a₁ * b)
    rw [hlin]
    have hid : (((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
        RingCat (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj X.ringCatSheaf).obj.map
          (Over.mk (𝟙 U)).hom.op = 𝟙 _ := by
      change (X.presheaf ⋙ forget₂ CommRingCat RingCat).map (𝟙 _) = 𝟙 _
      exact CategoryTheory.Functor.map_id _ _
    rw [hid] at h
    exact h

end AlgebraicGeometry
