/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule

import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.FiniteExactHomDerivedMate
import Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport

/-! # Lifting the exact affine right adjoint to degree zero
Source: Stacks Project, Tags 0AX2, 0AX3 and 0AVW
(blueprint: lem-sc-finite-exact-hom-degree-zero-lift). -/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry


private theorem scalarCounitTransport
    {C A B : Type*} [Category* C] [Category* A] [Category* B]
    (T : A ⥤ B) (H : B ⥤ A) (ε : H ⋙ T ⟶ 𝟭 B)
    (G : C ⥤ A) (F : C ⥤ B) (γ : G ⋙ T ≅ F)
    {x₀ x : C} {k l : B} (e₀ : x₀ ⟶ x) (eL : k ⟶ l)
    (φ : G.obj x ⟶ H.obj k) (d : F.obj x ⟶ k)
    (hφ : T.map φ ≫ ε.app k = γ.hom.app x ≫ d) :
    γ.inv.app x₀ ≫ T.map (G.map e₀ ≫ φ ≫ H.map eL) ≫ ε.app l =
      F.map e₀ ≫ d ≫ eL := by
  have hn := ε.naturality eL
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hg := γ.hom.naturality e₀
  dsimp only [Functor.comp_map] at hg
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, ← Category.assoc (T.map φ), hφ]
  simp only [Category.assoc]
  rw [reassoc_of% hg, Iso.inv_hom_id_app_assoc]

-- The retained interface includes iH, but lifting uses only the specified exact adjunction.
set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- Elaborating the canonical derived comparisons involves large sheaf category instances.
/-- Lift the derived finite-duality comparison to an isomorphism over the direct-image
algebra. This statement does not identify the underlying Hom model's evaluation or action.
Source: Stacks Project, Duality for Schemes, Tags 0AX2 and 0AX3; Tag 0AVW
(blueprint: lem-sc-finite-exact-hom-degree-zero-lift).

Proof:
1. Choose the standard derived category of A-modules. Derive the adjunction T ⊣ H.
   T is exact and H is exact by the explicit hypotheses.
   Their derived functors are the localization of the termwise functors, and on single
   complexes their canonical comparisons identify their values with T(N)[0] and H(L)[0].
2. Let G = Rg_*, rho = RT and rhoR = RH, with derived adjunction adjA. Construct
   gamma : G ⋙ rho ≅ Rf_* from the exact-restriction comparison, the inverse
   derived-composite comparison, and the identity g_* ⋙ T = f_*. Put J = iX ⋙ G
   and beta : R ⋙ iY ≅ J ⋙ rho using comparison and gamma.symm. The finite affine
   derived equivalence makes J fully faithful. Since K is bounded below by eL,
   finite_scalar_right_adjoint_qcoh puts rhoR(K) in the essential image of J.
   Define phi as the adjA-transpose of beta.inv.app(a(K)) followed by
   iY(adj.counit.app K). For every N, composition with phi is bijective by full
   faithfulness of J and iY and the two adjunction hom equivalences. Choose an
   isomorphism J(N0) ≅ rhoR(K) from essential image membership; bijectivity supplies
   a right inverse to phi, and injectivity at a(K) makes it a left inverse. Thus phi
   is an isomorphism. Its transpose equation gives rho(phi) followed by
   adjA.counit = gamma.hom followed by comparison.inv followed by the geometric
   counit, with this same gamma.
3. Construct the g_* single comparison from its right-derived unit. After exact
   scalar restriction and the canonical gamma, it is the f_* single comparison,
   which is invertible by `affine_singlePushforward_unit_isIso` and hM. Derived
   restriction reflects isomorphisms: its cohomology is underived restriction,
   which reflects isomorphisms since the underlying abelian sheaf is unchanged.
   Thus the g_* single comparison is invertible. Naturality along e0 and eL
   gives an A-linear derived isomorphism from (g_* M)[0] to H(L)[0]. Full faithfulness
   of the single functor over A lifts it to j. The derived counit equation, together
   with the derived-adjunction counit factorization and the canonical single comparisons,
   gives the equality below. Use this same gamma and its factorization built from the
   identity g_* ⋙ T = f_*, the exact-restriction comparison and the derived-composite
   comparison, not an arbitrary isomorphism with that type. Their localization
   factorization equations identify the
   composite on M[0] with the inverse single comparison followed by the derived unit.
   Naturality along e₀ and eL then gives the displayed composite; hc identifies its
   initial factor with c.hom.
No normalization of the underlying Hom isomorphism is needed in this lifting step.
Zero modules, empty opens, and rank zero use the same full-faithfulness argument. -/
theorem finite_exactHom_degreeZero_lift
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
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)))
    (H : Y.Modules ⥤ SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    (iH : H ⋙ SheafOfModules.restrictScalars f.toRingCatSheafHom ≅
      (SheafOfModules.homFunctor Y.sheaf).obj
        (op ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))))
    (adjH : SheafOfModules.restrictScalars f.toRingCatSheafHom ⊣ H)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    ∃ j : (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
          ((SheafOfModules.restrictScalars f.toRingCatSheafHom).map j.hom ≫
            adjH.counit.app L) =
        c.hom ≫ (schemeDerivedDirectImage f).map e₀.hom ≫
          comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom ≫ eL.hom := by
  classical
  let A := SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  let T : A ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
    SheafOfModules.restrictScalars f.toRingCatSheafHom
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let G := RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)
  let H' : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤ A := H
  have : PreservesFiniteLimits T := by
    have : PreservesFiniteLimits
        (T ⋙ SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)) := by
      change PreservesFiniteLimits
        (SheafOfModules.toSheaf (moduleRings (directImageAlgebraSpace f)))
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves T
      (SheafOfModules.toSheaf (moduleRings Y.toRingedSpace))
  have : PreservesFiniteColimits T := by
    exact @sheafAlgebraRestrictScalars_preservesFiniteColimits.{u, wY, u + 1} Y
      (Under.mk (⟨f.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf))
      inferInstance (by change HasDerivedCategory A; infer_instance)
  let adjH' : T ⊣ H' := adjH
  have : H'.Additive := adjH'.right_adjoint_additive
  let γ : G ⋙ T.mapDerivedCategory ≅ schemeDerivedDirectImage f :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).symm ≪≫
      Functor.rightDerivedFunctorNatIso
        (show F ⋙ T ≅ RingedSpace.moduleDirectImage f.toLRSHom.toShHom from Iso.refl _)
  let adjA : T.mapDerivedCategory ⊣ H'.rightDerivedFunctor :=
    adjH'.mapDerivedCategoryRightDerivedAdjunction
  have hK : ∃ n : ℤ, K.obj.IsGE n := by
    refine ⟨0, ?_⟩
    exact DerivedCategory.TStructure.t.isGE_of_iso eL.symm 0
  obtain ⟨φ, hφ⟩ := finite_exactHom_derived_mate f R comparison a adj K hK H' adjH' γ
  let e : G.obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≅
        H'.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L) :=
    G.mapIso e₀ ≪≫ φ ≪≫ H'.rightDerivedFunctor.mapIso eL
  obtain ⟨j, hj⟩ := finite_exactHom_single_counit_transport f M _hM L H' adjH' γ rfl e
  have ht := scalarCounitTransport T.mapDerivedCategory H'.rightDerivedFunctor
    adjA.counit G (schemeDerivedDirectImage f) γ e₀.hom eL.hom φ.hom
    (comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom) hφ
  refine ⟨j, ?_⟩
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom] at hj
  rw [ht] at hj
  rw [_hc]
  simpa only [Category.assoc] using hj

end AlgebraicGeometry
