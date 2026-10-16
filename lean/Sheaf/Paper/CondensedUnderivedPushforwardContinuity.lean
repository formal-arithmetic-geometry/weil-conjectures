/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # The degree-zero consequence of qcqs pushforward continuity -/

@[expose] public section

universe u
open CategoryTheory Limits Abelian
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- Degree zero of the derived functor on single complexes is the original left exact
functor, naturally in the module.
Source: the injective-resolution computation of the zeroth right derived functor.
(blueprint: lem-weil-pbc-condensed-underived-pushforward-continuity) -/
noncomputable def singleComplexRightDerivedZeroIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    HomologicalComplex.single C (.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
      F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0 ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C 0).symm
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso C 0).symm
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.rightDerivedFunctorPlusCompatibility.symm
          (DerivedCategory.homologyFunctor D 0) ≪≫
        Functor.associator _ _ _) ≪≫
    F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
    F.rightDerivedZeroIsoSelf

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A qcqs pushforward on condensed module sheaves preserves filtered colimits.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), in degree zero.
(blueprint: lem-weil-pbc-condensed-underived-pushforward-continuity)
Proof. Put the filtered diagram of modules in degree zero. Its good truncation at
zero is isomorphic to itself. Qcqs continuity makes the image of its colimit cocone
a colimit after derived pushforward and zeroth homology. The natural identification
of this composite on single complexes with ordinary pushforward proves the claim. -/
theorem lowerStar_preservesFilteredColimit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) : PreservesColimit D (lowerStar Λ f) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfShape I A := inferInstance
  have : HasColimitsOfShape I (CochainComplex A ℤ) := inferInstance
  have : HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) := inferInstance
  let S := HomologicalComplex.single A (.up ℤ) 0
  let T := DerivedCategory.Q ⋙ (lowerStar Λ f).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ 0
  let E := D ⋙ S
  let π := Functor.whiskerLeft E ((ComplexShape.embeddingUpIntGE 0).πTruncGENatTrans A)
  have hi (i : I) : IsIso (π.app i) := by
    change IsIso (CochainComplex.πTruncGE (S.obj (D.obj i)) 0)
    infer_instance
  have : IsIso π := NatIso.isIso_of_isIso_app π
  have : HasColimit (E ⋙ (ComplexShape.embeddingUpIntGE 0).truncGEFunctor A) :=
    HasColimitsOfShape.has_colimit _
  have : HasColimit (E ⋙ T) := HasColimitsOfShape.has_colimit _
  have hc : IsColimit (condensedContinuityCocone E 0) :=
    (IsColimit.precomposeHomEquiv (asIso π) _).symm
      (colimit.isColimit (E ⋙ (ComplexShape.embeddingUpIntGE 0).truncGEFunctor A))
  have hcomparison := condensed_qcqs_pushforward_continuity Λ f E 0 (fun i n hn ↦ by
    have : CochainComplex.IsStrictlyGE (S.obj (D.obj i)) 0 := inferInstance
    exact CochainComplex.isZero_of_isGE (S.obj (D.obj i)) 0 n hn) 0
  have hT : IsColimit (T.mapCocone (condensedContinuityCocone E 0)) :=
    IsColimit.ofPointIso (colimit.isColimit (E ⋙ T)) (i := hcomparison)
  have : PreservesColimit E T := preservesColimit_of_preserves_colimit_cocone hc hT
  have : PreservesColimit D S := inferInstance
  have : PreservesColimit D (S ⋙ T) := comp_preservesColimit S T
  exact preservesColimit_of_natIso D
    (Functor.singleComplexRightDerivedZeroIso (lowerStar Λ f))

end AlgebraicGeometry.ProEtale.CondensedRing
