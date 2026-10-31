/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtalePullbackStalkCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonStalk

/-! # Intrinsic finite-coefficient comparison on stalks

Source: Stacks Project, Tags 03CY, 0GLZ and 0993.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem coefficientGerm_smul
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (r : ULift.{u + 1, u} A)
    (a : M.val.obj (op N.right)) :
    proEtaleCoefficientModuleGerm x A M N
      (((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op N.right)) r • a) =
      r • proEtaleCoefficientModuleGerm x A M N a := by
  let O := proEtaleConstantRing T A
  let R := proEtaleGeometricStalkRingDiagram x O
  let SM := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget x)
    (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
  let f : N ⟶ proEtaleConstantGermNeighbourhood x :=
    StructuredArrow.homMk (MorphismProperty.Over.homMk N.right.hom) (by
      apply Over.OverMorphism.ext
      exact Over.w N.hom)
  let η := toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
  have hη : O.obj.map f.right.op (η.app (op (ProEt.mk (𝟙 T))) r) =
      η.app (op N.right) r := by
    have h := ConcreteCategory.congr_hom (η.naturality f.right.op) r
    exact h.symm
  have hr : proEtaleConstantRingGerm x A r =
      colimit.ι R (op N) (η.app (op N.right) r) := by
    have h := ConcreteCategory.congr_hom (colimit.w R f.op)
      (η.app (op (ProEt.mk (𝟙 T))) r)
    change colimit.ι R (op N)
      (O.obj.map f.right.op (η.app (op (ProEt.mk (𝟙 T))) r)) = _ at h
    rw [hη] at h
    exact h.symm
  have hsmul := (PresheafOfModules.ModuleColimit.smul_eq
    (colimit.isColimit R) (colimit.isColimit SM.presheaf)
      (U := op N) (η.app (op N.right) r) a).symm
  have hr' : PresheafOfModules.ModuleColimit.ιR (colimit.cocone R)
      (η.app (op N.right) r) = proEtaleConstantRingGerm x A r := hr.symm
  rw [hr'] at hsmul
  exact hsmul



private noncomputable def fixedStalk (T : Scheme.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (A : Type u) [CommRing A] :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1, u} A) :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood x)ᵒᵖ
      T.ProEtᵒᵖ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
      (proEtaleGeometricNeighbourhoodForget x).op ⋙ colim

private noncomputable def stalkCocone
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A]
    (F : proEtaleRingModules T (proEtaleConstantRing T A)) :
    Cocone (proEtaleGeometricStalkDiagram x ((proEtaleModuleRestriction T A).obj F)) where
  pt := (finiteCoefficientModuleStalkFunctor x A).obj F
  ι :=
    { app N := ModuleCat.ofHom
        (X := (proEtaleGeometricStalkDiagram x
          ((proEtaleModuleRestriction T A).obj F)).obj N)
        (Y := (finiteCoefficientModuleStalkFunctor x A).obj F)
        { toFun := proEtaleCoefficientModuleGerm x A F N.unop
          map_add' := map_add (colimit.ι
            ((proEtaleGeometricNeighbourhoodForget x).op ⋙ F.val.presheaf) N).hom
          map_smul' := fun r a ↦ coefficientGerm_smul x A F N.unop r a }
      naturality N M f := by
        ext a
        exact ConcreteCategory.congr_hom
          (colimit.w ((proEtaleGeometricNeighbourhoodForget x).op ⋙ F.val.presheaf) f) a }

private noncomputable def restrictionStalkIso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A]
    (F : proEtaleRingModules T (proEtaleConstantRing T A)) :
    (fixedStalk T x A).obj ((proEtaleModuleRestriction T A).obj F) ≅
      (finiteCoefficientModuleStalkFunctor x A).obj F := by
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}
  have hc : IsColimit (U.mapCocone (stalkCocone x A F)) :=
    colimit.isColimit ((proEtaleGeometricNeighbourhoodForget x).op ⋙ F.val.presheaf)
  have hc' : IsColimit (stalkCocone x A F) := isColimitOfReflects U hc
  exact colimit.isoColimitCocone ⟨_, hc'⟩

private noncomputable def restrictionStalkNatIso
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] :
    proEtaleModuleRestriction T A ⋙ fixedStalk T x A ≅
      finiteCoefficientModuleStalkFunctor x A :=
  NatIso.ofComponents (restrictionStalkIso x A) (by
    intro F G f
    apply colimit.hom_ext
    intro N
    change colimit.ι _ N ≫ (colim.map _) ≫ (restrictionStalkIso x A G).hom =
      colimit.ι _ N ≫ (restrictionStalkIso x A F).hom ≫ _
    simp only [colimit.ι_map_assoc, restrictionStalkIso,
      colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom_assoc]
    ext a
    exact (ConcreteCategory.congr_hom
      (colimit.ι_map (Functor.whiskerLeft
        (proEtaleGeometricNeighbourhoodForget x).op
        ((PresheafOfModules.toPresheaf _).map f.val)) N) a).symm)

/-- The intrinsic finite-coefficient inverse image has the ordinary etale stalk.
Source: Stacks Project, Tags 03CY, 0GLZ and 0993
(blueprint: lem-z8-intrinsic-finite-stalk-comparison).

Proof: restriction to constant scalars is inverse to intrinsic realization by the
module-sheafification counit. The fixed-scalar and intrinsic stalks are colimits
of the same additive diagram. The constant ring germ makes every coprojection
linear, so the comparison is a natural module isomorphism. Compose it with the
canonical etale-to-pro-etale stalk comparison. The construction includes zero
rings and zero modules and requires no point outside the specified geometric point. -/
theorem exists_intrinsicFiniteCoefficientStalkComparison
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] [Finite A] :
    Nonempty (ProEtale.finiteCoefficientIntrinsicComparison T A ⋙
        finiteCoefficientModuleStalkFunctor x A ≅
      (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} (ULift.{u + 1, u} A))) := by
  classical
  let R := ProEtale.finiteCoefficientIntrinsicRealization T A
  let G := proEtaleModuleRestriction T A
  have : R.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  let ε : G ⋙ R ≅ 𝟭 _ := NatIso.ofComponents
    (fun M ↦ asIso ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).counit.app M))
    (by intro M N f; exact (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).counit.naturality f)
  let δ : R ⋙ G ≅ 𝟭 _ := Functor.fullyFaithfulCancelRight R
    (Functor.associator R G R ≪≫ Functor.isoWhiskerLeft R ε ≪≫
      Functor.rightUnitor R ≪≫ (Functor.leftUnitor R).symm)
  let h := restrictionStalkNatIso x A
  let ρ : R ⋙ finiteCoefficientModuleStalkFunctor x A ≅ fixedStalk T x A :=
    Functor.isoWhiskerLeft R h.symm ≪≫ (Functor.associator R G _).symm ≪≫
      Functor.isoWhiskerRight δ _ ≪≫ Functor.leftUnitor _
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  obtain ⟨c, _⟩ := (proEtale_comparison_stalk T Ω x).2.2
    (ULift.{u + 1, u} A)
  exact ⟨Functor.associator C R _ ≪≫ Functor.isoWhiskerLeft C ρ ≪≫ c⟩

end AlgebraicGeometry.Scheme
