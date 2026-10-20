/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.IntegralFinitePullbackComposition

/-!
# Coherence of pro-etale pullback stalk comparisons

Source: Stacks Project, Tags 05V1 and 0F4F, and proetale.tex Tag 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme


/-- The stalk functor on cochain complexes, obtained term by term from the
finite-coefficient geometric stalk.  Source: Stacks Tags 0F4F and 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable def proEtaleFiniteCoefficientStalkComplexFunctor
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (u : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ℤ :=
  (finiteCoefficientModuleStalkFunctor u A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Pullback followed by the termwise geometric stalk on complexes.  Source:
Stacks Tags 05V1 and 0F4F (blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable def proEtalePullbackFiniteCoefficientStalkComplexFunctor
    {T S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : T ⟶ S) (u : Spec (.of Ω) ⟶ T) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules S (proEtaleConstantRing S A)) ℤ ⥤
      CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ℤ :=
  (proEtaleConstantRingPullback A t).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    proEtaleFiniteCoefficientStalkComplexFunctor u A

/-- The actual additive colimit coprojection, viewed in the stalk with constant scalars.
Source: Stacks Tags 0F6B and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleCoefficientModuleGerm {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    (finiteCoefficientModuleStalkFunctor x A).obj M :=
  (colimit.ι ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) (op N)) a

/-- Both representative formulas defining the canonical comparison. The first quantifies
all comma representatives `(P, theta, a)`; the equality of lifts says that `N` is their
projected pointed neighbourhood. The second is the inverse formula on unit germs.
Source: Stacks Tags 05V1 and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def ProEtalePullbackStalkGermNormalized (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (c : proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A) : Prop :=
  (∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ t))
    (P : ProEtaleGeometricNeighbourhood x)
    (θ : P.right ⟶ (proEtaleBaseChange t).obj N.right)
    (a : M.val.obj (op N.right)),
    P.hom.left ≫ θ.left ≫ pullback.fst N.right.hom t = N.hom.left →
    c.hom.app M (proEtaleCoefficientModuleGerm x A
      ((proEtaleConstantRingPullback A t).obj M) P
      (((proEtaleConstantRingPullback A t).obj M).val.map θ.op
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a))) =
      proEtaleCoefficientModuleGerm (x ≫ t) A M N a) ∧
  (∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
    (N : ProEtaleGeometricNeighbourhood (x ≫ t))
    (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
    (a : M.val.obj (op N.right)),
    l.left ≫ pullback.fst N.right.hom t = N.hom.left →
    c.inv.app M (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
      proEtaleCoefficientModuleGerm x A ((proEtaleConstantRingPullback A t).obj M)
        (StructuredArrow.mk l)
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a))

private theorem stalkOfUnitComparison {T S : Scheme.{u}} (t : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (F : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})
    (G : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
    (g : F ⟶ (proEtaleSheafDirectImage t AddCommGrpCat.{u + 1}).obj G)
    [IsIso (((proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}).homEquiv F G).symm g)] :
    ∃ d : proEtaleGeometricStalk x G ≅ proEtaleGeometricStalk (x ≫ t) F,
      ∀ (N : ProEtaleGeometricNeighbourhood (x ≫ t))
        (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right)),
        l.left ≫ pullback.fst N.right.hom t = N.hom.left →
        g.hom.app (op N.right) ≫ colimit.ι (proEtaleGeometricStalkDiagram x G)
          (op (StructuredArrow.mk l)) ≫ d.hom =
            colimit.ι (proEtaleGeometricStalkDiagram (x ≫ t) F) (op N) := by
  let a := proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}
  let b := (a.homEquiv F G).symm g
  let SX : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood x)ᵒᵖ T.ProEtᵒᵖ
        AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget x).op ⋙ colim
  obtain ⟨c, hc, _, _⟩ := proEtaleInverseImage_abelianStalk t x
  let d := SX.mapIso (asIso b).symm ≪≫ c F
  refine ⟨d, ?_⟩
  intro N l hl
  have hb := (a.homEquiv F G).apply_symm_apply g
  rw [Adjunction.homEquiv_unit] at hb
  have hu : g ≫ (proEtaleSheafDirectImage t AddCommGrpCat.{u + 1}).map (inv b) =
      a.unit.app F := by
    rw [← hb, Category.assoc, ← CategoryTheory.Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hu' := congrArg (fun q ↦ q.hom.app (op N.right)) hu
  change g.hom.app (op N.right) ≫
    (inv b).hom.app (op ((proEtaleBaseChange t).obj N.right)) = _ at hu'
  change g.hom.app (op N.right) ≫ colimit.ι (proEtaleGeometricStalkDiagram x G)
    (op (StructuredArrow.mk l)) ≫
    colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget x).op (inv b).hom) ≫
    (c F).hom = _
  rw [colimit.ι_map_assoc]
  change g.hom.app (op N.right) ≫
    (inv b).hom.app (op ((proEtaleBaseChange t).obj N.right)) ≫
    colimit.ι (proEtaleGeometricStalkDiagram x
      ((proEtaleSheafInverseImage t AddCommGrpCat.{u + 1}).obj F))
      (op (StructuredArrow.mk l)) ≫ (c F).hom = _
  rw [← Category.assoc, hu']
  exact hc F N l hl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackStalkAdditive (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃ d : ∀ M : proEtaleRingModules S (proEtaleConstantRing S A),
      AddCommGrpCat.of ((finiteCoefficientModuleStalkFunctor x A).obj
        ((proEtaleConstantRingPullback A t).obj M)) ≅
      AddCommGrpCat.of ((finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M),
      ∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
        (N : ProEtaleGeometricNeighbourhood (x ≫ t))
        (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
        (a : M.val.obj (op N.right)),
        l.left ≫ pullback.fst N.right.hom t = N.hom.left →
        (d M).hom (proEtaleCoefficientModuleGerm x A
          ((proEtaleConstantRingPullback A t).obj M) (StructuredArrow.mk l)
          (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a)) =
          proEtaleCoefficientModuleGerm (x ≫ t) A M N a := by
  let R : Sheaf (ProEt.topology S) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  let B : Sheaf (ProEt.topology T) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)
  let P := SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R
  let Q := SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} B
  let L := proEtaleConstantRingPullback A t
  let adj := proEtaleConstantRingAdjunction A t
  let a := proEtaleSheafAdjunction t AddCommGrpCat.{u + 1}
  let b (M : proEtaleRingModules S (proEtaleConstantRing S A)) :=
    (a.homEquiv (P.obj M) (Q.obj (L.obj M))).symm (P.map (adj.unit.app M))
  have (M : proEtaleRingModules S (proEtaleConstantRing S A)) : IsIso (b M) :=
    ringUnitComparison t (proEtaleConstantRing S A) (proEtaleConstantRing T A)
      (proEtaleConstantRingComparison t A) adj M
  have h (M : proEtaleRingModules S (proEtaleConstantRing S A)) :=
    stalkOfUnitComparison t x (P.obj M) (Q.obj (L.obj M)) (P.map (adj.unit.app M))
  choose d hd using h
  refine ⟨d, ?_⟩
  intro M N l z hl
  exact ConcreteCategory.congr_hom (hd M N l hl) z

private def pairedLift {T S : Scheme.{u}} (t : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (N : ProEtaleGeometricNeighbourhood (x ≫ t)) :
    Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right) :=
  Over.homMk (pullback.lift N.hom.left x (Over.w N.hom)) (by exact pullback.lift_snd _ _ _)
private theorem pairedLift_fst {T S : Scheme.{u}} (t : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (N : ProEtaleGeometricNeighbourhood (x ≫ t)) :
    (pairedLift t x N).left ≫ pullback.fst N.right.hom t = N.hom.left := by
  exact pullback.lift_fst _ _ _
private theorem coefficientGerm_restriction {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T)
    (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    {P Q : ProEtaleGeometricNeighbourhood x} (f : P ⟶ Q)
    (z : M.val.obj (op Q.right)) :
    proEtaleCoefficientModuleGerm x A M P (M.val.map f.right.op z) =
      proEtaleCoefficientModuleGerm x A M Q z :=
  ConcreteCategory.congr_hom
    (colimit.w ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) f.op) z
private theorem unitConstant_smul (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S)
    (M : proEtaleRingModules S (proEtaleConstantRing S A)) (V : S.ProEt)
    (r : ULift.{u + 1, u} A) (z : M.val.obj (op V)) :
    (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V))
      (((toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op V)) r • z) =
      ((toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op ((proEtaleBaseChange t).obj V))) r •
        (show ((proEtaleConstantRingPullback A t).obj M).val.obj
          (op ((proEtaleBaseChange t).obj V)) from
            ((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V) z) := by
  let C := CommRingCat.of (ULift.{u + 1, u} A)
  have hr : proEtaleRingDirectImageMap t (proEtaleConstantRing S A)
      (proEtaleConstantRing T A) (proEtaleConstantRingComparison t A) =
      proEtaleCoefficientDirectImageMap t A :=
    ((proEtaleSheafAdjunction t CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hη : toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C) ≫
      (proEtaleCoefficientDirectImageMap t A).hom =
      Functor.whiskerLeft (proEtaleBaseChange t).op
        (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C)) := by
    exact ((sheafificationAdjunction (ProEt.topology S) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hη (op V)) r
  have hu := (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V)).hom.map_smul
    (((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C)).app (op V)) r) z
  change _ =
    ((proEtaleRingDirectImageMap t (proEtaleConstantRing S A) (proEtaleConstantRing T A)
      (proEtaleConstantRingComparison t A)).hom.app (op V))
        (((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C)).app (op V)) r) •
      (show ((proEtaleConstantRingPullback A t).obj M).val.obj
        (op ((proEtaleBaseChange t).obj V)) from
          ((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op V) z) at hu
  change (proEtaleCoefficientDirectImageMap t A).hom.app (op V)
    (((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj C)).app (op V)) r) =
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj C)).app
        (op ((proEtaleBaseChange t).obj V))) r at h
  rw [hr] at hu
  erw [h] at hu
  exact hu

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


private theorem pullbackStalkInverseLinear (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃ e : ∀ M : proEtaleRingModules S (proEtaleConstantRing S A),
      (finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M ≅
        (finiteCoefficientModuleStalkFunctor x A).obj ((proEtaleConstantRingPullback A t).obj M),
      ∀ (M : proEtaleRingModules S (proEtaleConstantRing S A))
        (N : ProEtaleGeometricNeighbourhood (x ≫ t))
        (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
        (a : M.val.obj (op N.right)),
        l.left ≫ pullback.fst N.right.hom t = N.hom.left →
        (e M).hom (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
          proEtaleCoefficientModuleGerm x A
            ((proEtaleConstantRingPullback A t).obj M) (StructuredArrow.mk l)
            (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a) := by
  obtain ⟨d, hd⟩ := pullbackStalkAdditive A t x
  have hi (M : proEtaleRingModules S (proEtaleConstantRing S A))
      (N : ProEtaleGeometricNeighbourhood (x ≫ t))
      (l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right))
      (a : M.val.obj (op N.right))
      (hl : l.left ≫ pullback.fst N.right.hom t = N.hom.left) :
      (d M).inv (proEtaleCoefficientModuleGerm (x ≫ t) A M N a) =
        proEtaleCoefficientModuleGerm x A
          ((proEtaleConstantRingPullback A t).obj M) (StructuredArrow.mk l)
          (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a) := by
    apply (d M).addCommGroupIsoToAddEquiv.injective
    change (d M).hom ((d M).inv _) = (d M).hom _
    rw [Iso.inv_hom_id_apply, hd M N l a hl]
  let e (M : proEtaleRingModules S (proEtaleConstantRing S A)) :
      (finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M ≅
        (finiteCoefficientModuleStalkFunctor x A).obj ((proEtaleConstantRingPullback A t).obj M) :=
    LinearEquiv.toModuleIso
      (X₁ := (finiteCoefficientModuleStalkFunctor (x ≫ t) A).obj M)
      (X₂ := (finiteCoefficientModuleStalkFunctor x A).obj
        ((proEtaleConstantRingPullback A t).obj M))
      { __ := (d M).symm.addCommGroupIsoToAddEquiv
        map_smul' := by
          intro r z
          let R := proEtaleGeometricStalkRingDiagram (x ≫ t) (proEtaleConstantRing S A)
          let SM := (PresheafOfModules.pushforward₀
            (proEtaleGeometricNeighbourhoodForget (x ≫ t))
            ((proEtaleConstantRing S A).obj ⋙
              forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
          obtain ⟨N, a, rfl⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
            (hcR := colimit.isColimit R) (hcM := colimit.isColimit SM.presheaf) z
          change (d M).inv (r • proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a) =
            r • (d M).inv (proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a)
          rw [← coefficientGerm_smul,
            hi M N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop),
            hi M N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop),
            unitConstant_smul]
          exact coefficientGerm_smul x A _ _ r _ }
  exact ⟨e, hi⟩

/-- The normalized comparison exists uniquely; this fixes its data before any coherence
assertion. Source: Stacks Tags 05V1 and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: apply `proEtaleInverseImage_abelianStalk` to the underlying abelian sheaf.
Sheafification does not change its stalk by `proEtaleGeometricStalk_sheafification`.
The two colimit maps send `(P,theta,a)` to the projected germ and a germ to its
pullback-unit section. Restriction relations make both maps well defined; the pointed
arrow theta proves the second composite is the identity. Constant scalars are preserved
by the specified coefficient comparison, so these maps are A-linear. The unit is the
normalized module adjunction unit. A module morphism acts only on a, giving naturality.
Every stalk element is represented after sheafification by such a germ; hence the first
formula determines every component, proving uniqueness. -/
theorem proEtalePullbackStalkComparison_existsUnique (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    ∃! c : proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A,
      ProEtalePullbackStalkGermNormalized A t x c := by
  obtain ⟨e, he⟩ := pullbackStalkInverseLinear A t x
  let η : finiteCoefficientModuleStalkFunctor (x ≫ t) A ⟶
      proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A :=
    { app := fun M ↦ (e M).hom
      naturality := by
        intro M Q f
        apply (forget₂ (ModuleCat (ULift.{u + 1, u} A)) AddCommGrpCat).map_injective
        apply colimit.hom_ext
        intro N
        ext a
        have hf (y : Spec (.of Ω) ⟶ S) (P : ProEtaleGeometricNeighbourhood y)
            (a : M.val.obj (op P.right)) :
            (finiteCoefficientModuleStalkFunctor y A).map f
              (proEtaleCoefficientModuleGerm y A M P a) =
            proEtaleCoefficientModuleGerm y A Q P (f.val.app (op P.right) a) := by
          exact ConcreteCategory.congr_hom
            (colimit.ι_map (Functor.whiskerLeft
              (proEtaleGeometricNeighbourhoodForget y).op
              ((SheafOfModules.toSheaf _).map f).hom) (op P)) a
        change (e Q).hom ((finiteCoefficientModuleStalkFunctor (x ≫ t) A).map f
            (proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a)) =
          (finiteCoefficientModuleStalkFunctor x A).map
            ((proEtaleConstantRingPullback A t).map f)
            ((e M).hom (proEtaleCoefficientModuleGerm (x ≫ t) A M N.unop a))
        rw [hf, he Q N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop),
          he M N.unop (pairedLift t x N.unop) _ (pairedLift_fst t x N.unop)]
        have hmap := ConcreteCategory.congr_hom
          (colimit.ι_map (Functor.whiskerLeft
            (proEtaleGeometricNeighbourhoodForget x).op
            ((SheafOfModules.toSheaf _).map ((proEtaleConstantRingPullback A t).map f)).hom)
            (op (StructuredArrow.mk (pairedLift t x N.unop))))
              (((proEtaleConstantRingAdjunction A t).unit.app M).val.app
                (op N.unop.right) a)
        rw [show (finiteCoefficientModuleStalkFunctor x A).map
            ((proEtaleConstantRingPullback A t).map f)
            (proEtaleCoefficientModuleGerm x A _ (StructuredArrow.mk (pairedLift t x N.unop))
              (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.unop.right) a)) =
            proEtaleCoefficientModuleGerm x A _ (StructuredArrow.mk (pairedLift t x N.unop))
              ((((proEtaleConstantRingPullback A t).map f).val.app
                (op ((proEtaleBaseChange t).obj N.unop.right)))
                (((proEtaleConstantRingAdjunction A t).unit.app M).val.app
                  (op N.unop.right) a)) from hmap]
        congr 1
        exact congrArg (fun q ↦ q.val.app (op N.unop.right) a)
          ((proEtaleConstantRingAdjunction A t).unit.naturality f) }
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let c := (asIso η).symm
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro M N P θ a hθ
    let l : Over.mk x ⟶ (ProEt.forget T).obj ((proEtaleBaseChange t).obj N.right) :=
      P.hom ≫ (ProEt.forget T).map θ
    have hl : l.left ≫ pullback.fst N.right.hom t = N.hom.left := hθ
    let q : P ⟶ StructuredArrow.mk l := StructuredArrow.homMk θ rfl
    have hr := coefficientGerm_restriction x A
      ((proEtaleConstantRingPullback A t).obj M) q
      (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a)
    change proEtaleCoefficientModuleGerm x A _ P
      (((proEtaleConstantRingPullback A t).obj M).val.map θ.op
        (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a)) =
        proEtaleCoefficientModuleGerm x A _ (StructuredArrow.mk l)
          (((proEtaleConstantRingAdjunction A t).unit.app M).val.app (op N.right) a) at hr
    apply (ConcreteCategory.bijective_of_isIso (c.inv.app M)).1
    change (c.inv.app M) ((c.hom.app M) _) = (e M).hom _
    rw [← ModuleCat.comp_apply, c.hom_inv_id_app]
    exact hr.trans (he M N l a hl).symm
  · exact he
  · intro c' hc'
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply (forget₂ (ModuleCat (ULift.{u + 1, u} A)) AddCommGrpCat).map_injective
    apply colimit.hom_ext
    intro N
    ext a
    exact (hc'.2 M N.unop (pairedLift t x N.unop) a (pairedLift_fst t x N.unop)).trans
      (he M N.unop (pairedLift t x N.unop) a (pairedLift_fst t x N.unop)).symm


/-- The unique comparison specified on all represented germs, not a choice of an
unnormalized isomorphism. Source: Stacks Tags 05V1 and 0F4F
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtalePullbackStalkComparison (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (x ≫ t) A :=
  (proEtalePullbackStalkComparison_existsUnique A t x).exists.choose

/-- Reindex pointed neighbourhoods by precomposition with the field automorphism.
The underlying site object and section are unchanged. Source: Stacks Tag 05V1
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkNeighbourhoodReparam {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    ProEtaleGeometricNeighbourhood x ⥤
      ProEtaleGeometricNeighbourhood (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) :=
  StructuredArrow.map (T := ProEt.forget T)
    (Over.homMk (Spec.map (CommRingCat.ofHom α.toRingHom)) rfl)

private noncomputable def reparamAdditive (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
    AddCommGrpCat.of ((finiteCoefficientModuleStalkFunctor x A).obj M) ⟶
      AddCommGrpCat.of ((finiteCoefficientModuleStalkFunctor
        (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A).obj M) :=
  show colimit ((proEtaleGeometricNeighbourhoodForget x).op ⋙ M.val.presheaf) ⟶
      colimit ((proEtaleGeometricNeighbourhoodForget
        (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).op ⋙ M.val.presheaf) from
    colimit.pre ((proEtaleGeometricNeighbourhoodForget
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).op ⋙ M.val.presheaf)
        (proEtaleStalkNeighbourhoodReparam x α).op

private theorem reparamAdditive_germ
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (A : Type u) [CommRing A]
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)) :
    reparamAdditive A x α M (proEtaleCoefficientModuleGerm x A M N a) =
      proEtaleCoefficientModuleGerm _ A M
        ((proEtaleStalkNeighbourhoodReparam x α).obj N) a := by
  exact ConcreteCategory.congr_hom
    (colimit.ι_pre ((proEtaleGeometricNeighbourhoodForget
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).op ⋙ M.val.presheaf)
      (proEtaleStalkNeighbourhoodReparam x α).op (op N)) a

private noncomputable def reparamLinear (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
    (finiteCoefficientModuleStalkFunctor x A).obj M ⟶
      (finiteCoefficientModuleStalkFunctor
        (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A).obj M :=
  ModuleCat.ofHom (X := (finiteCoefficientModuleStalkFunctor x A).obj M)
    (Y := (finiteCoefficientModuleStalkFunctor
      (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A).obj M)
    { toAddHom := (reparamAdditive A x α M).hom
      map_smul' := by
        intro r z
        let R := proEtaleGeometricStalkRingDiagram x (proEtaleConstantRing T A)
        let SM := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget x)
          ((proEtaleConstantRing T A).obj ⋙
            forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj M.val
        obtain ⟨N, a, rfl⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
          (hcR := colimit.isColimit R) (hcM := colimit.isColimit SM.presheaf) z
        change reparamAdditive A x α M
          (r • proEtaleCoefficientModuleGerm x A M N.unop a) =
          r • reparamAdditive A x α M (proEtaleCoefficientModuleGerm x A M N.unop a)
        rw [← coefficientGerm_smul, reparamAdditive_germ, reparamAdditive_germ]
        exact coefficientGerm_smul _ A M
          ((proEtaleStalkNeighbourhoodReparam x α).obj N.unop) r a }

private theorem reparamAdditive_isIso (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
    IsIso (reparamAdditive A x α M) := by
  let i : Over.mk (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) ≅ Over.mk x :=
    Over.isoMk (Scheme.Spec.mapIso α.toCommRingCatIso.op) rfl
  let e := (StructuredArrow.mapIso (T := ProEt.forget T) i).symm
  change IsIso (colimit.pre ((proEtaleGeometricNeighbourhoodForget
    (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).op ⋙ M.val.presheaf) e.functor.op)
  infer_instance


/-- The colimit map of neighbourhood reindexing is a unique A-linear natural
isomorphism. Source: Stacks Tag 05V1
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: each coprojection is sent to the coprojection at its reindexed neighbourhood.
Reindexing preserves pointed arrows, so the colimit universal property supplies the
additive map. Common pointed refinements show compatibility with the constant scalar
action. Reindexing by alpha inverse supplies the inverse. Module maps apply to sections
and commute with reindexing, giving naturality. Coprojections jointly determine maps,
so the displayed formula determines the natural isomorphism uniquely. -/
theorem proEtaleStalkReparam_existsUnique (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    ∃! r : finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A,
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A))
        (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)),
        r.hom.app M (proEtaleCoefficientModuleGerm x A M N a) =
          proEtaleCoefficientModuleGerm _ A M ((proEtaleStalkNeighbourhoodReparam x α).obj N)
            a := by
  let η : finiteCoefficientModuleStalkFunctor x A ⟶
      finiteCoefficientModuleStalkFunctor
        (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A :=
    { app := reparamLinear A x α
      naturality := by
        intro M Q f
        apply (forget₂ (ModuleCat (ULift.{u + 1, u} A)) AddCommGrpCat).map_injective
        apply colimit.hom_ext
        intro N
        ext a
        change reparamAdditive A x α Q
            ((finiteCoefficientModuleStalkFunctor x A).map f
              (proEtaleCoefficientModuleGerm x A M N.unop a)) =
          (finiteCoefficientModuleStalkFunctor _ A).map f
            (reparamAdditive A x α M (proEtaleCoefficientModuleGerm x A M N.unop a))
        have hmap := ConcreteCategory.congr_hom
          (colimit.ι_map (Functor.whiskerLeft
            (proEtaleGeometricNeighbourhoodForget x).op
            ((SheafOfModules.toSheaf _).map f).hom) N) a
        change (finiteCoefficientModuleStalkFunctor x A).map f
          (proEtaleCoefficientModuleGerm x A M N.unop a) =
            proEtaleCoefficientModuleGerm x A Q N.unop (f.val.app (op N.unop.right) a) at hmap
        rw [hmap, reparamAdditive_germ, reparamAdditive_germ]
        exact (ConcreteCategory.congr_hom
          (colimit.ι_map (Functor.whiskerLeft
            (proEtaleGeometricNeighbourhoodForget _).op
            ((SheafOfModules.toSheaf _).map f).hom) (op
              ((proEtaleStalkNeighbourhoodReparam x α).obj N.unop))) a).symm }
  have (M : proEtaleRingModules T (proEtaleConstantRing T A)) : IsIso (η.app M) := by
    have : IsIso ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        AddCommGrpCat.{u + 1}).map (η.app M)) := reparamAdditive_isIso A x α M
    exact isIso_of_reflects_iso _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})
  have : IsIso η := NatIso.isIso_of_isIso_app η
  refine ⟨asIso η, ?_, ?_⟩
  · intro M N a
    exact reparamAdditive_germ x α A M N a
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (forget₂ (ModuleCat (ULift.{u + 1, u} A)) AddCommGrpCat).map_injective
    apply colimit.hom_ext
    intro N
    ext a
    exact (he M N.unop a).trans (reparamAdditive_germ x α A M N.unop a).symm


/-- The map induced by the specified neighbourhood reindexing, uniquely fixed by
its formula on coprojections. Source: Stacks Tag 05V1
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkReparam (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    finiteCoefficientModuleStalkFunctor x A ≅
      finiteCoefficientModuleStalkFunctor (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) A :=
  (proEtaleStalkReparam_existsUnique A x α).exists.choose

private theorem identityCoefficientMap (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleCoefficientDirectImageMap (𝟙 T) A ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv
          CommRingCat.{u + 1} (ProEt.topology T) (ProEt.topology T)).app
            (proEtaleConstantRing T A) = 𝟙 _ := by
  let B := CommRingCat.of (ULift.{u + 1, u} A)
  apply ((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    ((Functor.const T.ProEtᵒᵖ).obj B) _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv _ _
      (((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
        _ _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext V
  have h := (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj B)).naturality
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V.unop).op
  change 𝟙 B ≫ _ = _ at h
  rw [Category.id_comp] at h
  exact h.symm

@[irreducible] private noncomputable def identityDirect (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingPushforward A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)) := by
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)
  have hr : proEtaleRingDirectImageMap (𝟙 T) (proEtaleConstantRing T A)
      (proEtaleConstantRing T A) (proEtaleConstantRingComparison (𝟙 T) A) =
      proEtaleCoefficientDirectImageMap (𝟙 T) A :=
    ((proEtaleSheafAdjunction (𝟙 T) CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  let ρ : R ⟶ ((proEtaleBaseChange (𝟙 T)).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology T) (ProEt.topology T)).obj R :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap (𝟙 T) (proEtaleConstantRing T A)
      (proEtaleConstantRing T A) (proEtaleConstantRingComparison (𝟙 T) A)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hρ : ρ ≫ (Functor.sheafPushforwardContinuousNatTrans
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv RingCat.{u + 1}
      (ProEt.topology T) (ProEt.topology T)).app R = 𝟙 R := by
    dsimp only [ρ]
    rw [hr]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact congrArg (fun q ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (q.hom.app V)) (identityCoefficientMap A T)
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ T)).IsContinuous
      (ProEt.topology T) (ProEt.topology T) :=
    Functor.isContinuous_id _
  change SheafOfModules.pushforward ρ ≅ _
  letI hi : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ T)).IsContinuous
      (ProEt.topology T) (ProEt.topology T) := Functor.isContinuous_id _
  exact SheafOfModules.pushforwardNatIso ρ
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).symm ≪≫
    SheafOfModules.pushforwardCongr hρ ≪≫ SheafOfModules.pushforwardId R


private theorem identityDirect_hom (A : Type u) [CommRing A] (T : Scheme.{u})
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEt)
    (a : ((proEtaleConstantRingPushforward A (𝟙 T)).obj M).val.obj (op V)) :
    ((identityDirect A T).hom.app M).val.app (op V) a =
      M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V).op a := by
  unfold identityDirect
  rfl

/-- The identity-pullback comparison is uniquely fixed by its inverse, the unit
followed by restriction along the diagonal. Source: Stacks Tags 05V1 and 09A5
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: inverse image for the identity is the identity left Kan extension followed by
sheafification. The inverse is its unit restricted along U to U times_T T. The comma
universal property and the sheaf axiom show this is an isomorphism. The coefficient
comparison preserves constants and the tensor unit, so this is A-linear and natural.
The formula fixes its inverse sectionwise and therefore determines the isomorphism. -/
theorem proEtaleStalkIdentityPullback_existsUnique (A : Type u) [CommRing A]
    (T : Scheme.{u}) :
    ∃! e : proEtaleConstantRingPullback A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)),
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEt)
        (a : M.val.obj (op V)),
        (e.inv.app M).val.app (op V) a =
          ((proEtaleConstantRingPullback A (𝟙 T)).obj M).val.map
            ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V).op
            (((proEtaleConstantRingAdjunction A (𝟙 T)).unit.app M).val.app (op V) a) := by
  let adj := (proEtaleConstantRingAdjunction A (𝟙 T)).ofNatIsoRight (identityDirect A T)
  let e := adj.leftAdjointUniq Adjunction.id
  have he (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
      e.inv.app M = adj.unit.app M := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app Adjunction.id adj M
    exact h
  refine ⟨e, ?_, ?_⟩
  · intro M V a
    rw [he]
    change ((identityDirect A T).hom.app _).val.app (op V)
      (((proEtaleConstantRingAdjunction A (𝟙 T)).unit.app M).val.app (op V) a) = _
    exact identityDirect_hom A T _ V _
  · intro e' he'
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext a
    exact (he' M V.unop a).trans (by
      rw [he]
      exact (identityDirect_hom A T _ V.unop _).symm)


/-- The canonical identity-pullback isomorphism with its diagonal-unit normalization.
Source: Stacks Tags 05V1 and 09A5
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkIdentityPullback (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingPullback A (𝟙 T) ≅
      𝟭 (proEtaleRingModules T (proEtaleConstantRing T A)) :=
  (proEtaleStalkIdentityPullback_existsUnique A T).exists.choose


/-- Exactness of the geometric module stalk, needed for ordinary derived localization.
Source: Stacks Tags 0993 and 00Y8
(blueprint: lem-trf-proetale-pullback-stalk-coherence).
Proof: `proEtale_classical_stalk` gives exactness of the abelian stalk. Kernels and
cokernels of module sheaves and modules have the corresponding underlying abelian
groups. The module colimit construction has that abelian stalk, and restriction along
the constant germ changes only the action. Thus both finite limits and finite colimits
are preserved, with no nonzero-ring or nonempty-scheme condition. -/
theorem proEtaleCoefficientStalk_exact (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (finiteCoefficientModuleStalkFunctor x A) ∧
      PreservesFiniteColimits (finiteCoefficientModuleStalkFunctor x A) := by
  let S := sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood x)ᵒᵖ
      T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
      (proEtaleGeometricNeighbourhoodForget x).op ⋙ colim
  obtain ⟨_, _, _, _, _, hlim, hcolim⟩ := proEtale_classical_stalk x
  have : PreservesFiniteLimits S := hlim
  have : PreservesFiniteColimits S := hcolim
  let R : Sheaf (ProEt.topology T) RingCat.{u + 1} :=
    (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{0, 0} U := by
    constructor
    intro J _
    exact ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0}
      (J := J) (ULift.{u + 1, u} A)
  have : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  have : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  have : PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R) :=
    SheafOfModules.preservesFiniteColimits_toSheaf.{u + 1, u, u + 1, u + 1} R
  let e : finiteCoefficientModuleStalkFunctor x A ⋙ U ≅
      SheafOfModules.toSheaf.{u + 1, u, u + 1, u + 1} R ⋙ S :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)
  have : PreservesFiniteColimits U :=
    PreservesColimitsOfSize.preservesFiniteColimits U
  have : PreservesFiniteLimits (finiteCoefficientModuleStalkFunctor x A ⋙ U) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (finiteCoefficientModuleStalkFunctor x A ⋙ U) :=
    preservesFiniteColimits_of_natIso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩


/-- Left exactness from the underlying abelian stalk. Source: Stacks Tag 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable instance proEtaleCoefficientStalk_preservesFiniteLimits
    (A : Type u) [CommRing A] {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    PreservesFiniteLimits (finiteCoefficientModuleStalkFunctor x A) :=
  (proEtaleCoefficientStalk_exact A x).1

/-- Right exactness from the underlying abelian stalk. Source: Stacks Tag 0993
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
noncomputable instance proEtaleCoefficientStalk_preservesFiniteColimits
    (A : Type u) [CommRing A] {T : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    PreservesFiniteColimits (finiteCoefficientModuleStalkFunctor x A) :=
  (proEtaleCoefficientStalk_exact A x).2

/-- The ordinary derived stalk obtained by localizing the termwise stalk functor.
Source: Stacks Tag 0D6D and the localization universal property
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
abbrev proEtaleFiniteCoefficientDerivedStalk (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :=
  (finiteCoefficientModuleStalkFunctor x A).mapDerivedCategory

/-- The normalized comparison descended by the localization universal property.
Source: Stacks Tags 05V1 and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleDerivedPullbackStalkComparison (A : Type u) [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) :
    proEtaleConstantRingDerivedPullback A t ⋙ proEtaleFiniteCoefficientDerivedStalk A x ≅
      proEtaleFiniteCoefficientDerivedStalk A (x ≫ t) :=
  letI : PreservesFiniteLimits
      (proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (proEtaleConstantRingPullback A t ⋙ finiteCoefficientModuleStalkFunctor x A) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A t)
      (finiteCoefficientModuleStalkFunctor x A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (proEtalePullbackStalkComparison A t x)

/-- Neighbourhood reindexing descended to ordinary derived categories.
Source: Stacks Tags 05V1 and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleDerivedStalkReparam (A : Type u) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω) :
    proEtaleFiniteCoefficientDerivedStalk A x ≅
      proEtaleFiniteCoefficientDerivedStalk A (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x) :=
  Functor.mapDerivedCategoryNatIso (proEtaleStalkReparam A x α)

/-- The canonical identity comparison descended termwise, including the localization
identity unitor. Source: Stacks Tag 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def proEtaleStalkDerivedIdentityPullback (A : Type u) [CommRing A] (T : Scheme.{u}) :
    proEtaleConstantRingDerivedPullback A (𝟙 T) ≅ 𝟭 (proEtaleDerivedCategory T A) :=
  Functor.mapDerivedCategoryNatIso (proEtaleStalkIdentityPullback A T) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The precise normalized stalk comparison and its coherence, including the equations
in the ordinary derived category for bounded complexes. Reassociation of point maps
is written explicitly as transport by equality.
Source: Stacks Tags 05V1, 0F4F and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence). -/
def ProEtalePullbackStalkCoherent (A : Type u) [CommRing A] [Finite A] : Prop :=
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T),
    ProEtalePullbackStalkGermNormalized A t x (proEtalePullbackStalkComparison A t x)) ∧
  (∀ {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (N : ProEtaleGeometricNeighbourhood x) (a : M.val.obj (op N.right)),
    (proEtaleStalkReparam A x α).hom.app M (proEtaleCoefficientModuleGerm x A M N a) =
      proEtaleCoefficientModuleGerm _ A M ((proEtaleStalkNeighbourhoodReparam x α).obj N) a) ∧
  (∀ {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (M : proEtaleRingModules T (proEtaleConstantRing T A)),
    (proEtalePullbackStalkComparison A (𝟙 T) x).hom.app M ≫
        eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
          (Category.comp_id x)) =
      (finiteCoefficientModuleStalkFunctor x A).map
        ((proEtaleStalkIdentityPullback A T).hom.app M)) ∧
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (M : proEtaleRingModules S (proEtaleConstantRing S A)),
    (proEtalePullbackStalkComparison A t x).hom.app M ≫
        (proEtaleStalkReparam A (x ≫ t) α).hom.app M =
      (proEtaleStalkReparam A x α).hom.app ((proEtaleConstantRingPullback A t).obj M) ≫
        (proEtalePullbackStalkComparison A t
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).hom.app M ≫
        eqToHom (congrArg (fun w ↦ (finiteCoefficientModuleStalkFunctor w A).obj M)
          (Category.assoc (Spec.map (CommRingCat.ofHom α.toRingHom)) x t))) ∧
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (H : CochainComplex (proEtaleRingModules S (proEtaleConstantRing S A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A t x).hom.app (DerivedCategory.Q.obj H) ≫
        (finiteCoefficientModuleStalkFunctor (x ≫ t) A).mapDerivedCategoryFactors.hom.app H =
      (proEtaleFiniteCoefficientDerivedStalk A x).map
        ((proEtaleConstantRingPullback A t).mapDerivedCategoryFactors.hom.app H) ≫
        (finiteCoefficientModuleStalkFunctor x A).mapDerivedCategoryFactors.hom.app
          (((proEtaleConstantRingPullback A t).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj H) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (proEtalePullbackStalkComparison A t x)
            (ComplexShape.up ℤ)).hom.app H)) ∧
  (∀ {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ Z)
    (H : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A (h ≫ f) v).hom.app
        (DerivedCategory.Q.obj H) =
      (proEtaleFiniteCoefficientDerivedStalk A v).map
        ((proEtaleConstantRingPullbackComposition h f A).inv.app (DerivedCategory.Q.obj H)) ≫
        (proEtaleDerivedPullbackStalkComparison A h v).hom.app
          ((proEtaleConstantRingDerivedPullback A f).obj (DerivedCategory.Q.obj H)) ≫
        (proEtaleDerivedPullbackStalkComparison A f (v ≫ h)).hom.app
          (DerivedCategory.Q.obj H) ≫
        eqToHom (congrArg
          (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H))
          (Category.assoc v h f))) ∧
  (∀ {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T)
    (H : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A (𝟙 T) x).hom.app (DerivedCategory.Q.obj H) ≫
        eqToHom (congrArg
          (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H))
          (Category.comp_id x)) =
      (proEtaleFiniteCoefficientDerivedStalk A x).map
        ((proEtaleStalkDerivedIdentityPullback A T).hom.app (DerivedCategory.Q.obj H))) ∧
  (∀ {T S : Scheme.{u}} (t : T ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ T) (α : Ω ≃+* Ω)
    (H : CochainComplex (proEtaleRingModules S (proEtaleConstantRing S A)) ℤ),
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) →
    (proEtaleDerivedPullbackStalkComparison A t x).hom.app (DerivedCategory.Q.obj H) ≫
        (proEtaleDerivedStalkReparam A (x ≫ t) α).hom.app (DerivedCategory.Q.obj H) =
      (proEtaleDerivedStalkReparam A x α).hom.app
        ((proEtaleConstantRingDerivedPullback A t).obj (DerivedCategory.Q.obj H)) ≫
        (proEtaleDerivedPullbackStalkComparison A t
          (Spec.map (CommRingCat.ofHom α.toRingHom) ≫ x)).hom.app (DerivedCategory.Q.obj H) ≫
        eqToHom (congrArg
          (fun w ↦ (proEtaleFiniteCoefficientDerivedStalk A w).obj (DerivedCategory.Q.obj H))
          (Category.assoc (Spec.map (CommRingCat.ofHom α.toRingHom)) x t)))

/-- Coherence of the canonical finite-coefficient pro-etale pullback--stalk comparison.
Source: Stacks Tags 05V1, 0F4F, 0993 and 0D6D
(blueprint: lem-trf-proetale-pullback-stalk-coherence).

Proof:
1. Apply `proEtaleInverseImage_abelianStalk` to the underlying abelian sheaf of M.
   Before sheafification, a double-colimit representative `(P,theta,a)` maps to
   `[V,pr_V theta x',a]`; the inverse uses the unit on `T times_S V` with paired
   lift `(x,w)`. `proEtaleGeometricStalk_sheafification` identifies this calculation
   with the actual inverse-image stalk. The two restriction relations are preserved;
   the pointed arrow theta identifies the second composite with the identity.
   The specified constant-section coefficient map transports the action without
   changing the underlying abelian sheaf, so the comparison is A-linear. These are
   exactly the two clauses of `ProEtalePullbackStalkGermNormalized`; they fix c uniquely.
2. A module morphism applies only to the section a, and commutes with restrictions,
   proving naturality. For identity pullback, restriction of its unit along the
   diagonal is the inverse of the canonical identity comparison. The germ formulas
   therefore identify c with the stalk of `proEtaleStalkIdentityPullback`, yielding
   the displayed identity equation, rather than an isomorphism cancellation law.
3. For h followed by f the canonical constant-section comparisons agree with the
   composite, since both preserve every constant section. Reassociate the two fibre
   products by their universal property. Both germ computations then give the same
   projected germ. The normalized module adjunctions and termwise K-flat formula in
   `proEtaleCanonicalPullbackComposition` fix chi to precisely this reassociation.
   `proEtaleConstantRingPullbackComposition` transports chi to the constant-ring
   coefficients; its inverse has the direction chi_(h,f) in the displayed equation.
4. `proEtaleStalkNeighbourhoodReparam` precomposes each lift by Spec(alpha) and leaves
   its section unchanged. It preserves pointed arrows; alpha inverse supplies the
   inverse colimit map. Common refinements prove A-linearity. On every germ the two
   paths r after c and c after r have the same section and projected lift. Colimit
   uniqueness proves the module equation, with the written associativity transport.
5. `proEtale_classical_stalk` gives exactness on underlying abelian sheaves; module
   kernels and cokernels are computed there. Pullback is exact by the recorded
   operations. Thus termwise stalk and pullback preserve quasi-isomorphisms. Apply
   steps 1--4 in every degree; naturality makes them chain maps and equalities of
   chain maps. The localization universal property lifts the comparisons and their
   equalities. Its representative equation is the fifth conjunct; its composition,
   identity and reparametrization equations are the last three conjuncts. The
   comparison chi is the recorded normalized derived comparison, so this passage
   introduces no new compositor or choice of representatives. -/
theorem proEtalePullbackStalkCoherence :
    ∀ (A : Type u) [CommRing A] [Finite A],
      ProEtalePullbackStalkCoherent A := by
  sorry

end AlgebraicGeometry.Scheme
