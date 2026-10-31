/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleStrictLocalRestriction
import all WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-! # Invertibility of the specified module strict-local germ restriction

Source: Stacks Tags 03Q9 and 03QO. The pointed-section and colimit proofs adapt the
proved abelian arguments of StrictlyHenselianSectionsStalk, InverseImageStalkGerm,
and PointedEtaleSectionConeStalkIso to module-valued sheaves.
(blueprint: new-pur-module-strict-local-restriction-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem module_sections_stalk_isIso
    (A : Type (u + 1)) [CommRing A]
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : s default = IsLocalRing.closedPoint R) :
    (∀ (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of R)))
      ((ModuleCat.{u + 1} A))),
      IsIso ((Scheme.pointSmallEtale s).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of R))))
        (Over.homMk s (Category.comp_id s)) F.obj)) ∧
    (∀ (F G : Sheaf (Scheme.smallEtaleTopology (Spec (.of R)))
      ((ModuleCat.{u + 1} A))) (φ : F ⟶ G),
      (Scheme.pointSmallEtale s).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (Over.homMk s (Category.comp_id s)) F.obj ≫
        (Scheme.pointSmallEtale s).sheafFiber.map φ =
      φ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (Over.homMk s (Category.comp_id s)) G.obj) := by
  let : IsStrictlyHenselianLocalRing R := hR
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale s
  let T := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let t : Φ.fiber.obj T := Over.homMk s (Category.comp_id s)
  have hsec (X : (Spec (.of R)).Etale) (x : Φ.fiber.obj X) :
      ∃ g : T ⟶ X, Φ.fiber.map g t = x := by
    obtain ⟨σ, hσ, hsσ⟩ := Scheme.strictlyHenselianSections_pointedSection hR X.hom x.left s x.w hs
    refine ⟨MorphismProperty.Over.homMk σ hσ, ?_⟩
    apply Over.OverMorphism.ext
    exact hsσ
  constructor
  · intro F
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro a b hab
      obtain ⟨Y, f, y, _, heq⟩ :=
        (Φ.toPresheafFiber_eq_iff' (P := F.obj) T t a b).mp hab
      obtain ⟨g, _⟩ := hsec Y y
      have hgf : g ≫ f = 𝟙 T := by
        apply MorphismProperty.Over.Hom.ext
        have hf' : f.left ≫ T.hom = Y.hom := f.w
        have hg' : g.left ≫ Y.hom = T.hom := g.w
        change g.left ≫ f.left = 𝟙 _
        have hf'' : f.left = Y.hom := by
          change f.left ≫ 𝟙 _ = Y.hom at hf'
          simpa only [Category.comp_id] using hf'
        rw [hf'']
        exact hg'
      have h := congrArg (F.obj.map g.op) heq
      simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
    · intro z
      obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) z
      obtain ⟨g, hg⟩ := hsec X x
      refine ⟨F.obj.map g.op a, ?_⟩
      rw [Φ.toPresheafFiber_w_apply, hg]
  · intro F G φ
    exact Φ.toPresheafFiber_naturality φ.hom T t


private theorem module_inverseImage_stalk_germ
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    ∃ c : Etale.upperStar (ModuleCat.{u + 1} A) f ⋙ (Scheme.pointSmallEtale y).sheafFiber ≅
        (Scheme.pointSmallEtale (y ≫ f)).sheafFiber,
      ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (U : X.Etale)
        (ū : (Scheme.pointSmallEtale (y ≫ f)).fiber.obj U),
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app G).hom.app
              (op U) ≫
            (Scheme.pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
              ((Scheme.pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
              ((Etale.upperStar (ModuleCat.{u + 1} A) f).obj G).obj ≫
            (c.app G).hom =
          (Scheme.pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  refine ⟨Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f y, ?_⟩
  intro G U ū
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv _).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (Scheme.pointSmallEtale y).sheafFiber.map _ =
    (Scheme.pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} A)
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl


private theorem module_pointed_restriction_isIso
    (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {I : Type u} [Category.{u} I]
    {N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements} {g : T ⟶ S}
    (c : PointedEtaleSectionCone g N)
    (y : Spec (.of Ω) ⟶ T) (hbase : y ≫ g = s)
    (hpoint : ∀ i : I, y ≫ (c.section_ i).left ≫
      pullback.fst (N.obj i).1.hom g = (N.obj i).2.left)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hγ : IsIso ((Scheme.pointSmallEtale y).toPresheafFiber
      (Scheme.Etale.mk (𝟙 T)) (Over.homMk y (Category.comp_id y))
      ((upperStar (ModuleCat.{u + 1} A) g).obj F).obj))
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        ((upperStar (ModuleCat.{u + 1} A) g).obj F))
    (hr : ∀ i : I, (Scheme.pointSmallEtale s).toPresheafFiber
      (N.obj i).1 (N.obj i).2 F.obj ≫ r =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app F).hom.app
        (op (N.obj i).1) ≫
      ((upperStar (ModuleCat.{u + 1} A) g).obj F).obj.map (c.section_ i).op ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T)
          (Scheme.Etale.mk (𝟙 T)) Over.mkIdTerminal)).inv.app _) : IsIso r := by
  let P := (upperStar (ModuleCat.{u + 1} A) g).obj F
  let e := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (IsTerminal.isTerminalOfObj (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T)
      (Scheme.Etale.mk (𝟙 T)) Over.mkIdTerminal)
  let γ := (Scheme.pointSmallEtale y).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
    (Over.homMk y (Category.comp_id y)) P.obj
  have : IsIso γ := hγ
  have comparison : ∀ (t : Spec (.of Ω) ⟶ S) (ht : y ≫ g = t),
      ∃ b : (Scheme.pointSmallEtale y).sheafFiber.obj P ≅
          (Scheme.pointSmallEtale t).sheafFiber.obj F,
        ∀ (U : S.Etale) (ū : (Scheme.pointSmallEtale t).fiber.obj U)
          (a : Scheme.Etale.mk (𝟙 T) ⟶ g.Etale.obj U),
          y ≫ a.left ≫ pullback.fst U.hom g = ū.left →
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app F).hom.app
            (op U) ≫ P.obj.map a.op ≫ γ ≫ b.hom =
            (Scheme.pointSmallEtale t).toPresheafFiber U ū F.obj := by
    intro t ht
    subst t
    obtain ⟨b, hb⟩ := module_inverseImage_stalk_germ A g y
    refine ⟨b.app F, ?_⟩
    intro U ū a ha
    have hp : (Scheme.pointSmallEtale y).fiber.map a
        (Over.homMk y (Category.comp_id y)) =
        (Scheme.pointSmallEtaleFiberEtaleIso g y).inv.app U ū := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
        change (y ≫ a.left) ≫ pullback.fst U.hom g = ū.left
        exact ha
      · rw [Scheme.pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
        change (y ≫ a.left) ≫ pullback.snd U.hom g = y
        rw [Category.assoc]
        have hw := a.w
        change a.left ≫ pullback.snd U.hom g = 𝟙 _ at hw
        rw [hw]
        rfl
    dsimp only [γ]
    rw [GrothendieckTopology.Point.toPresheafFiber_w_assoc, hp]
    exact hb F U ū
  obtain ⟨b, hb⟩ := comparison s hbase
  let r₀ := b.inv ≫ inv γ ≫ e.inv.app P
  have hr₀ : ∀ i : I, (Scheme.pointSmallEtale s).toPresheafFiber
      (N.obj i).1 (N.obj i).2 F.obj ≫ r₀ =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app F).hom.app
        (op (N.obj i).1) ≫ P.obj.map (c.section_ i).op ≫ e.inv.app P := by
    intro i
    have h := hb (N.obj i).1 (N.obj i).2 (c.section_ i) (hpoint i)
    change (Scheme.pointSmallEtale s).toPresheafFiber
      (N.obj i).1 (N.obj i).2 F.obj ≫ r₀ =
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app F).hom.app
          (op (N.obj i).1) ≫ P.obj.map (c.section_ i).op ≫ e.inv.app P
    dsimp only [r₀]
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
  have hEq : r = r₀ := by
    have : N.Initial := c.initial
    let hk := (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
    apply hk.hom_ext
    intro i
    exact (hr i.unop).trans (hr₀ i.unop).symm
  rw [hEq]
  dsimp only [r₀]
  infer_instance



private theorem module_restriction_isIso
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ B)
    (F : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso ((moduleStrictLocalRestriction A x).app F) := by
  let r := (moduleStrictLocalRestriction A x).app F
  have hr : ∀ i : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods x),
      (Scheme.pointSmallEtale x).toPresheafFiber
        ((Scheme.AffineEtale.Spec B).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods x)).inverse.obj
            i).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods x)).inverse.obj
          i).2 F.obj ≫ r = moduleStrictLocalSectionRestriction A x F i :=
    fun i => (Classical.choose_spec (moduleStrictLocalRestriction_properties A x).2.2).1 F i
  let : Algebra (B.residueField (x (IsLocalRing.closedPoint Ω))) Ω :=
    (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom.toAlgebra
  obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
    strictHenselizationResidue x rfl
  let := hlocal
  let y := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (B.residueField (x (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing x))))
  have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing x) := by
    rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (B.residueField (x (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing x)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  refine module_pointed_restriction_isIso A (strictLocalSectionCone x) y hbase ?_
    F ((module_sections_stalk_isIso A hstrict y hy).1 _) r hr
  intro i
  let n := (equivSmallModel.{u}
    (Scheme.strictHenselizationNeighbourhoods x)).inverse.obj i
  change y ≫ (strictLocalNeighbourhoodSection x i).left ≫
    pullback.fst ((Scheme.AffineEtale.Spec B).obj n.1).hom
      (Scheme.strictHenselizationStructuralMap x) = n.2.left
  dsimp only [n]
  simp only [strictLocalNeighbourhoodSection,
    MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
  simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint i

/-- The specified module germ restriction and its bounded-below derived comparison
are invertible.
Source: Stacks Tags 03Q9 and 03QO
(blueprint: new-pur-module-strict-local-restriction-is-iso).

Proof: each pointed etale neighbourhood of the closed point of a strictly henselian
local scheme has a section through that point. Thus the terminal-neighbourhood germ
is bijective for module-valued sheaves, by the same colimit argument as for abelian
sheaves. The inverse-image stalk comparison respects the adjunction unit's germs.
Use the compatible sections of the strict-local cone and colimit extensionality to
identify the specified restriction with the inverse of these two stalk isomorphisms.
Every component is invertible, hence the natural transformation is invertible.
Deriving this natural isomorphism preserves invertibility; every other factor of
the defined derived restriction is one of the canonical exact-functor isomorphisms.
-/
theorem moduleStrictLocalRestriction_isIso
    (A : Type (u + 1)) [CommRing A] {B : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) :
    IsIso (moduleStrictLocalRestriction A s) ∧
      IsIso (moduleStrictLocalDerivedRestriction A s) := by
  have : ∀ F, IsIso ((moduleStrictLocalRestriction A s).app F) :=
    fun F => module_restriction_isIso A s F
  have : IsIso (moduleStrictLocalRestriction A s) := NatIso.isIso_of_isIso_app _
  refine ⟨this, ?_⟩
  unfold moduleStrictLocalDerivedRestriction
  infer_instance

end AlgebraicGeometry.Etale
