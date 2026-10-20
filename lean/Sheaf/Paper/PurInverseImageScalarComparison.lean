/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.PurInverseImageTensorHomDefinitions
import all Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
/-! The normalized scalar-extension comparison. -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s h
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.PurScalar
open SheafOfModules
private abbrev ringSheaf {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev restriction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :=
  SheafOfModules.restrictScalars.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map c)

private theorem tensorRestriction_tmul
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c M).map i
        (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  changeOfRingsMap_tmulOfUniverses.{h, s, u, u} c M i s m

private noncomputable def tensorPresheafFunctor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ PresheafOfModules.{u} (ringSheaf S).obj where
  obj M := changeOfRingsPresheafOfUniverses.{h, s, u, u} c M
  map {M N} f :=
    show changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶
      changeOfRingsPresheafOfUniverses.{h, s, u, u} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturalityOfUniverses.{h, s, u, u} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ SheafOfModules.{u} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val) :
    M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) :
    changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheafOfUniverses.{h, s, u, u} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    {M N : SheafOfModules.{u} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{u} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A))
    {H H' : SheafOfModules.{u} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

@[irreducible] private noncomputable def tensorAdjunction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

attribute [local irreducible] proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (O O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (α : O ⟶ O')
private noncomputable abbrev imageMap :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α
private noncomputable abbrev push (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  T g R

private noncomputable def restrictionSquare :
    restriction.{u + 1, u + 1, u} (K := ProEt.topology X)
        (imageMap g O O' α) ⋙ push g O ≅
      push g O' ⋙ restriction.{u + 1, u + 1, u} (K := ProEt.topology Y) α := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
    · let P := ((restriction.{u + 1, u + 1, u} (K := ProEt.topology X)
          (imageMap g O O' α) ⋙ push g O).obj M).val.obj V
      let Q := ((push g O' ⋙ restriction.{u + 1, u + 1, u}
          (K := ProEt.topology Y) α).obj M).val.obj V
      refine
        { hom := ModuleCat.ofHom (X := P) (Y := Q)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          inv := ModuleCat.ofHom (X := Q) (Y := P)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          hom_inv_id := by ext; rfl
          inv_hom_id := by ext; rfl }
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change (imageMap g O O' α).hom.app ((proEtaleBaseChange g).op.obj V)
            (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O).hom.app V r) • m' =
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app V
            (α.hom.app V r) • m'
        congr 1
        exact (congrArg (fun k ↦ k.hom.app V (show O.obj.obj V from r))
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality α)).symm
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app V
            (α.hom.app V r) • m' =
          (imageMap g O O' α).hom.app ((proEtaleBaseChange g).op.obj V)
            (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O).hom.app V r) • m'
        congr 1
        exact congrArg (fun k ↦ k.hom.app V (show O.obj.obj V from r))
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality α)
    · intro V W i
      ext m
      rfl
  · intro M N f
    ext V m
    rfl

private noncomputable def scalarIso :
    tensorFunctor.{u + 1, u + 1, u} (K := ProEt.topology Y) α ⋙
        proEtaleModuleInverseImage g O' ≅
      proEtaleModuleInverseImage g O ⋙
        tensorFunctor.{u + 1, u + 1, u} (K := ProEt.topology X) (imageMap g O O' α) :=
  ((tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology Y) α).comp
    (canonicalAdjunction g O')).leftAdjointUniq
    (((canonicalAdjunction g O).comp
      (tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology X)
        (imageMap g O O' α))).ofNatIsoRight
      (restrictionSquare g O O' α))

private theorem tensorUnit_section {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf.{u + 1, u + 1, u} R)) (V : Z.ProEt)
    (m : M.val.obj (op V)) :
    ((tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology Z) c).unit.app M).val.app
        (op V) m = purScalarSection R S c M V 1 m := by
  unfold tensorAdjunction
  rfl

private theorem scalarIso_one
    (M : SheafOfModules.{u + 1} (ringSheaf.{u + 1, u + 1, u} O)) (V : Y.ProEt)
    (m : M.val.obj (op V)) :
    ((scalarIso g O O' α).hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (purInverseImageSection g O' _ V (purScalarSection O O' α M V 1 m)) =
    purScalarSection _ _ (imageMap g O O' α) ((proEtaleModuleInverseImage g O).obj M)
      ((proEtaleBaseChange g).obj V) 1 (purInverseImageSection g O M V m) := by
  let a := tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology Y) α
  let b := canonicalAdjunction g O'
  let c := canonicalAdjunction g O
  let d := tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology X)
    (imageMap g O O' α)
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b)
    ((c.comp d).ofNatIsoRight (restrictionSquare g O O' α)) M
  rw [Adjunction.comp_unit_app] at h
  have he := congrArg (fun k ↦ k.val.app (op V) m) h
  change ((scalarIso g O O' α).hom.app M).val.app
    (op ((proEtaleBaseChange g).obj V))
    ((b.unit.app ((tensorFunctor.{u + 1, u + 1, u}
      (K := ProEt.topology Y) α).obj M)).val.app (op V)
      ((a.unit.app M).val.app (op V) m)) = _ at he
  rw [show a = tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology Y) α from rfl,
    tensorUnit_section] at he
  rw [canonicalUnit_sections] at he
  refine he.trans ?_
  change ((d.unit.app ((proEtaleModuleInverseImage g O).obj M)).val.app
    (op ((proEtaleBaseChange g).obj V)) ((c.unit.app M).val.app (op V) m)) = _
  rw [show c = canonicalAdjunction g O from rfl, canonicalUnit_sections]
  exact tensorUnit_section (imageMap g O O' α)
    ((proEtaleModuleInverseImage g O).obj M) ((proEtaleBaseChange g).obj V)
    (purInverseImageSection g O M V m)


private noncomputable def scalarSectionLinear {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (V : Z.ProEt) :
    (ModuleCat.extendScalars (c.hom.app (op V)).hom).obj (M.val.obj (op V)) ⟶
      (changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).unit.app
    (changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M)).app (op V) ≫
      (ModuleCat.restrictScalarsId (S.obj.obj (op V))).hom.app _

private theorem scalarSectionLinear_apply {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (V : Z.ProEt)
    (b : S.obj.obj (op V)) (m : M.val.obj (op V)) :
    scalarSectionLinear c M V
      (b ⊗ₜ[R.obj.obj (op V), (c.hom.app (op V)).hom] m) =
      purScalarSection R S c M V b m := by rfl

attribute [local irreducible] SheafOfModules.changeOfRingsOfUniverses


private theorem scalarSection_one {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (V : Z.ProEt)
    (b : S.obj.obj (op V)) (m : M.val.obj (op V)) :
    @Eq (ModuleCat.carrier
      ((changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M).val.obj (op V)))
      (purScalarSection R S c M V b m) (@SMul.smul (S.obj.obj (op V))
        ((changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M).val.obj (op V))
        inferInstance b (purScalarSection R S c M V 1 m)) := by
  rw [← scalarSectionLinear_apply, ← scalarSectionLinear_apply]
  have ht : b ⊗ₜ[R.obj.obj (op V), (c.hom.app (op V)).hom] m =
      b • ((1 : S.obj.obj (op V)) ⊗ₜ[R.obj.obj (op V), (c.hom.app (op V)).hom] m) := by
    change b ⊗ₜ[R.obj.obj (op V), (c.hom.app (op V)).hom] m =
      (b * 1) ⊗ₜ[R.obj.obj (op V), (c.hom.app (op V)).hom] m
    rw [mul_one]
  rw [ht]
  exact (scalarSectionLinear c M V).hom.map_smul b _

private theorem inverseSection_smul
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O')) (V : Y.ProEt)
    (b : O'.obj.obj (op V)) (m : M.val.obj (op V)) :
    @Eq (ModuleCat.carrier (((proEtaleModuleInverseImage g O').obj M).val.obj
      (op ((proEtaleBaseChange g).obj V))))
      (purInverseImageSection g O' M V
        (@SMul.smul (O'.obj.obj (op V)) (M.val.obj (op V)) inferInstance b m))
      (@SMul.smul
        (((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O').obj.obj
          (op ((proEtaleBaseChange g).obj V)))
        (((proEtaleModuleInverseImage g O').obj M).val.obj
          (op ((proEtaleBaseChange g).obj V))) inferInstance
        ((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app
          (op V)) b) (purInverseImageSection g O' M V m)) := by
  have h := (((canonicalAdjunction g O').unit.app M).val.app (op V)).hom.map_smul b m
  rw [canonicalUnit_sections, canonicalUnit_sections] at h
  exact h

attribute [local semireducible] SheafOfModules.changeOfRingsOfUniverses
  proEtaleModuleInverseImage

end AlgebraicGeometry.Scheme.PurScalar
namespace AlgebraicGeometry.Scheme

/-- The normalized scalar-extension comparison.
Source: Stacks Project, `sites-modules.tex`, Tags 03EK and 03EL
(blueprint: lem-pur-inverse-image-scalar-comparison).
Proof: use the inverse site equivalence to express module inverse image as
reindexing with transported scalar action. The presheaf scalar extension at U is
O'(U) tensor over O(U) with F(U), and reindexing preserves this formula and its
restriction maps. Commute reindexing with module sheafification using its universal
property, now over the reindexed O'. This gives the desired O'-linear isomorphism.
Its formula follows on pure scalar tensors from compatibility with sheafification
maps and with the ring and module adjunction units. No flatness or nonzero-ring
hypothesis is needed: this is transport by an equivalence. -/
theorem purInverseImageScalarComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
        (∀ (O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
            (α : O ⟶ O')
            (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)),
          ∃ e : (proEtaleModuleInverseImage g O').obj
              (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α F) ≅
            inverseImageScalarExtension g O O' α F,
            ∀ (V : Y.ProEt) (b : O'.obj.obj (op V)) (s : F.val.obj (op V)),
              e.hom.val.app (op ((proEtaleBaseChange g).obj V))
                (purInverseImageSection g O' _ V (purScalarSection O O' α F V b s)) =
              purScalarSection
                ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O)
                ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O')
                ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α)
                ((proEtaleModuleInverseImage g O).obj F) ((proEtaleBaseChange g).obj V)
                (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app
                  (op V) b) (purInverseImageSection g O F V s)) := by
  intro O' α F
  let e : (proEtaleModuleInverseImage g O').obj
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α F) ≅
        inverseImageScalarExtension g O O' α F := (PurScalar.scalarIso g O O' α).app F
  refine ⟨e, ?_⟩
  intro V b s
  rw [PurScalar.scalarSection_one, PurScalar.inverseSection_smul]
  have he := (e.hom.val.app (op ((proEtaleBaseChange g).obj V))).hom.map_smul
    ((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app (op V)) b)
    (purInverseImageSection g O' _ V (purScalarSection O O' α F V 1 s))
  refine he.trans ?_
  refine (congrArg (fun z ↦
    ((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app (op V)) b) • z)
      (PurScalar.scalarIso_one g O O' α F V s)).trans ?_
  exact (PurScalar.scalarSection_one
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α)
    ((proEtaleModuleInverseImage g O).obj F) ((proEtaleBaseChange g).obj V) _
    (purInverseImageSection g O F V s)).symm

end AlgebraicGeometry.Scheme
