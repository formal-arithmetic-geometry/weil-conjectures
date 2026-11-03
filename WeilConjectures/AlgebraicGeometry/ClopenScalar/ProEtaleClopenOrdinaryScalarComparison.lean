/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import all WeilConjectures.Algebra.Homology.StrictScalarHom.SliceScalarHomChainAdjunction
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Ordinary clopen scalar comparison

Source: Stacks Project, sites-modules.tex, Tags 03EL, 03CY and 03DH.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] ClopenLocalization.sheafify ClopenLocalization.locallyBijective

open scoped ChangeOfRings
open SheafOfModules.StrictScalarHom
universe a b e f r

section OrdinaryRestriction
variable {C₀ : Type a} [Category.{b} C₀] {D₀ : Type e} [Category.{f} D₀]
  {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
  (F : C₀ ⥤ D₀) [Functor.IsContinuous F J₀ K₀] [F.IsCocontinuous J₀ K₀]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J₀ AddCommGrpCat.{r}]
  [HasWeakSheafify J₀ AddCommGrpCat.{r}]
  [K₀.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify K₀ AddCommGrpCat.{r}]
  [HasWeakSheafify K₀ AddCommGrpCat.{r}]
  [K₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ S₀ : Sheaf K₀ CommRingCat.{r}} (φ₀ : R₀ ⟶ S₀)

private theorem pure_hom_ext
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    {H : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)}
    (f g : changeOfRings φ₀ M ⟶ H)
    (h : ∀ U s x, f.val.app U (pure φ₀ M U s x) =
      g.val.app U (pure φ₀ M U s x)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀) (𝟙 _)).homEquiv _ _
    |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U 1 x

private theorem pure_map
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) (U : D₀ᵒᵖ) (s : S₀.obj.obj U) (x : M.val.obj U) :
    (changeOfRingsHom φ₀ M g).val.app U (pure φ₀ M U s x) =
      pure φ₀ N U s (g.val.app U x) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀) (𝟙 _)).unit.naturality
      ({ app := fun V ↦ (ModuleCat.extendScalars (φ₀.hom.app V).hom).map (g.val.app V)
         naturality := changeOfRingsHom_naturality φ₀ M g } :
        changeOfRingsPresheaf φ₀ M ⟶ changeOfRingsPresheaf φ₀ N)
  exact (congrArg (fun z ↦ z.app U
    (s ⊗ₜ[R₀.obj.obj U, (φ₀.hom.app U).hom] x)) h).symm

private def oldScalarRawIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsPresheaf ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (rawRestriction (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsPresheaf φ₀ M) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro X Y f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (changeOfRingsMap_tmul
      ((pullRing (J₀ := J₀) F).map φ₀) _ f 1 x).trans
      (changeOfRingsMap_tmul φ₀ M (F.op.map f) 1 x).symm)

omit [F.IsCocontinuous J₀ K₀] [HasSheafify J₀ AddCommGrpCat.{r}]
  [HasSheafify K₀ AddCommGrpCat.{r}] in
private theorem oldScalarRawIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
      (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x) =
      s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x := rfl

attribute [local irreducible] oldScalarRawIso

private def oldScalarBackHom
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRings ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ⟶
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRings φ₀ M) :=
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let T := PresheafOfModules.sheafification
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)
  T.map (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
    restrictionSheafify (J₀ := J₀) F A (changeOfRingsPresheaf φ₀ M)

omit [F.IsCocontinuous J₀ K₀] [HasSheafify J₀ AddCommGrpCat.{r}]
  [HasSheafify K₀ AddCommGrpCat.{r}] in
private theorem oldScalarBackHom_eq
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    oldScalarBackHom (J₀ := J₀) F φ₀ M =
      (PresheafOfModules.sheafification
        (R := restrictedRing (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
        (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
        restrictionSheafify (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
          (changeOfRingsPresheaf φ₀ M) := rfl

attribute [local irreducible] oldScalarBackHom

omit [F.IsCocontinuous J₀ K₀] in
private theorem oldScalarBackHom_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (oldScalarBackHom (J₀ := J₀) F φ₀ M).val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      pure φ₀ M (F.op.obj X) s x := by
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let P := changeOfRingsPresheaf φ₀ M
  let Q := changeOfRingsPresheaf ((pullRing (J₀ := J₀) F).map φ₀)
    ((moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M)
  let b := PresheafOfModules.sheafificationAdjunction (R := restrictedRing (J₀ := J₀) F A)
    (𝟙 _)
  have hn := b.unit.naturality (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom
  have hu := restrictionSheafify_unit (J₀ := J₀) (K₀ := K₀) F A P
  have hn' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hn
  change (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf).app X
      ((oldScalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
        (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) = _ at hn'
  rw [oldScalarRawIso_pure] at hn'
  have hu' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hu
  have hn'' := congrArg (fun z ↦ (restrictionSheafify (J₀ := J₀) F A P).val.app X z) hn'
  change (oldScalarBackHom (J₀ := J₀) F φ₀ M).val.app X
      (pure _ _ X s x) = _
  rw [oldScalarBackHom_eq]
  change (restrictionSheafify (J₀ := J₀) F A P).val.app X
    (((PresheafOfModules.sheafification (𝟙 _)).map
      (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom).val.app X
      (pure ((pullRing (J₀ := J₀) F).map φ₀) _ X s x)) = _
  exact hn''.symm.trans hu'

omit [F.IsCocontinuous J₀ K₀] in
private theorem oldScalarBackHom_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHom ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (oldScalarBackHom (J₀ := J₀) F φ₀ N) =
      (oldScalarBackHom (J₀ := J₀) F φ₀ M) ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHom φ₀ M g) := by
  apply pure_hom_ext ((pullRing (J₀ := J₀) F).map φ₀)
    ((moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M)
  intro X s x
  change (oldScalarBackHom (J₀ := J₀) F φ₀ N).val.app X
      ((changeOfRingsHom ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g)).val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x)) =
    (changeOfRingsHom φ₀ M g).val.app (F.op.obj X)
      ((oldScalarBackHom (J₀ := J₀) F φ₀ M).val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x))
  rw [pure_map, oldScalarBackHom_pure, oldScalarBackHom_pure, pure_map]
  rfl

omit [HasSheafify J₀ AddCommGrpCat.{r}] [HasSheafify K₀ AddCommGrpCat.{r}] in
private theorem oldScalarBackHom_isIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    IsIso (oldScalarBackHom (J₀ := J₀) F φ₀ M) := by
  let := restrictionSheafify_isIso (J₀ := J₀) F
    ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
      (changeOfRingsPresheaf φ₀ M)
  change IsIso (oldScalarBackHom (J₀ := J₀) F φ₀ M)
  rw [oldScalarBackHom_eq]
  change IsIso
    ((PresheafOfModules.sheafification
      (R := restrictedRing (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
      (oldScalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
      restrictionSheafify (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
        (changeOfRingsPresheaf φ₀ M))
  infer_instance

private def oldScalarBackIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRings ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRings φ₀ M) := by
  letI := oldScalarBackHom_isIso (J₀ := J₀) F φ₀ M
  exact asIso (oldScalarBackHom (J₀ := J₀) F φ₀ M)

private theorem oldScalarBackIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (oldScalarBackIso (J₀ := J₀) F φ₀ M).hom.val.app X
        (pure ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      pure φ₀ M (F.op.obj X) s x := by
  exact oldScalarBackHom_pure (J₀ := J₀) F φ₀ M X s x

private theorem oldScalarBackIso_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHom ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (oldScalarBackIso (J₀ := J₀) F φ₀ N).hom =
      (oldScalarBackIso (J₀ := J₀) F φ₀ M).hom ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHom φ₀ M g) := by
  exact oldScalarBackHom_natural (J₀ := J₀) F φ₀ g

private def presentedBackComparison
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} X) (q : Presentations.{t, u} Y)
    {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) :
    res j R ⋙ ext (q ((rings j).map a)) ≅ ext (p a) ⋙ res j S := by
  classical
  let : HasWeakSheafify (topology X) AddCommGrpCat.{max u (t + 1)} :=
    (sheafify.{t, u} X).isRightAdjoint
  let : HasWeakSheafify (topology Y) AddCommGrpCat.{max u (t + 1)} :=
    (sheafify.{t, u} Y).isRightAdjoint
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let back {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
      (M : Mods.{t, u} R) :
      ((res j R ⋙ ext (q ((rings j).map a))).obj M) ≅
        ((ext (p a) ⋙ res j S).obj M) :=
    eqToIso ((q ((rings j).map a)).obj_eq ((res j R).obj M)) ≪≫
      oldScalarBackIso (J₀ := topology Y) F a M ≪≫
        (res j S).mapIso (eqToIso ((p a).obj_eq M).symm)
  let c {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) :
      res j R ⋙ ext (q ((rings j).map a)) ≅ ext (p a) ⋙ res j S :=
    NatIso.ofComponents (back a) (by
      intro M N g
      dsimp only [back, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
      let hqM := (q ((rings j).map a)).obj_eq ((res j R).obj M)
      let hqN := (q ((rings j).map a)).obj_eq ((res j R).obj N)
      change (q ((rings j).map a)).ordinary.map ((res j R).map g) ≫
          eqToHom hqN ≫
          (oldScalarBackIso (J₀ := topology Y) F a N).hom ≫
          (res j S).map (eqToHom ((p a).obj_eq N).symm) =
        (eqToHom hqM ≫
          (oldScalarBackIso (J₀ := topology Y) F a M).hom ≫
          (res j S).map (eqToHom ((p a).obj_eq M).symm)) ≫
            (res j S).map ((p a).ordinary.map g)
      rw [(q ((rings j).map a)).map_eq, (p a).map_eq]
      have h := oldScalarBackIso_natural (J₀ := topology Y) F a g
      simp only [Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      simp only [← Functor.map_comp_assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      have ht := congrArg (fun z ↦ eqToHom hqM ≫ z ≫
        (res j S).map (eqToHom ((p a).obj_eq N).symm)) h
      dsimp only [moduleRestrictionF, res, ClopenLocalization.restriction,
        clopenModuleRestriction, pullRing, rings, clopenTensorRings, F] at ht ⊢
      simpa only [Category.assoc] using ht)
  exact c a

/-- Ordinary scalar extension commutes with clopen restriction, preserving pure tensors.
Source: Stacks Project, sites-modules.tex, Tag 03EL, and sites-cohomology.tex, Tag 06YY.
(blueprint: lem-pur-clopen-ordinary-scalar-comparison).

Proof: restrict the sheafification unit of the sectionwise scalar tensor presheaf
along composition with j. This functor is cocontinuous, so it preserves local
bijectivity of that unit. Sectionwise tensor after composition is the same tensor
presheaf over the restricted rings. Both module sheaves are therefore
sheafifications of this one presheaf. Their universal properties give inverse
linear maps, natural in the input module, whose composites are identities by
uniqueness of sheafification. Transport through the object and map equations of
p and q. The defining unit equation gives the displayed pure tensor formula.
This argument includes empty component sites and zero coefficient rings. -/
theorem clopen_ordinary_scalar_comparison
    {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} X) (q : Presentations.{t, u} Y) :
    ∃ c : ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
        ext (p a) ⋙ res j S ≅ res j R ⋙ ext (q ((rings j).map a)),
      ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
        (M : Mods.{t, u} R) (U : Y.ProEtᵒᵖ)
        (s : ((rings j).obj S).obj.obj U) (x : ((res j R).obj M).val.obj U),
        ((c a).hom.app M).val.app U
          (sectionTensor (p a) M
            ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj U) s x) =
          sectionTensor (q ((rings j).map a)) ((res j R).obj M) U s x := by
  classical
  let : HasWeakSheafify (topology X) AddCommGrpCat.{max u (t + 1)} :=
    (sheafify.{t, u} X).isRightAdjoint
  let : HasWeakSheafify (topology Y) AddCommGrpCat.{max u (t + 1)} :=
    (sheafify.{t, u} Y).isRightAdjoint
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  have : F.IsContinuous (topology Y) (topology X) :=
    isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : F.IsCocontinuous (topology Y) (topology X) :=
    isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let c {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S) :=
    presentedBackComparison j @p @q a
  refine ⟨fun a ↦ (c a).symm, ?_⟩
  intro R S a M U s x
  have hb : ((c a).hom.app M).val.app U
      (sectionTensor (q ((rings j).map a)) ((res j R).obj M) U s x) =
        sectionTensor (p a) M (F.op.obj U) s x := by
    dsimp only [c]
    unfold presentedBackComparison
    dsimp only [NatIso.ofComponents_hom_app, Iso.trans_hom,
      Functor.mapIso_hom, eqToIso.hom, sectionTensor]
    let hq := (q ((rings j).map a)).obj_eq ((res j R).obj M)
    have hc := congrArg (fun f ↦ f.val.app U
      (pure ((rings j).map a) ((res j R).obj M) U s x))
        (eqToHom_trans hq.symm hq)
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hc
    change ((res j S).map (eqToHom ((p a).obj_eq M).symm)).val.app U
      ((oldScalarBackIso (J₀ := topology Y) F a M).hom.val.app U
        ((eqToHom hq).val.app U ((eqToHom hq.symm).val.app U
          (pure ((rings j).map a) ((res j R).obj M) U s x)))) = _
    rw [hc]
    exact congrArg (fun z ↦ ((res j S).map
      (eqToHom ((p a).obj_eq M).symm)).val.app U z)
      (oldScalarBackIso_pure (J₀ := topology Y) F a M U s x)
  have hh := congrArg (fun z ↦ ((c a).inv.app M).val.app U z) hb
  have hi := congrArg (fun f ↦ f.val.app U
    (sectionTensor (q ((rings j).map a)) ((res j R).obj M) U s x))
    ((c a).hom_inv_id_app M)
  exact hh.symm.trans hi

attribute [local irreducible] oldScalarBackIso

end OrdinaryRestriction

attribute [local irreducible] changeOfRings changeOfRingsHom changeOfRingsPresheaf
  SheafOfModules.pushforward PresheafOfModules.pushforward


attribute [local semireducible] SheafOfModules.pushforward PresheafOfModules.pushforward

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
