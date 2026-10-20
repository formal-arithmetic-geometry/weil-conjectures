# AlgebraicGeometry.Scheme.Modules.picardTensorFrame_map

## Reason

Complete the retirement item in coord/retire-items.tsv. The adopted source module
WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates already provides
all the coordinate definitions and the complete proof. Its only substantive
textual difference is the unit comparison name: picardTensorFrameUnitIso replaces
picardTensorUnitIsoFrame. Both definitions construct asIso of the same pinned
map tensorPullbackObjUnitToUnit, with the same isomorphism proof. A remote Lean
check proves their equality by rfl.

The sole remaining consumer, Sheaf.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized,
is unclaimed and also has an adopted source twin. After the same unit-name
replacement, its entire text agrees with that twin except for the copyright
header and import root. Re-export that twin rather than keep a second
implementation of the same public theorem. Its statement is unchanged.

## Old

In Sheaf.AlgebraicGeometry.PicardTensorFrameCoordinates:

```lean
/-- The canonical tensor-unit isomorphism, with the pinned adjoint structure map. -/
def picardTensorUnitIsoFrame {X Y : Scheme.{v}} (g : X ⟶ Y) :
    (tensorPullback g).obj (Modules.unit Y) ≅ Modules.unit X := by
  haveI := (tensorPullbackObjUnitToUnit_isIso g).1
  exact asIso (tensorPullbackObjUnitToUnit g)

/-- The tensor pullback of a free sheaf, normalized on each summand by the unit map. -/
def picardTensorFreeIso {X Y : Scheme.{v}} (g : X ⟶ Y) (I : Type v) :
    (tensorPullback g).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I := by
  letI := (Classical.choose (exists_tensorPullbackAdjunction g)).isLeftAdjoint
  exact (SheafOfModules.mapFreeIso (tensorPullback g) I (picardTensorUnitIsoFrame g).symm).symm

/-- Morphisms from the structure sheaf are additive global-section coordinates. -/
def picardUnitHomTopEquiv {X : Scheme.{v}} (M : X.Modules) :
    (Modules.unit X ⟶ M) ≃+ Γ(M, ⊤) where
  toFun f := (SheafOfModules.unitHomEquiv M f).val (.op ⊤)
  invFun x := (SheafOfModules.unitHomEquiv M).symm
    (M.val.sectionsMk
      (fun V ↦ M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op x)
      (fun V W k ↦ by rw [← M.val.map_comp_apply]; congr 1))
  left_inv f := by
    apply (SheafOfModules.unitHomEquiv M).injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    exact PresheafOfModules.sections_property _ _
  right_inv x := by
    dsimp only
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 _) x = x
    simp
  map_add' f g := rfl

/-- Conjugation by two isomorphisms is an additive equivalence of morphism groups. -/
def picardHomCongr {X : Scheme.{v}} {M M' N N' : X.Modules}
    (a : M ≅ M') (b : N ≅ N') : (M ⟶ N) ≃+ (M' ⟶ N') where
  toFun f := a.inv ≫ f ≫ b.hom
  invFun f := a.hom ≫ f ≫ b.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp [Preadditive.comp_add, Preadditive.add_comp]

/-- Coordinates of a raw morphism into the tensor pullback of a rank-one frame. -/
def picardTensorScalarCoordinate {W Y T : Scheme.{v}}
    (t : T ⟶ W) (s : T ⟶ Y) {M : Y.Modules} (q : M ≅ Modules.unit Y) :
    ((tensorPullback t).obj (Modules.unit W) ⟶ (tensorPullback s).obj M) ≃+
      Γ(T, ⊤) :=
  (picardHomCongr (picardTensorUnitIsoFrame t)
    ((tensorPullback s).mapIso q ≪≫ picardTensorUnitIsoFrame s)).trans
      (picardUnitHomTopEquiv (Modules.unit T))

/-- Coordinates of a raw morphism into the tensor pullback of a finite-rank frame. -/
def picardTensorVectorCoordinate {W Y T : Scheme.{v}}
    (t : T ⟶ W) (s : T ⟶ Y) {M : Y.Modules} (m : ℕ)
    (q : M ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{v} (Fin m))) :
    ((tensorPullback t).obj (Modules.unit W) ⟶ (tensorPullback s).obj M) ≃+
      (Fin m → Γ(T, ⊤)) :=
  ((picardHomCongr (picardTensorUnitIsoFrame t)
    ((tensorPullback s).mapIso q ≪≫ picardTensorFreeIso s (ULift.{v} (Fin m)))).trans
      ((picardUnitHomTopEquiv _).trans (freeSectionsEquiv _).toAddEquiv)).trans
        { toFun := fun a i ↦ a ⟨i⟩
          invFun := fun a i ↦ a i.down
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl }

theorem picardTensorFrame_map {W Y T : Scheme.{v}}
    (t : T ⟶ W) (s : T ⟶ Y) {M N : Y.Modules}
    (q0 : M ≅ Modules.unit Y) (m : ℕ)
    (q1 : N ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{v} (Fin m)))
    (δ : M ⟶ N)
    (f : (tensorPullback t).obj (Modules.unit W) ⟶ (tensorPullback s).obj M) :
    picardTensorVectorCoordinate t s m q1 (f ≫ (tensorPullback s).map δ) =
      picardTensorScalarCoordinate t s q0 f •
        (fun i ↦ s.appTop
          (freeSectionsEquiv (ULift.{v} (Fin m))
            (Hom.app (q0.inv ≫ δ ≫ q1.hom) ⊤ (1 : Γ(Y, ⊤))) ⟨i⟩))
```

In Sheaf.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized:

```lean
theorem picardTensorFrame_restriction_normalized (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU :
    w ∈ U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (q :
    (Modules.overEquiv U).functor.obj (K.X 0) ≅ Modules.unit U.toScheme) (V : W.Opens) (hwV : w
    ∈ V) (hVU : V ≤ U) (hs : picardResidueLift W w V hwV ≫ W.homOfLE hVU = picardResidueLift W
    w U hwU) (f : (Modules.tensorPullback V.ι).obj (Modules.unit W) ⟶ (Modules.tensorPullback
    (W.homOfLE hVU)).obj ((Modules.overEquiv U).functor.obj (K.X 0))) :
    Modules.picardTensorScalarCoordinate (W.fromSpecResidueField w) (picardResidueLift W w U
    hwU) q (picardOrdinaryModelRestriction W U K (picardResidueLift W w V hwV) V.ι
    (W.fromSpecResidueField w) (W.homOfLE hVU) (picardResidueLift W w U hwU)
    (picardResidueLift_comp W w V hwV) hs f) = (picardResidueLift W w V hwV).appTop
    (Modules.picardTensorScalarCoordinate V.ι (W.homOfLE hVU) q f)  
```

The latter module publicly imported the duplicate coordinates module and used
picardTensorUnitIsoFrame in its private helpers and theorem proof.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/PicardTensorFrameCoordinates.lean through
deleted.txt. The delivery tool leaves an empty module, and no module imports it.
All coordinate declarations and their complete proof remain at
WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates; no source-library
file is changed. Update the existing frame-map node's lean attachment accordingly.

Replace the unclaimed normalized-restriction consumer with:

```lean
module

public import WeilConjectures.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized

/-! Re-export the adopted proof of normalized tensor-frame restriction. -/

@[expose] public section
```

Update its existing node's lean attachment to the source theorem. The mathematical
statements, proof routes, hypotheses, universes and coordinate formulas stay the
same. No new declaration, arbitrary choice, or proof hole is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardTensorFrameCoordinates | U6 | Withdraw duplicate definitions and proof; reattach its node to the adopted source theorem. |
| Sheaf.AlgebraicGeometry.PicardTensorFrameRestrictionNormalized | unclaimed | Sole current consumer; re-export its adopted twin, removing its import and all uses of the retired unit name. |

The downstream.py --uses searches found only these two modules for
picardTensorUnitIsoFrame. The normalized theorem has no current importers or
other users. PicardTensorFrameRestriction was already retired independently
while this session was reading the repository, and imports no longer need repair.
No downstream module needs an adaptation beyond the consumer above. Both adopted
source modules use source imports only and remain unchanged. Their public
statements have been checked against the former statements by remote compilation;
all six coordinate definitions, the frame-map theorem and normalized-restriction
theorem use only propext, Classical.choice and Quot.sound. The m=0 frame-map
specialization also compiles. The unit construction agrees by rfl, so the
coordinate definitions retain their meaning and target review is not reopened.

## Status

landed 20261020T144307-L-2263053 2026-10-20 (merge of deliver/U6/Sheaf.AlgebraicGeometry.PicardTensorFrameCoordinates)
