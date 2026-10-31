/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VerdierHomChainCompositionData

/-! # Projection and exceptional transpose pasting

Source: current blueprint, fix-prop-coherence.proof.md, adjoint-mate sentence;
proof steps 3--4 of lem-sf-verdier-hom-chain-composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.MonoidalCategory

namespace WeilConjectures.VerdierHomChainComposition
open TensorHomCoefficientTransposes

private theorem exceptional_transpose_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {F' : B ⥤ A} {G' : C ⥤ B} {H' : C ⥤ A}
    (af : F ⊣ F') (ag : G ⊣ G') (ah : H ⊣ H') (e : H ≅ F ⋙ G)
    (U : A) (V : C) (b : U ⟶ F'.obj (G'.obj V)) :
    (ah.homEquiv U V).symm
        (b ≫ (ah.rightAdjointUniq ((af.comp ag).ofNatIsoLeft e.symm)).inv.app V) =
      e.hom.app U ≫ (ag.homEquiv _ V).symm ((af.homEquiv U _).symm b) := by
  let a := (af.comp ag).ofNatIsoLeft e.symm
  have hu : (ah.homEquiv U V).symm
      (b ≫ (ah.rightAdjointUniq a).inv.app V) = (a.homEquiv U V).symm b := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.rightAdjointUniq_inv_app, Adjunction.rightAdjointUniq_hom_app_counit]
  rw [hu, Adjunction.homEquiv_ofNatIsoLeft_symm_apply, Adjunction.comp_homEquiv]
  rfl

private theorem closed_left_uncurry_natural
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (C : CoefficientClosedStructure H) (sym : @SymmetricCategory A _ C.monoidal)
    {P P' T N : A} (a : P' ⟶ P) (v : T ⟶ H.obj (op P, N)) :
    (((C.adjunction P').ofNatIsoLeft
      (@BraidedCategory.tensorLeftIsoTensorRight _ _ C.monoidal
        sym.toBraidedCategory P').symm).homEquiv T N).symm
        (v ≫ H.map (Prod.mkHom a.op (𝟙 N))) =
      (@MonoidalCategory.whiskerRight _ _ C.monoidal.toMonoidalCategoryStruct
        _ _ a T) ≫
        (((C.adjunction P).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ C.monoidal
            sym.toBraidedCategory P).symm).homEquiv T N).symm v := by
  let := C.monoidal
  let := sym
  have h : ((C.adjunction P').homEquiv T N).symm
      (v ≫ H.map (Prod.mkHom a.op (𝟙 N))) =
      (T ◁ a) ≫ ((C.adjunction P).homEquiv T N).symm v := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [C.evaluation_naturality]
    exact (MonoidalCategory.whisker_exchange_assoc v a
      ((C.adjunction P).counit.app N)).symm
  simp only [Adjunction.homEquiv_ofNatIsoLeft_symm_apply, Iso.symm_inv,
    BraidedCategory.tensorLeftIsoTensorRight_hom_app]
  rw [h, ← Category.assoc, ← BraidedCategory.braiding_naturality_left]
  exact Category.assoc _ _ _

variable {D : FiniteFieldDatum.{u}} {B : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic B.l) E]
  [FiniteDimensional (Padic B.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D B E n hn) (s : PodCoefficientStage)

private theorem inverse_tensor_coordinate
    {W : SixFunctorSpace D}
    {C C' : SixFunctorClosedDomain (PodCoefficientStage.domain S s W)
      (PodCoefficientStage.homPairs (S := S) s W)
      (PodCoefficientStage.internalHom (S := S) s W)}
    (h : C = C') (M T N : (PodCoefficientStage.domain S s W).FullSubcategory)
    (v : T ⟶ (sixFunctorDomainHom _ _ _ C.homPermitted C.homDomain).obj (op M, N)) :
    (tensorCoordinate S s h M T).hom ≫
        (((C'.closed.adjunction M).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ C'.closed.monoidal
            C'.symmetric.toBraidedCategory M).symm).homEquiv T N).symm v =
      (((C.closed.adjunction M).ofNatIsoLeft
          (@BraidedCategory.tensorLeftIsoTensorRight _ _ C.closed.monoidal
            C.symmetric.toBraidedCategory M).symm).homEquiv T N).symm v := by
  subst C'
  simp only [tensorCoordinate, eqToIso_refl, Iso.refl_hom, Category.id_comp]

private theorem projection_map {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) (R : Domain S s f c)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Y).FullSubcategory) :
    (PodCoefficientStage.domain S s Y).ι.map (PodCtfPairing.projection S s f c R M T) =
      (R.tensorY (R.support.obj M)).hom.app T ≫
        PodCtfPairing.rawProjection S s f c R M T ≫
        ((PodCoefficientStage.operations S s).support f c).map
          ((R.tensorX M).inv.app (R.pull.obj T)) := by
  simp only [PodCtfPairing.projection, PodCtfPairing.projectionIso,
    Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom]
  cases s <;> rfl

variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
  [QuasiCompact (f ≫ g).hom.left]
  (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
  (cx : Compactification (f ≫ g).hom.left)
  (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)


omit [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
  [QuasiCompact (f ≫ g).hom.left] in
private theorem raw_projection_comp
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Z).FullSubcategory) :
    ((PodCoefficientStage.tensor S s Z).map
        (((PodCoefficientStage.operations S s).composition f g cf cg cx).hom.app M.obj)).app T ≫
      PodCtfPairing.rawProjection S s g cg Rg (Rf.support.obj M) T ≫
      ((PodCoefficientStage.operations S s).support g cg).map
        (PodCtfPairing.rawProjection S s f cf Rf M (Rg.pull.obj T)) =
    PodCtfPairing.rawProjection S s (f ≫ g) cx Rx M T ≫
      ((PodCoefficientStage.operations S s).composition f g cf cg cx).hom.app
        (((PodCoefficientStage.tensor S s X).obj M.obj).obj (Rx.pull.obj T)) ≫
      ((PodCoefficientStage.operations S s).support g cg).map
        (((PodCoefficientStage.operations S s).support f cf).map
          (((PodCoefficientStage.tensor S s X).obj M.obj).map
            ((pullComposition S s f g cf cg cx Rf Rg Rx).hom.app T))) := by
  cases s with
  | finite =>
    exact (compactSupportProjectionFormula S).1.composition f g cf cg cx M.obj
      ⟨T.obj.obj, T.property⟩
  | integral =>
    exact (compactSupportProjectionFormula S).2.1.composition f g cf cg cx M.obj
      T.obj T.property
  | rational =>
    exact (compactSupportProjectionFormula S).2.2.1.composition f g cf cg cx M.obj
      T.obj trivial
  | common =>
    exact (compactSupportProjectionFormula S).2.2.2.1.composition f g cf cg cx M.obj
      T.obj trivial

private theorem projection_comp
    (hX : Rf.closedX = Rx.closedX) (hY : Rf.closedY = Rg.closedX)
    (hZ : Rg.closedY = Rx.closedY)
    (tX : HEq Rf.tensorX Rx.tensorX) (tY : HEq Rf.tensorY Rg.tensorX)
    (tZ : HEq Rg.tensorY Rx.tensorY)
    (nZ : TensorPresentationNatural S s Z Rg.closedY Rg.tensorY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (T : (PodCoefficientStage.domain S s Z).FullSubcategory) :
    (tensorCoordinate S s hZ (Rx.support.obj M) T).hom ≫
      PodCtfPairing.projection S s (f ≫ g) cx Rx M T ≫
      Rx.support.map ((tensorCoordinate S s hX M (Rx.pull.obj T)).inv ≫
        (tensorLeft Rf.closedX.closed.monoidal M).map
          ((pullComposition S s f g cf cg cx Rf Rg Rx).hom.app T)) ≫
      (supportComposition S s f g cf cg cx Rf Rg Rx).hom.app
        ((tensorLeft Rf.closedX.closed.monoidal M).obj (Rf.pull.obj (Rg.pull.obj T))) =
    (@MonoidalCategory.whiskerRight _ _ Rg.closedY.closed.monoidal.toMonoidalCategoryStruct
        _ _ ((supportComposition S s f g cf cg cx Rf Rg Rx).hom.app M) T) ≫
      PodCtfPairing.projection S s g cg Rg (Rf.support.obj M) T ≫
      Rg.support.map ((tensorCoordinate S s hY (Rf.support.obj M) (Rg.pull.obj T)).inv ≫
        PodCtfPairing.projection S s f cf Rf M (Rg.pull.obj T)) := by
  rcases Rf with ⟨pf, df, sf, ef, CX, CY, txf, tyf⟩
  rcases Rg with ⟨pg, dg, sg, eg, CY', CZ, txg, tyg⟩
  rcases Rx with ⟨px, dx, sx, ex, CX', CZ', txx, tyx⟩
  dsimp only at hX hY hZ
  subst CX'
  subst CY'
  subst CZ'
  cases eq_of_heq tX
  cases eq_of_heq tY
  cases eq_of_heq tZ
  simp only [tensorCoordinate, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  let Rf : Domain S s f cf := ⟨pf, df, sf, ef, CX, CY, txf, tyf⟩
  let Rg : Domain S s g cg := ⟨pg, dg, sg, eg, CY, CZ, tyf, tyg⟩
  let Rx : Domain S s (f ≫ g) cx := ⟨px, dx, sx, ex, CX, CZ, txf, tyg⟩
  let i := (PodCoefficientStage.domain S s Z).ι
  let j := (PodCoefficientStage.domain S s X).ι
  let k := (PodCoefficientStage.domain S s Y).ι
  let F := (PodCoefficientStage.operations S s).support f cf
  let G := (PodCoefficientStage.operations S s).support g cg
  let H := (PodCoefficientStage.operations S s).support (f ≫ g) cx
  let e := (PodCoefficientStage.operations S s).composition f g cf cg cx
  let p := (pullComposition S s f g cf cg cx Rf Rg Rx).hom.app T
  let U := (tensorLeft CX.closed.monoidal M).obj (Rf.pull.obj (Rg.pull.obj T))
  let q := (tensorLeft CX.closed.monoidal M).map p
  let z := @MonoidalCategory.whiskerRight _ _ CZ.closed.monoidal.toMonoidalCategoryStruct
    _ _ ((supportComposition S s f g cf cg cx Rf Rg Rx).hom.app M) T
  apply i.map_injective
  change i.map (PodCtfPairing.projection S s (f ≫ g) cx Rx M T) ≫
      H.map (j.map q) ≫ e.hom.app U.obj =
    i.map z ≫ i.map (PodCtfPairing.projection S s g cg Rg (Rf.support.obj M) T) ≫
      G.map (k.map (PodCtfPairing.projection S s f cf Rf M (Rg.pull.obj T)))
  rw [projection_map, projection_map]
  have ht := (txf M).inv.naturality p
  change ((PodCoefficientStage.tensor S s X).obj M.obj).map p ≫
      (txf M).inv.app (Rf.pull.obj (Rg.pull.obj T)) =
    (txf M).inv.app (Rx.pull.obj T) ≫ j.map q at ht
  have hx : H.map ((txf M).inv.app (Rx.pull.obj T)) ≫
      H.map (j.map q) ≫ e.hom.app U.obj =
    e.hom.app (((PodCoefficientStage.tensor S s X).obj M.obj).obj (Rx.pull.obj T)) ≫
      G.map (F.map (((PodCoefficientStage.tensor S s X).obj M.obj).map p)) ≫
      G.map (F.map ((txf M).inv.app (Rf.pull.obj (Rg.pull.obj T)))) := by
    rw [← Category.assoc, ← H.map_comp, ← ht]
    simpa only [F, G, H, U, TensorHomCoefficientTransposes.tensorLeft, Functor.comp_obj,
      ObjectProperty.ι_obj, Functor.comp_map, Functor.map_comp, Category.assoc] using
      e.hom.naturality
        (((PodCoefficientStage.tensor S s X).obj M.obj).map p ≫
          (txf M).inv.app (Rf.pull.obj (Rg.pull.obj T)))
  have hy : G.map ((tyf (Rf.support.obj M)).inv.app (Rg.pull.obj T)) ≫
      G.map (k.map (PodCtfPairing.projection S s f cf Rf M (Rg.pull.obj T))) =
    G.map (PodCtfPairing.rawProjection S s f cf Rf M (Rg.pull.obj T)) ≫
      G.map (F.map ((txf M).inv.app (Rf.pull.obj (Rg.pull.obj T)))) := by
    rw [← G.map_comp, projection_map]
    dsimp only [Rf]
    rw [Iso.inv_hom_id_app_assoc, G.map_comp]
  have hz := nZ (Rx.support.obj M) (Rg.support.obj (Rf.support.obj M)) T
    ((supportComposition S s f g cf cg cx Rf Rg Rx).hom.app M)
  change i.map z ≫ (tyg (Rg.support.obj (Rf.support.obj M))).hom.app T =
    (tyg (Rx.support.obj M)).hom.app T ≫
      ((PodCoefficientStage.tensor S s Z).map (e.hom.app M.obj)).app T at hz
  simp only [Category.assoc]
  rw [hx, hy]
  have hr := congrArg
    (fun a ↦ (tyg (Rx.support.obj M)).hom.app T ≫ a ≫
      G.map (F.map ((txf M).inv.app (Rf.pull.obj (Rg.pull.obj T)))))
    (raw_projection_comp S s f g cf cg cx Rf Rg Rx M T).symm
  have hn := congrArg
    (fun a ↦ a ≫ PodCtfPairing.rawProjection S s g cg Rg (Rf.support.obj M) T ≫
      G.map (PodCtfPairing.rawProjection S s f cf Rf M (Rg.pull.obj T)) ≫
      G.map (F.map ((txf M).inv.app (Rf.pull.obj (Rg.pull.obj T))))) hz
  simp only [Category.assoc] at hr hn
  exact hr.trans hn.symm

omit [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
  [QuasiCompact (f ≫ g).hom.left] in
private theorem curry_target_coordinate
    (hZ : Rg.closedY = Rx.closedY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (v : (tensorLeft Rx.closedY.closed.monoidal (Rx.support.obj M)).obj T ⟶ N) :
    (Rg.tensorAdjunctionY (Rg.support.obj (Rf.support.obj M))).homEquiv T N
        ((@MonoidalCategory.whiskerRight _ _
            Rg.closedY.closed.monoidal.toMonoidalCategoryStruct _ _
            ((supportComposition S s f g cf cg cx Rf Rg Rx).inv.app M) T) ≫
          (tensorCoordinate S s hZ (Rx.support.obj M) T).hom ≫ v) =
      (Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N v ≫
        (targetCoordinate S s f g cf cg cx Rf Rg Rx M N).hom := by
  apply ((Rg.tensorAdjunctionY (Rg.support.obj (Rf.support.obj M))).homEquiv T N).symm.injective
  rw [Equiv.symm_apply_apply]
  have hc := closed_left_uncurry_natural Rg.closedY.closed Rg.closedY.symmetric
    ((supportComposition S s f g cf cg cx Rf Rg Rx).inv.app M)
    ((Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N v)
  have ht := inverse_tensor_coordinate S s hZ (Rx.support.obj M) T N
    ((Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N v)
  change (tensorCoordinate S s hZ (Rx.support.obj M) T).hom ≫
      ((Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N).symm
        ((Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N v) =
    ((Rg.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N).symm
      ((Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N v) at ht
  rw [Equiv.symm_apply_apply] at ht
  exact (congrArg
    (fun a ↦ (@MonoidalCategory.whiskerRight _ _
      Rg.closedY.closed.monoidal.toMonoidalCategoryStruct _ _
      ((supportComposition S s f g cf cg cx Rf Rg Rx).inv.app M) T) ≫ a) ht).trans hc.symm

/-- The upper part of the reverse Hom chain pastes: projection followed by
exceptional inverse transposition and tensor currying. The ordinary adjunctions
and the initial inverse tensor transposes do not occur in this statement.
Source: fix-prop-coherence.proof.md, projection associativity and adjoint-mate sentence
(blueprint: lem-sf-verdier-projection-exceptional-paste).
Proof: identify the shared closed data and tensor comparisons on X,Y,Z. Apply
inverse tensor transposition on Z to the proposed equality. Naturality in the
first tensor variable turns the contravariant Hom coordinate on the right into
precomposition by the support compositor tensored with the identity of T.
Expand inverse exceptional transposition as support(b) followed by its counit.
For the composite, the defining rightAdjointUniq equation for the exceptional
compositor replaces this counit by the pasted f and g counits. Naturality of the
support compositor moves b through it. The projection associativity equation of
compactSupportProjectionFormula replaces the remaining composite projection by
the g projection followed by the g image of the f projection. The supplied
factor naturality moves the tensor comparisons across the support compositor;
their test naturality moves the pullback compositor. All comparison inverses
cancel. This is exactly the left-hand side after uncurrying; injectivity finishes.
At finite coefficients use the finite Laws.composition field, and at integral,
rational and common coefficients use the corresponding higher Laws.composition.
This proof uses actual projection arrows and arbitrary b, including the zero
arrow, and does not identify arrows solely from their finite reductions. -/
theorem projection_exceptional_paste
    (hX : Rf.closedX = Rx.closedX) (hY : Rf.closedY = Rg.closedX)
    (hZ : Rg.closedY = Rx.closedY)
    (tX : HEq Rf.tensorX Rx.tensorX) (tY : HEq Rf.tensorY Rg.tensorX)
    (tZ : HEq Rg.tensorY Rx.tensorY)
    (nX : TensorPresentationNatural S s X Rf.closedX Rf.tensorX)
    (nY : TensorPresentationNatural S s Y Rf.closedY Rf.tensorY)
    (nZ : TensorPresentationNatural S s Z Rg.closedY Rg.tensorY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (b : (tensorLeft Rf.closedX.closed.monoidal M).obj
      (Rf.pull.obj (Rg.pull.obj T)) ⟶ Rf.exceptional.obj (Rg.exceptional.obj N)) :
    (Rg.tensorAdjunctionY (Rg.support.obj (Rf.support.obj M))).homEquiv T N
        (PodCtfPairing.projection S s g cg Rg (Rf.support.obj M) T ≫
          (Rg.exceptionalAdjunction.homEquiv _ N).symm
            ((tensorCoordinate S s hY (Rf.support.obj M) (Rg.pull.obj T)).inv ≫
              PodCtfPairing.projection S s f cf Rf M (Rg.pull.obj T) ≫
              (Rf.exceptionalAdjunction.homEquiv _ _).symm b)) =
      (Rx.tensorAdjunctionY (Rx.support.obj M)).homEquiv T N
          (PodCtfPairing.projection S s (f ≫ g) cx Rx M T ≫
            (Rx.exceptionalAdjunction.homEquiv _ N).symm
              ((tensorCoordinate S s hX M (Rx.pull.obj T)).inv ≫
                (tensorLeft Rf.closedX.closed.monoidal M).map
                  ((pullComposition S s f g cf cg cx Rf Rg Rx).hom.app T) ≫
                b ≫ (exceptionalComposition S s f g cf cg cx Rf Rg Rx).inv.app N)) ≫
        (targetCoordinate S s f g cf cg cx Rf Rg Rx M N).hom := by
  have _ := nX
  have _ := nY
  let e := supportComposition S s f g cf cg cx Rf Rg Rx
  let p := pullComposition S s f g cf cg cx Rf Rg Rx
  let U := (tensorLeft Rf.closedX.closed.monoidal M).obj
    (Rf.pull.obj (Rg.pull.obj T))
  let a := (tensorCoordinate S s hX M (Rx.pull.obj T)).inv ≫
    (tensorLeft Rf.closedX.closed.monoidal M).map (p.hom.app T)
  let c := (tensorCoordinate S s hY (Rf.support.obj M) (Rg.pull.obj T)).inv ≫
    PodCtfPairing.projection S s f cf Rf M (Rg.pull.obj T)
  let d := (Rg.exceptionalAdjunction.homEquiv _ N).symm
    ((Rf.exceptionalAdjunction.homEquiv U _).symm b)
  rw [← curry_target_coordinate S s f g cf cg cx Rf Rg Rx hZ M N T]
  apply congrArg ((Rg.tensorAdjunctionY (Rg.support.obj (Rf.support.obj M))).homEquiv T N)
  have he := exceptional_transpose_comp Rf.exceptionalAdjunction Rg.exceptionalAdjunction
    Rx.exceptionalAdjunction e U N b
  change (Rx.exceptionalAdjunction.homEquiv U N).symm
    (b ≫ (exceptionalComposition S s f g cf cg cx Rf Rg Rx).inv.app N) =
      e.hom.app U ≫ d at he
  have hp := projection_comp S s f g cf cg cx Rf Rg Rx hX hY hZ tX tY tZ nZ M T
  let r := @MonoidalCategory.whiskerRight _ _
    Rg.closedY.closed.monoidal.toMonoidalCategoryStruct _ _ (e.inv.app M) T
  have hh := congrArg (fun k ↦ r ≫ k ≫ d) hp
  have hi : r ≫ (@MonoidalCategory.whiskerRight _ _
      Rg.closedY.closed.monoidal.toMonoidalCategoryStruct _ _ (e.hom.app M) T) = 𝟙 _ := by
    let := Rg.closedY.closed.monoidal
    dsimp only [r]
    rw [← MonoidalCategory.comp_whiskerRight, e.inv_hom_id_app,
      MonoidalCategory.id_whiskerRight]
  have hc := congrArg
    (fun k ↦ k ≫ PodCtfPairing.projection S s g cg Rg (Rf.support.obj M) T ≫
      Rg.support.map c ≫ d) hi
  simp only [Category.assoc] at hh
  simp only [Category.assoc, Category.id_comp] at hc
  have hh' := hh.trans hc
  have hg := Rg.exceptionalAdjunction.homEquiv_naturality_left_symm c
    ((Rf.exceptionalAdjunction.homEquiv U _).symm b)
  have hx := Rx.exceptionalAdjunction.homEquiv_naturality_left_symm a
    (b ≫ (exceptionalComposition S s f g cf cg cx Rf Rg Rx).inv.app N)
  dsimp only [U, Functor.comp_obj] at he hg hx
  have hx' := hx.trans (congrArg (fun k ↦ Rx.support.map a ≫ k) he)
  simp only [a, c, p, Category.assoc] at hg hx'
  rw [hg, hx']
  simpa only [a, c, d, e, p, Category.assoc] using hh'.symm

end WeilConjectures.VerdierHomChainComposition
