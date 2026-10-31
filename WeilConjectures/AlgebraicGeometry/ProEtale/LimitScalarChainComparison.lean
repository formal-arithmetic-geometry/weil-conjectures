/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.Homotopy

/-! # Inverse-limit coefficient transport and scalar chain comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and the inverse-limit and
termwise chain calculation in the node's proof
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison).

The sectionwise inverse image is the recorded canonical model for an isomorphism.
The index `op n` represents level `m = n + 1` of each inverse system.
Scalar extension uses the existing sheafified balanced tensor with the scalar first.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t r

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CochainPullback

namespace AlgebraicGeometry.Scheme

/-- Transport the module action through the specified ring isomorphism.
Source: Stacks 03EL, coefficient-transport calculation, Step 2
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
def scalarChainTransport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} RX :=
  SheafOfModules.pushforward.{max r (t + 1)} (F := proEtaleIsoPostcompose g)
    (((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).mapIso c).inv)

/-- A local section in the canonical sectionwise model of transported modules.
Its underlying element is unchanged; only its ring action is transported.
Source: Stacks 00WX and 03EL, coefficient-transport calculation, Steps 2--3
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
abbrev scalarChainSection {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((scalarChainTransport g c).obj M).val.obj (op U) :=
  x

/-- The first termwise functor: transport R-modules, then extend scalars on X.
Source: Stacks 03EL, coefficient-transport calculation, Steps 2--4
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
def scalarChainLeft {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (jX : RX ⟶ SX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} SX :=
  scalarChainTransport g cR ⋙ extensionFunctor.{max r (t + 1), t + 1, t} jX

/-- The second termwise functor: extend scalars on Y, then transport S-modules.
Source: Stacks 03EL, coefficient-transport calculation, Steps 2--4
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
def scalarChainRight {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (jY : RY ⟶ SY)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} SX :=
  extensionFunctor.{max r (t + 1), t + 1, t} jY ⋙ scalarChainTransport g cS

/-- The transported action is additive on module maps.
Source: Stacks 03EL (blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
instance scalarChainTransportAdditive {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX) :
    (scalarChainTransport g c).Additive := by
  constructor
  intro M N f h
  ext U x
  rfl

/-- Transport followed by scalar extension is additive.
Source: Stacks 03EL (blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
instance scalarChainLeftAdditive {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (jX : RX ⟶ SX) : (scalarChainLeft g cR jX).Additive := by
  unfold scalarChainLeft
  infer_instance

/-- Scalar extension followed by transport is additive.
Source: Stacks 03EL (blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
instance scalarChainRightAdditive {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (jY : RY ⟶ SY)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX) :
    (scalarChainRight g jY cS).Additive := by
  unfold scalarChainRight
  infer_instance

/-- The two local tensor rules and the transport of all chain homotopies.
Naturality for chain maps and compatibility with differentials are already fields
of the natural isomorphism of complexes b.
Source: Stacks 03EL, coefficient-transport calculation, Steps 2--5
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison). -/
def ScalarChainComparisonRules {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (jX : RX ⟶ SX) (jY : RY ⟶ SY)
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX)
    (b : (scalarChainLeft g cR jX).mapHomologicalComplex (.up ℤ) ≅
      (scalarChainRight g jY cS).mapHomologicalComplex (.up ℤ)) : Prop :=
    (∀ (P : CochainPullback.Complex.{max r (t + 1), t + 1, t} RY) (n : ℤ) (U : X.ProEt)
      (p : (P.X n).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (s : SY.obj.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((b.hom.app P).f n).val.app (op U)
          (extensionTmul jX ((scalarChainTransport g cR).obj (P.X n))
            (op U) (cS.hom.hom.app (op U) s) (scalarChainSection g cR (P.X n) U p)) =
        scalarChainSection g cS ((extensionFunctor jY).obj (P.X n)) U
          (extensionTmul jY (P.X n)
            (op ((proEtaleIsoPostcompose g).obj U)) s p)) ∧
    (∀ (P : CochainPullback.Complex.{max r (t + 1), t + 1, t} RY) (n : ℤ) (U : X.ProEt)
      (p : (P.X n).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (s : SY.obj.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((b.inv.app P).f n).val.app (op U)
          (scalarChainSection g cS ((extensionFunctor jY).obj (P.X n)) U
            (extensionTmul jY (P.X n)
              (op ((proEtaleIsoPostcompose g).obj U)) s p)) =
        extensionTmul jX ((scalarChainTransport g cR).obj (P.X n))
          (op U) (cS.hom.hom.app (op U) s) (scalarChainSection g cR (P.X n) U p)) ∧
    (∀ (P Q : CochainPullback.Complex.{max r (t + 1), t + 1, t} RY)
      (a a' : P ⟶ Q) (h : Homotopy a a'),
      (∀ n k : ℤ,
        ((scalarChainLeft g cR jX).mapHomotopy h).hom n k ≫ (b.hom.app Q).f k =
          (b.hom.app P).f n ≫ ((scalarChainRight g jY cS).mapHomotopy h).hom n k) ∧
      (∀ n k : ℤ,
        ((scalarChainRight g jY cS).mapHomotopy h).hom n k ≫ (b.inv.app Q).f k =
          (b.inv.app P).f n ≫ ((scalarChainLeft g cR jX).mapHomotopy h).hom n k))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance scalarChainLeft_zero {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (jX : RX ⟶ SX) : (scalarChainLeft g cR jX).PreservesZeroMorphisms := by
  infer_instance

private instance scalarChainRight_zero {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (jY : RY ⟶ SY)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX) :
    (scalarChainRight g jY cS).PreservesZeroMorphisms := by
  infer_instance

section AdjointSquare

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  (F : A ⥤ B) (G : C ⥤ D)
  {L : A ⥤ C} {R : C ⥤ A} {L' : B ⥤ D} {R' : D ⥤ B}
  (a : L ⊣ R) (a' : L' ⊣ R') (e : R ⋙ F ≅ G ⋙ R')

private def scalarSquareMap : F ⋙ L' ⟶ L ⋙ G where
  app M := (a'.homEquiv _ _).symm (F.map (a.unit.app M) ≫ e.hom.app (L.obj M))
  naturality {M N} f := by
    apply (a'.homEquiv _ _).injective
    change a'.homEquiv _ _ (L'.map (F.map f) ≫ _) =
      a'.homEquiv _ _ (_ ≫ G.map (L.map f))
    rw [a'.homEquiv_naturality_left, a'.homEquiv_naturality_right]
    erw [(a'.homEquiv (F.obj N) (G.obj (L.obj N))).apply_symm_apply,
      (a'.homEquiv (F.obj M) (G.obj (L.obj M))).apply_symm_apply]
    change F.map f ≫ (F.map (a.unit.app N) ≫ e.hom.app (L.obj N)) =
      (F.map (a.unit.app M) ≫ e.hom.app (L.obj M)) ≫ (G ⋙ R').map (L.map f)
    rw [Category.assoc, ← e.hom.naturality]
    change F.map f ≫ F.map (a.unit.app N) ≫ e.hom.app (L.obj N) =
      F.map (a.unit.app M) ≫ F.map (R.map (L.map f)) ≫ e.hom.app (L.obj N)
    rw [← Category.assoc, ← F.map_comp, ← Category.assoc, ← F.map_comp]
    exact congrArg (fun z ↦ F.map z ≫ e.hom.app (L.obj N)) (a.unit.naturality f)

private theorem scalarSquareMap_unit (M : A) :
    a'.unit.app (F.obj M) ≫ R'.map ((scalarSquareMap F G a a' e).app M) =
      F.map (a.unit.app M) ≫ e.hom.app (L.obj M) := by
  exact (a'.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

variable [F.IsEquivalence] [G.IsEquivalence]

private theorem scalarSquareMap_bijective (M : A) (N : C) :
    Function.Bijective (fun h : G.obj (L.obj M) ⟶ G.obj N ↦
      (scalarSquareMap F G a a' e).app M ≫ h) := by
  let E := ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
    (a.homEquiv M N)).trans
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
        ((Iso.homCongr (Iso.refl (F.obj M)) (e.app N)).trans
          (a'.homEquiv (F.obj M) (G.obj N)).symm))
  have he (h : G.obj (L.obj M) ⟶ G.obj N) :
      (scalarSquareMap F G a a' e).app M ≫ h = E h := by
    apply (a'.homEquiv _ _).injective
    dsimp only [E, Equiv.trans_apply]
    erw [(a'.homEquiv (F.obj M) (G.obj N)).apply_symm_apply]
    change a'.homEquiv _ _ ((scalarSquareMap F G a a' e).app M ≫ h) =
      𝟙 _ ≫ F.map (a.homEquiv M N (G.preimage h)) ≫ e.hom.app N
    rw [Category.id_comp, a'.homEquiv_naturality_right]
    erw [(a'.homEquiv (F.obj M) (G.obj (L.obj M))).apply_symm_apply]
    change (F.map (a.unit.app M) ≫ e.hom.app (L.obj M)) ≫ R'.map h = _
    rw [a.homEquiv_unit, F.map_comp, Category.assoc, Category.assoc]
    change F.map (a.unit.app M) ≫ e.hom.app (L.obj M) ≫ R'.map h =
      F.map (a.unit.app M) ≫ (R ⋙ F).map (G.preimage h) ≫ e.hom.app N
    rw [e.hom.naturality (G.preimage h)]
    simp only [Functor.comp_map, Functor.map_preimage]
  exact (show (fun h ↦ (scalarSquareMap F G a a' e).app M ≫ h) = E from
    funext he) ▸ E.bijective

private def scalarSquareIso : F ⋙ L' ≅ L ⋙ G := by
  let b := scalarSquareMap F G a a' e
  have hb (M : A) : IsIso (b.app M) := by
    apply isIso_of_coyoneda_map_bijective
    intro T
    let i := G.asEquivalence.counitIso.app T
    let E := Iso.homCongr (Iso.refl (G.obj (L.obj M))) i
    let E' := Iso.homCongr (Iso.refl (L'.obj (F.obj M))) i
    have hh : (fun h : G.obj (L.obj M) ⟶ T ↦ b.app M ≫ h) =
        E.symm.trans ((Equiv.ofBijective _
          (scalarSquareMap_bijective F G a a' e M (G.asEquivalence.inverse.obj T))).trans
            E') := by
      funext h
      change b.app M ≫ h = 𝟙 _ ≫
        (b.app M ≫ (𝟙 _ ≫ h ≫ i.inv)) ≫ i.hom
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hh.symm ▸ Equiv.bijective _
  letI : ∀ M, IsIso (b.app M) := hb
  letI : IsIso b := (NatTrans.isIso_iff_isIso_app b).2 hb
  exact asIso b

private theorem scalarSquareIso_hom :
    (scalarSquareIso F G a a' e).hom = scalarSquareMap F G a a' e := rfl

private theorem scalarSquareIso_unit (M : A) :
    a'.unit.app (F.obj M) ≫ R'.map ((scalarSquareIso F G a a' e).hom.app M) =
      F.map (a.unit.app M) ≫ e.hom.app (L.obj M) := by
  rw [scalarSquareIso_hom]
  exact scalarSquareMap_unit F G a a' e M

attribute [local irreducible] scalarSquareIso

end AdjointSquare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The site equivalence is constructed once without unfolding its module adjunction.
private theorem scalarTransport_isEquivalence {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ≅ RX) :
    (SheafOfModules.pushforward.{max r (t + 1)} (F := proEtaleIsoPostcompose g)
      c.inv).IsEquivalence := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max r (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := c.inv
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c.hom
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    have hc := congrArg (fun f ↦ f.hom.app (op (G.obj U.unop))) c.hom_inv_id
    change c.hom.hom.app _ ≫ c.inv.hom.app _ = 𝟙 _ at hc
    change RY.obj.map (E.counit.app U.unop).op =
      (RY.obj.map (E.counit.app U.unop).op ≫
        c.hom.hom.app (op (G.obj U.unop))) ≫ c.inv.hom.app (op (G.obj U.unop))
    rw [Category.assoc, hc]
    exact (Category.comp_id _).symm
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c.hom]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c.hom := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c.hom := congrArg (fun h ↦ φ ≫ h ≫ c.hom) ht
        _ = _ := by
          simp only [Category.id_comp]
          exact c.inv_hom_id
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  have : (SheafOfModules.pushforward.{max r (t + 1)} (F := F) c.inv).IsEquivalence :=
    EM.isEquivalence_functor
  infer_instance

private instance scalarChainTransport_equivalence {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX) :
    (scalarChainTransport g c).IsEquivalence :=
  scalarTransport_isEquivalence.{t, r} g
    (RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).obj RY)
    (RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).obj RX)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).mapIso c)

section ModuleSquare

variable {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
  {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
  (jX : RX ⟶ SX) (jY : RY ⟶ SY)
  (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
  (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX)
  (hsq : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map jY ≫
    cS.hom = cR.hom ≫ jX)

include hsq in
private theorem inverseScalarSquare :
    cR.inv ≫ (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map jY =
      jX ≫ cS.inv := by
  apply (cancel_mono cS.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hsq, Iso.inv_hom_id_assoc]

private def restrictionScalarSquare
    (hsq : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map jY ≫
      cS.hom = cR.hom ≫ jX) :
    restrictionFunctor.{max r (t + 1), t + 1, t} jY ⋙ scalarChainTransport g cR ≅
      scalarChainTransport g cS ⋙ restrictionFunctor.{max r (t + 1), t + 1, t} jX := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
        (m₁ := (((restrictionFunctor.{max r (t + 1), t + 1, t} jY ⋙
          scalarChainTransport g cR).obj M).val.obj U).isModule)
        (m₂ := (((scalarChainTransport g cS ⋙
          restrictionFunctor.{max r (t + 1), t + 1, t} jX).obj M).val.obj U).isModule)
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }) (fun _ _ f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  intro r x
  let y : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) := x
  change (jY.hom.app (op ((proEtaleIsoPostcompose g).obj U.unop))
      (cR.inv.hom.app U r)) • y = cS.inv.hom.app U (jX.hom.app U r) • y
  exact congrArg (fun z ↦ z • y)
    (congrArg (fun f ↦ f.hom.app U r) (inverseScalarSquare g jX jY cR cS hsq))

set_option maxHeartbeats 10000 in
-- Keep the identity-on-sections calculation independent of adjunction elaboration.
private theorem restrictionScalarSquare_hom_apply
    (hsq : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map jY ≫
      cS.hom = cR.hom ≫ jX)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} SY)
    (U : X.ProEtᵒᵖ) (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) :
    ((restrictionScalarSquare g jX jY cR cS hsq).hom.app M).val.app U x = x := by
  rfl

attribute [local irreducible] restrictionScalarSquare

set_option maxHeartbeats 20000 in
-- Keep scalar-square elaboration from unfolding the chosen adjunctions.
private def scalarModuleIso
    (hsq : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map jY ≫
      cS.hom = cR.hom ≫ jX) : scalarChainLeft g cR jX ≅ scalarChainRight g jY cS := by
  exact scalarSquareIso (scalarChainTransport g cR) (scalarChainTransport g cS)
    (extensionAdjunction jY) (extensionAdjunction jX)
      (restrictionScalarSquare g jX jY cR cS hsq)

private theorem scalarModuleIso_unit
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY) :
    (extensionAdjunction jX).unit.app ((scalarChainTransport g cR).obj M) ≫
      (restrictionFunctor jX).map ((scalarModuleIso g jX jY cR cS hsq).hom.app M) =
    (scalarChainTransport g cR).map ((extensionAdjunction jY).unit.app M) ≫
      (restrictionScalarSquare g jX jY cR cS hsq).hom.app ((extensionFunctor jY).obj M) := by
  exact scalarSquareIso_unit _ _ _ _ _ M

attribute [local irreducible] scalarModuleIso
attribute [-instance] scalarChainTransport_equivalence

private theorem transportMap_apply
    {M N : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) :
    ((scalarChainTransport g cR).map f).val.app U x =
      f.val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x := rfl

private theorem restrictionMap_apply
    {M N : CochainPullback.Modules.{max r (t + 1), t + 1, t} SX}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((restrictionFunctor jX).map f).val.app U x = f.val.app U x := rfl

private theorem scalarModuleIso_one
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY) (U : X.ProEt)
    (p : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((scalarModuleIso g jX jY cR cS hsq).hom.app M).val.app (op U)
      (extensionTmul jX ((scalarChainTransport g cR).obj M) (op U) 1 p) =
      extensionTmul jY M (op ((proEtaleIsoPostcompose g).obj U)) 1 p := by
  have h := scalarModuleIso_unit g jX jY cR cS hsq M
  have hh := congrArg (fun f ↦ f.val.app (op U) p) h
  have hx := (Classical.choose_spec (extensionAdjunction_existsUnique jX)).1
    ((scalarChainTransport g cR).obj M) (op U) p
  have hy := (Classical.choose_spec (extensionAdjunction_existsUnique jY)).1
    M (op ((proEtaleIsoPostcompose g).obj U)) p
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hh
  have hh1 := (restrictionMap_apply jX
    ((scalarModuleIso g jX jY cR cS hsq).hom.app M) (op U)
    (((extensionAdjunction jX).unit.app ((scalarChainTransport g cR).obj M)).val.app
      (op U) p)).symm.trans hh
  have hh2 := hh1.trans (restrictionScalarSquare_hom_apply g jX jY cR cS hsq
    ((extensionFunctor jY).obj M) (op U)
    (((scalarChainTransport g cR).map ((extensionAdjunction jY).unit.app M)).val.app
      (op U) p))
  have hh3 := hh2.trans (transportMap_apply g cR
    ((extensionAdjunction jY).unit.app M) (op U) p)
  exact (congrArg
    (((scalarModuleIso g jX jY cR cS hsq).hom.app M).val.app (op U)) hx.symm).trans
      (hh3.trans hy)

open scoped ChangeOfRings in
private theorem extensionTmul_smul {Z : Scheme.{t}}
    {A B : Sheaf (ProEt.topology Z) CommRingCat.{max r (t + 1)}} (j : A ⟶ B)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} A)
    (U : Z.ProEtᵒᵖ) (s : B.obj.obj U) (x : M.val.obj U) :
    extensionTmul j M U s x = s • extensionTmul j M U 1 x := by
  unfold extensionTmul
  erw [← map_smul]
  congr 1
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def moduleAction {R : Type*} [Ring R] (M : ModuleCat R) (s : R) : M → M :=
  @SMul.smul R M M.isModule.toDistribMulAction.toMulAction.toSMul s

private theorem transportSmul_apply
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} SY) (U : X.ProEt)
    (s : SY.obj.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (moduleAction (((scalarChainTransport g cS).obj M).val.obj (op U))
      (cS.hom.hom.app (op U) s)) (scalarChainSection g cS M U x) =
      scalarChainSection g cS M U (s • x) := by
  change (cS.inv.hom.app (op U) (cS.hom.hom.app (op U) s)) • x = s • x
  have hc := congrArg (fun f ↦ f.hom.app (op U) s) cS.hom_inv_id
  exact congrArg (fun z ↦ z • x) hc

private theorem scalarModuleIso_pure
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} RY) (U : X.ProEt)
    (p : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (s : SY.obj.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((scalarModuleIso g jX jY cR cS hsq).hom.app M).val.app (op U)
      (extensionTmul jX ((scalarChainTransport g cR).obj M) (op U)
        (cS.hom.hom.app (op U) s) p) =
      extensionTmul jY M (op ((proEtaleIsoPostcompose g).obj U)) s p := by
  let f := ((scalarModuleIso g jX jY cR cS hsq).hom.app M).val.app (op U)
  have h₁ := congrArg f (extensionTmul_smul jX
    ((scalarChainTransport g cR).obj M) (op U) (cS.hom.hom.app (op U) s) p)
  have h₂ := f.hom.map_smul (cS.hom.hom.app (op U) s)
    (extensionTmul jX ((scalarChainTransport g cR).obj M) (op U) 1 p)
  have h₃ := congrArg
    (moduleAction (((scalarChainRight g jY cS).obj M).val.obj (op U))
      (cS.hom.hom.app (op U) s))
    (scalarModuleIso_one g jX jY cR cS hsq M U p)
  exact h₁.trans (h₂.trans (h₃.trans
    ((transportSmul_apply g cS ((extensionFunctor jY).obj M) U s _).trans
      (extensionTmul_smul jY M (op ((proEtaleIsoPostcompose g).obj U)) s p).symm)))

set_option maxHeartbeats 20000 in
-- Keep the extension adjunction folded during the section calculation.
private theorem extensionHom_ext {Z : Scheme.{t}}
    {A B : Sheaf (ProEt.topology Z) CommRingCat.{max r (t + 1)}} (j : A ⟶ B)
    (M : CochainPullback.Modules.{max r (t + 1), t + 1, t} A)
    {N : CochainPullback.Modules.{max r (t + 1), t + 1, t} B}
    (f h : (extensionFunctor j).obj M ⟶ N)
    (he : ∀ (U : Z.ProEtᵒᵖ) (x : M.val.obj U),
      f.val.app U (extensionTmul j M U 1 x) =
        h.val.app U (extensionTmul j M U 1 x)) : f = h := by
  apply ((extensionAdjunction j).homEquiv M N).injective
  ext U x
  change f.val.app U (((extensionAdjunction j).unit.app M).val.app U x) =
    h.val.app U (((extensionAdjunction j).unit.app M).val.app U x)
  erw [(Classical.choose_spec (extensionAdjunction_existsUnique j)).1 M U x]
  exact he U x


include hsq in
private theorem scalarComplexComparison :
    ∃! b : (scalarChainLeft g cR jX).mapHomologicalComplex (.up ℤ) ≅
        (scalarChainRight g jY cS).mapHomologicalComplex (.up ℤ),
      ScalarChainComparisonRules g jX jY cR cS b := by
  let e := scalarModuleIso g jX jY cR cS hsq
  let b := NatIso.mapHomologicalComplex
    (F := scalarChainLeft g cR jX) (G := scalarChainRight g jY cS) e (.up ℤ)
  have hb : ScalarChainComparisonRules g jX jY cR cS b := by
    refine ⟨?_, ?_, ?_⟩
    · intro P n U p s
      exact scalarModuleIso_pure g jX jY cR cS hsq (P.X n) U p s
    · intro P n U p s
      have hp := scalarModuleIso_pure g jX jY cR cS hsq
        (P.X n) U p s
      have hi := congrArg (fun f ↦ f.val.app (op U)
        (extensionTmul jX ((scalarChainTransport g cR).obj (P.X n))
          (op U) (cS.hom.hom.app (op U) s) p)) (e.app (P.X n)).hom_inv_id
      exact (congrArg (((e.inv.app (P.X n)).val.app (op U))) hp.symm).trans hi
    · intro P Q a a' h
      exact ⟨fun n k ↦ e.hom.naturality (h.hom n k),
        fun n k ↦ e.inv.naturality (h.hom n k)⟩
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro n
  apply extensionHom_ext jX ((scalarChainTransport g cR).obj (P.X n))
  intro U p
  have hh := hb'.1 P n U.unop p 1
  have h := hb.1 P n U.unop p 1
  simp only [map_one] at hh h
  exact hh.trans h.symm

end ModuleSquare

private instance countableRingSheafLimit (Z : Scheme.{t})
    (D : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Z) CommRingCat.{max r (t + 1)}) : HasLimit D := by
  infer_instance

/-- Compatible finite-stage and limit identifications yield the scalar square and
its uniquely pure-tensor-normalized natural isomorphism on unbounded complexes.
The inverse has the reverse rule; the termwise functors transport chain homotopies,
and the comparison intertwines their components in both directions.

Source: Stacks Project, Tag 03EL, with the node's coefficient and chain calculation
(blueprint: lem-weil-isomorphism-limit-scalar-chain-comparison).

Proof: (1) Compose the two candidate limit ring maps with each B_X projection.
Use the projection equations, naturality of i, and the stage coefficient square.
The resulting composites coincide; the limit projections are jointly monic.
(2) On transported module sections define n tensor s to go to
n tensor c_S inverse(s). Balancing follows from the ring square in (1).
The reverse rule uses c_S. Both descend through module sheafification and
are inverse because their composites fix pure tensors.
(3) Compose this transport with the inverse of the inverse-image tensor comparison
(lem-pur-proetale-inverse-image-tensor-comparison). The sectionwise identification
of lem-weil-proetale-isomorphism-inverse-image identifies every local section with
a source section; the formulas therefore determine the sheaf maps uniquely.
(4) Apply the module construction in every integer degree. Naturality for d_P
makes it a chain isomorphism with differential d_P tensor 1; naturality for
arbitrary module maps gives naturality for all chain maps, without boundedness.
(5) Apply the additive termwise functors to a-a' = d h + h d. Their images of h
are homotopies; module naturality for each h component gives both intertwining
identities. No flatness or K-flatness occurs in these constructions. -/
theorem limitScalarChainComparison {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (AX BX : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)})
    (AY BY : ℕᵒᵖ ⥤ Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)})
    (iX : AX ⟶ BX) (iY : AY ⟶ BY)
    (cA : AY ⋙ isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)} ≅ AX)
    (cB : BY ⋙ isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)} ≅ BX)
    (hstage : Functor.whiskerRight iY (isoSectionwiseInverseImage g
      CommRingCat.{max r (t + 1)}) ≫ cB.hom = cA.hom ≫ iX)
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj
      (limit AY) ≅ limit AX)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj
      (limit BY) ≅ limit BX)
    (hR : ∀ m : ℕᵒᵖ, cR.hom ≫ limit.π AX m =
      (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map
        (limit.π AY m) ≫ cA.hom.app m)
    (hS : ∀ m : ℕᵒᵖ, cS.hom ≫ limit.π BX m =
      (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map
        (limit.π BY m) ≫ cB.hom.app m) :
    (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map (limMap iY) ≫
        cS.hom = cR.hom ≫ limMap iX ∧
      ∃! b : (scalarChainLeft g cR (limMap iX)).mapHomologicalComplex (.up ℤ) ≅
          (scalarChainRight g (limMap iY) cS).mapHomologicalComplex (.up ℤ),
        ScalarChainComparisonRules g (limMap iX) (limMap iY) cR cS b := by
  let F := isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}
  have hsq : F.map (limMap iY) ≫ cS.hom = cR.hom ≫ limMap iX := by
    apply limit.hom_ext
    intro m
    rw [Category.assoc, hS, ← Category.assoc, ← F.map_comp, limMap_π,
      F.map_comp, Category.assoc]
    have hm := congrArg (fun f ↦ f.app m) hstage
    change F.map (iY.app m) ≫ cB.hom.app m = cA.hom.app m ≫ iX.app m at hm
    rw [hm, ← Category.assoc, ← hR]
    simp only [Category.assoc, limMap_π]
  exact ⟨hsq, scalarComplexComparison g (limMap iX) (limMap iY) cR cS hsq⟩

end AlgebraicGeometry.Scheme
