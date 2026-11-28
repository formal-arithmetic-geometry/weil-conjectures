/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemScalarCoreData

/-! # Proper/open compatibility of the normalized selected scalar comparison

The normalized selected comparison intertwines the left scalar mates.

## Implementation details

Both coefficient paths from the completed coefficients over `E` to the finite level over `L`
factor through their common composite change. Through the faithful full inclusion,
`selected_balanced` identifies the selected comparison with the two scalar associators of
this composite. The compatibility on reconstructed objects then follows from the
reconstruction, evaluation and cocycle squares, by an abstract diagram chase
(`selectedLeftCompat_of_cocycles`). Every normalized sequence is isomorphic to a
reconstructed one, so naturality gives the equality on all objects.

## References

* [Zheng, Lemma 5.22 and Proposition 5.26]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

-- The categorical core: the selected square follows from the reduction, evaluation and
-- cocycle squares once the selected comparison is identified with the two associators.
private theorem selectedLeftCompat_of_cocycles
    {CiEX CiEY CiLX CiLY SEX SEY SLX SLY CfEX CfEY CfLX CfLY : Type*}
    [Category CiEX] [Category CiEY] [Category CiLX] [Category CiLY]
    [Category SEX] [Category SEY] [Category SLX] [Category SLY]
    [Category CfEX] [Category CfEY] [Category CfLX] [Category CfLY]
    (ρEX : CiEX ⥤ SEX) (ρEY : CiEY ⥤ SEY) (ρLX : CiLX ⥤ SLX) (ρLY : CiLY ⥤ SLY)
    [ρEX.EssSurj]
    (evEX : SEX ⥤ CfEX) (evEY : SEY ⥤ CfEY) (evLX : SLX ⥤ CfLX) (evLY : SLY ⥤ CfLY)
    (σX : SEX ⥤ SLX) (σY : SEY ⥤ SLY) (FE : SEX ⥤ SEY) (FL : SLX ⥤ SLY)
    (IE : CiEX ⥤ CiEY) (IL : CiLX ⥤ CiLY) (PE : CfEX ⥤ CfEY) (PL : CfLX ⥤ CfLY)
    (ScX : CiEX ⥤ CiLX) (ScY : CiEY ⥤ CiLY)
    (REX : CiEX ⥤ CfEX) (REY : CiEY ⥤ CfEY) (RLX : CiLX ⥤ CfLX) (RLY : CiLY ⥤ CfLY)
    (ZX : CfEX ⥤ CfLX) (ZY : CfEY ⥤ CfLY) (DX : CiEX ⥤ CfLX) (DY : CiEY ⥤ CfLY)
    (redX : ScX ⋙ ρLX ≅ ρEX ⋙ σX) (redY : ScY ⋙ ρLY ≅ ρEY ⋙ σY)
    (εEX : REX ≅ ρEX ⋙ evEX) (εEY : REY ≅ ρEY ⋙ evEY)
    (εLX : RLX ≅ ρLX ⋙ evLX) (εLY : RLY ≅ ρLY ⋙ evLY)
    (selX : σX ⋙ evLX ≅ evEX ⋙ ZX) (selY : σY ⋙ evLY ≅ evEY ⋙ ZY)
    (cq : FE ⋙ σY ≅ σX ⋙ FL)
    (rFE : IE ⋙ ρEY ≅ ρEX ⋙ FE) (rFL : IL ⋙ ρLY ≅ ρLX ⋙ FL)
    (evFE : FE ⋙ evEY ≅ evEX ⋙ PE) (evFL : FL ⋙ evLY ≅ evLX ⋙ PL)
    (qc : IE ⋙ ScY ≅ ScX ⋙ IL) (qRE : IE ⋙ REY ≅ REX ⋙ PE)
    (qRL : IL ⋙ RLY ≅ RLX ⋙ PL)
    (qZ : PE ⋙ ZY ≅ ZX ⋙ PL) (qD : IE ⋙ DY ≅ DX ⋙ PL)
    (α1X : ScX ⋙ RLX ≅ DX) (α1Y : ScY ⋙ RLY ≅ DY)
    (α2X : REX ⋙ ZX ≅ DX) (α2Y : REY ⋙ ZY ≅ DY)
    (hq : ∀ K, ρLY.map (qc.hom.app K) ≫ rFL.hom.app (ScX.obj K) ≫ FL.map (redX.hom.app K) =
      redY.hom.app (IE.obj K) ≫ σY.map (rFE.hom.app K) ≫ cq.hom.app (ρEX.obj K))
    (hE : ∀ K, qRE.hom.app K ≫ PE.map (εEX.hom.app K) =
      εEY.hom.app (IE.obj K) ≫ evEY.map (rFE.hom.app K) ≫ evFE.hom.app (ρEX.obj K))
    (hL : ∀ K, qRL.hom.app K ≫ PL.map (εLX.hom.app K) =
      εLY.hom.app (IL.obj K) ≫ evLY.map (rFL.hom.app K) ≫ evFL.hom.app (ρLX.obj K))
    (h1 : ∀ K, RLY.map (qc.hom.app K) ≫ qRL.hom.app (ScX.obj K) ≫ PL.map (α1X.hom.app K) =
      α1Y.hom.app (IE.obj K) ≫ qD.hom.app K)
    (h2 : ∀ K, ZY.map (qRE.hom.app K) ≫ qZ.hom.app (REX.obj K) ≫ PL.map (α2X.hom.app K) =
      α2Y.hom.app (IE.obj K) ≫ qD.hom.app K)
    (bX : ∀ K, εLX.hom.app (ScX.obj K) ≫ evLX.map (redX.hom.app K) ≫
      selX.hom.app (ρEX.obj K) ≫ ZX.map (εEX.inv.app K) = α1X.hom.app K ≫ α2X.inv.app K)
    (bY : ∀ K, εLY.hom.app (ScY.obj K) ≫ evLY.map (redY.hom.app K) ≫
      selY.hom.app (ρEY.obj K) ≫ ZY.map (εEY.inv.app K) = α1Y.hom.app K ≫ α2Y.inv.app K)
    (N : SEX) :
    evLY.map (cq.hom.app N) ≫ evFL.hom.app (σX.obj N) ≫ PL.map (selX.hom.app N) =
      selY.hom.app (FE.obj N) ≫ ZY.map (evFE.hom.app N) ≫ qZ.hom.app (evEX.obj N) := by
  -- both sides are natural in `N`, so it suffices to treat `N = ρEX.obj K`
  suffices H : ∀ K, evLY.map (cq.hom.app (ρEX.obj K)) ≫ evFL.hom.app (σX.obj (ρEX.obj K)) ≫
      PL.map (selX.hom.app (ρEX.obj K)) = selY.hom.app (FE.obj (ρEX.obj K)) ≫
        ZY.map (evFE.hom.app (ρEX.obj K)) ≫ qZ.hom.app (evEX.obj (ρEX.obj K)) by
    let e := ρEX.objObjPreimageIso N
    have nat : ∀ {N' N : SEX} (f : N' ⟶ N),
        (evLY.map (cq.hom.app N') ≫ evFL.hom.app (σX.obj N') ≫ PL.map (selX.hom.app N')) ≫
          PL.map (ZX.map (evEX.map f)) =
        evLY.map (σY.map (FE.map f)) ≫
          (evLY.map (cq.hom.app N) ≫ evFL.hom.app (σX.obj N) ≫ PL.map (selX.hom.app N)) ∧
        (selY.hom.app (FE.obj N') ≫ ZY.map (evFE.hom.app N') ≫ qZ.hom.app (evEX.obj N')) ≫
          PL.map (ZX.map (evEX.map f)) =
        evLY.map (σY.map (FE.map f)) ≫
          (selY.hom.app (FE.obj N) ≫ ZY.map (evFE.hom.app N) ≫ qZ.hom.app (evEX.obj N)) := by
      intro N' N f
      have n1 := selX.hom.naturality f
      have n2 := evFL.hom.naturality (σX.map f)
      have n3 := cq.hom.naturality f
      have n4 := selY.hom.naturality (FE.map f)
      have n5 := evFE.hom.naturality f
      have n6 := qZ.hom.naturality (evEX.map f)
      simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4 n5 n6
      constructor
      · rw [Category.assoc, Category.assoc, ← PL.map_comp, ← n1, PL.map_comp,
          ← Category.assoc (evFL.hom.app _), ← n2]
        simp only [Category.assoc]
        rw [← evLY.map_comp_assoc, ← n3, evLY.map_comp_assoc]
      · rw [Category.assoc, Category.assoc, ← n6, ← Category.assoc (ZY.map _),
          ← ZY.map_comp, ← n5, ZY.map_comp]
        simp only [Category.assoc]
        rw [← reassoc_of% n4]
    rw [← cancel_epi (evLY.map (σY.map (FE.map e.hom))), ← (nat e.hom).1, ← (nat e.hom).2,
      H]
  intro K
  have bX' : evLX.map (redX.hom.app K) ≫ selX.hom.app (ρEX.obj K) =
      εLX.inv.app (ScX.obj K) ≫ α1X.hom.app K ≫ α2X.inv.app K ≫
        ZX.map (εEX.hom.app K) := by
    rw [← reassoc_of% (bX K)]
    simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc, ← ZX.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have bY' : εLY.inv.app (ScY.obj (IE.obj K)) ≫ α1Y.hom.app (IE.obj K) ≫
      α2Y.inv.app (IE.obj K) = evLY.map (redY.hom.app (IE.obj K)) ≫
        selY.hom.app (ρEY.obj (IE.obj K)) ≫ ZY.map (εEY.inv.app (IE.obj K)) := by
    rw [← bY (IE.obj K)]
    simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]
  have hL' : evLY.map (rFL.hom.app (ScX.obj K)) ≫ evFL.hom.app (ρLX.obj (ScX.obj K)) ≫
      PL.map (εLX.inv.app (ScX.obj K)) =
      εLY.inv.app (IL.obj (ScX.obj K)) ≫ qRL.hom.app (ScX.obj K) := by
    rw [← cancel_mono (PL.map (εLX.hom.app (ScX.obj K)))]
    simp only [Category.assoc]
    rw [hL]
    simp only [Functor.comp_obj, ← PL.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_app_assoc]
  have h2' : qD.hom.app K ≫ PL.map (α2X.inv.app K) =
      α2Y.inv.app (IE.obj K) ≫ ZY.map (qRE.hom.app K) ≫ qZ.hom.app (REX.obj K) := by
    rw [← cancel_epi (α2Y.hom.app (IE.obj K)), ← reassoc_of% (h2 K)]
    simp only [Functor.comp_obj, ← PL.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Iso.hom_inv_id_app_assoc]
  have nF := evFL.hom.naturality (redX.hom.app K)
  have nε := εLY.inv.naturality (qc.hom.app K)
  have nZ := qZ.hom.naturality (εEX.hom.app K)
  have nS := selY.hom.naturality (rFE.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at nF nε nZ nS
  rw [← cancel_epi (evLY.map (redY.hom.app (IE.obj K) ≫ σY.map (rFE.hom.app K)))]
  calc evLY.map (redY.hom.app (IE.obj K) ≫ σY.map (rFE.hom.app K)) ≫
        evLY.map (cq.hom.app (ρEX.obj K)) ≫ evFL.hom.app (σX.obj (ρEX.obj K)) ≫
          PL.map (selX.hom.app (ρEX.obj K))
      = evLY.map (ρLY.map (qc.hom.app K)) ≫
          (evLY.map (rFL.hom.app (ScX.obj K)) ≫ evFL.hom.app (ρLX.obj (ScX.obj K)) ≫
            PL.map (εLX.inv.app (ScX.obj K))) ≫
          PL.map (α1X.hom.app K ≫ α2X.inv.app K ≫ ZX.map (εEX.hom.app K)) := by
        rw [← evLY.map_comp_assoc, Category.assoc, ← hq K]
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% nF, ← PL.map_comp, bX']
        simp only [Functor.map_comp]
    _ = εLY.inv.app (ScY.obj (IE.obj K)) ≫
          (RLY.map (qc.hom.app K) ≫ qRL.hom.app (ScX.obj K) ≫ PL.map (α1X.hom.app K)) ≫
          PL.map (α2X.inv.app K) ≫ PL.map (ZX.map (εEX.hom.app K)) := by
        rw [hL']
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% nε]
    _ = (εLY.inv.app (ScY.obj (IE.obj K)) ≫ α1Y.hom.app (IE.obj K) ≫
          α2Y.inv.app (IE.obj K)) ≫ ZY.map (qRE.hom.app K) ≫ qZ.hom.app (REX.obj K) ≫
          PL.map (ZX.map (εEX.hom.app K)) := by
        rw [h1 K]
        simp only [Category.assoc]
        rw [reassoc_of% h2']
    _ = evLY.map (redY.hom.app (IE.obj K)) ≫ selY.hom.app (ρEY.obj (IE.obj K)) ≫
          ZY.map (εEY.inv.app (IE.obj K) ≫ qRE.hom.app K ≫ PE.map (εEX.hom.app K)) ≫
          qZ.hom.app (evEX.obj (ρEX.obj K)) := by
        rw [bY', ← nZ]
        simp only [Functor.map_comp, Category.assoc]
    _ = evLY.map (redY.hom.app (IE.obj K) ≫ σY.map (rFE.hom.app K)) ≫
          selY.hom.app (FE.obj (ρEX.obj K)) ≫ ZY.map (evFE.hom.app (ρEX.obj K)) ≫
          qZ.hom.app (evEX.obj (ρEX.obj K)) := by
        rw [hE K]
        simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc, Functor.map_comp,
          Category.assoc]
        rw [reassoc_of% nS]

-- A comparison is identified with a composite of associators through a faithful functor.
private theorem eq_of_balanced {A B : Type*} [Category A] [Category B] (ι : A ⥤ B)
    [ι.Faithful] {P Q R : A} (f : P ⟶ Q) (g₁ : P ⟶ R) (g₂ : Q ≅ R)
    {P' M W Q' : B} (s : P' ⟶ M) (t₁ : M ⟶ W) (t₂ : Q' ≅ W)
    {eP : ι.obj P = P'} {eQ : ι.obj Q = Q'} {eR eR' : ι.obj R = W}
    (hf : HEq (ι.map f) (s ≫ t₁ ≫ t₂.inv))
    (h₁ : ι.map g₁ ≫ eqToHom eR = eqToHom eP ≫ s ≫ t₁)
    (h₂ : ι.map g₂.hom ≫ eqToHom eR' = eqToHom eQ ≫ t₂.hom) :
    f = g₁ ≫ g₂.inv := by
  apply ι.map_injective
  rw [(conj_eqToHom_iff_heq (ι.map f) (s ≫ t₁ ≫ t₂.inv) eP eQ).2 hf]
  have h₁' : ι.map g₁ = eqToHom eP ≫ s ≫ t₁ ≫ eqToHom eR.symm := by
    rw [← reassoc_of% h₁, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have h₂' : ι.map g₂.inv = eqToHom eR' ≫ t₂.inv ≫ eqToHom eQ.symm := by
    rw [← cancel_epi (ι.map g₂.hom), ← ι.map_comp, Iso.hom_inv_id, ι.map_id,
      reassoc_of% h₂]
    simp
  rw [ι.map_comp, h₁', h₂']
  simp

-- The composite of two coefficient changes.
private def compositeChange {R S T : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) (b : PurCompactSupport.Change S T) :
    PurCompactSupport.Change R T where
  map W := a.map W ≫ b.map W
  square g := by
    rw [← Category.assoc, a.square g, Category.assoc, b.square g]
    simp only [Functor.map_comp, Category.assoc]


/-- The normalized selected comparison intertwines the left scalar mates. -/
theorem exceptionalIntegralSystemSelectedLeftCompat
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (transport : Transported l Ω D hl c operation left)
    (d : Mates l Ω c operation left)
    (red : ∀ (E : FieldStage.{u} l) (n : ℕ),
      ReductionMates l Ω D hl c operation left transport d E n)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (core : SystemScalarCore l Ω D hl c operation left transport d E L i)
    (selected_square : ∀ (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (T : Scheme.{u}),
    (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T)
    (selected : ∀ (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool),
    core.scalar side ⋙ (transport.reconstruction L side).evaluation z.m ≅
      (transport.reconstruction E side).evaluation z.n ⋙
        (d.scalar z.change z.allowed side).functor)
    (selected_balanced : ∀ (e : ℕ+)
      (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (side : Bool)
      (K : C.{u} l Ω (endpoint X Y side) (.integral E)),
    HEq ((finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
      (endpoint X Y side)).ι.map
        ((red L z.m).evaluation side |>.hom.app
            ((d.scalar (s := .integral E) (t := .integral L)
              (PurCompactSupport.completedChange l E.carrier L.carrier i)
              (Allowed.integral E L i) side).functor.obj K)) ≫
      (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
        (endpoint X Y side)).ι.map
        (((transport.reconstruction L side).evaluation z.m).map ((core.reduction side).hom.app K) ≫
          (selected e he z side).hom.app
            ((transport.reconstruction E side).equivalence.functor.obj K) ≫
          (d.scalar z.change z.allowed side).functor.map
            (((red E z.n).evaluation side).inv.app K)))
      ((pbcDerivedExtend ((PurCompactSupport.reduction l L.carrier
          (z.m + 1) (Nat.succ_pos z.m)).map (endpoint X Y side))).map
        ((d.scalar (s := .integral E) (t := .integral L)
          (PurCompactSupport.completedChange l E.carrier L.carrier i)
          (Allowed.integral E L i) side).realization.hom.app K) ≫
        (PurCompactSupport.tensorSquare
          ((PurCompactSupport.completedChange l E.carrier L.carrier i).map
            (endpoint X Y side)) (z.change.map (endpoint X Y side))
          ((PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map
            (endpoint X Y side))
          ((PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map
            (endpoint X Y side)) (selected_square e he z (endpoint X Y side))).hom.app K.obj)) :
    ∀ (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (z : RamifiedMap l E L i e he) (N : (sequenceProperty l E X).FullSubcategory),
    ((transport.reconstruction L false).evaluation z.m).map (core.q.hom.app N) ≫
      (transport.evaluationF L z.m).hom.app ((core.scalar true).obj N) ≫
      (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).F.map
        ((selected e he z true).hom.app N) =
    (selected e he z false).hom.app ((transport.F E).obj N) ≫
      (d.scalar z.change z.allowed false).functor.map
        ((transport.evaluationF E z.n).hom.app N) ≫
      (Mates.q l Ω d z.change z.allowed).hom.app
        (((transport.reconstruction E true).evaluation z.n).obj N) := by
  intro e he z N
  let d₀ : PurCompactSupport.Change ((RingStage.integral E).coefficients l)
      ((RingStage.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩).coefficients l) :=
    compositeChange (PurCompactSupport.completedChange l E.carrier L.carrier i)
      (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m))
  have hd₀ : Allowed l d₀ := Allowed.comp _ _ d₀ (fun _ ↦ rfl) (Allowed.integral E L i)
    (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩)
  have h₁ : ∀ T : Scheme.{u},
      (PurCompactSupport.completedChange l E.carrier L.carrier i).map T ≫
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)).map T =
      d₀.map T := fun _ ↦ rfl
  have h₂ : ∀ T : Scheme.{u},
      (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)).map T ≫
        z.change.map T = d₀.map T := fun T ↦ (selected_square e he z T).symm
  let α₁ (side : Bool) := d.scalarComposition _ _ d₀ h₁ (Allowed.integral E L i)
    (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩) hd₀ side
  let α₂ (side : Bool) := d.scalarComposition _ _ d₀ h₂
    (Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩) z.allowed hd₀ side
  have bal : ∀ (side : Bool) (K : C.{u} l Ω (endpoint X Y side) (.integral E)),
      ((red L z.m).evaluation side).hom.app
          ((d.scalar (s := .integral E) (t := .integral L)
            (PurCompactSupport.completedChange l E.carrier L.carrier i)
            (Allowed.integral E L i) side).functor.obj K) ≫
        ((transport.reconstruction L side).evaluation z.m).map
          ((core.reduction side).hom.app K) ≫
        (selected e he z side).hom.app
          ((transport.reconstruction E side).equivalence.functor.obj K) ≫
        (d.scalar z.change z.allowed side).functor.map
          (((red E z.n).evaluation side).inv.app K) =
      (α₁ side).iso.hom.app K ≫ (α₂ side).iso.inv.app K := by
    intro side K
    have n₁ := (α₁ side).normalized K
    have n₂ := (α₂ side).normalized K
    rw [d.finiteScalar_normalized (s := .integral E) L ⟨z.m + 1, Nat.succ_pos z.m⟩ d₀ hd₀
        side,
      d.finiteScalar_normalized (s := .integral L) L ⟨z.m + 1, Nat.succ_pos z.m⟩
        (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m))
        (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩) side] at n₁
    rw [d.finiteScalar_normalized (s := .integral E) L ⟨z.m + 1, Nat.succ_pos z.m⟩ d₀ hd₀
        side,
      d.finiteScalar_normalized (s := .finite E ⟨z.n + 1, Nat.succ_pos z.n⟩) L
        ⟨z.m + 1, Nat.succ_pos z.m⟩ z.change z.allowed side,
      d.finiteScalar_normalized (s := .integral E) E ⟨z.n + 1, Nat.succ_pos z.n⟩
        (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n))
        (Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩) side] at n₂
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans_assoc] at n₁ n₂
    refine eq_of_balanced
      (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m) (endpoint X Y side)).ι
      _ _ ((α₂ side).iso.app K) _ _
      ((PurCompactSupport.tensorComposition _ _ _ (h₂ (endpoint X Y side))).app K.obj)
      ?_ n₁ n₂
    rw [Functor.map_comp]
    exact selected_balanced e he z side K
  let (side : Bool) := (d.scalar _ (Allowed.integral E L i) side).commShift
  let (side : Bool) := (d.scalar (s := .integral _) (t := .finite E ⟨z.n + 1, Nat.succ_pos z.n⟩)
    (PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n))
    (Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩) side).commShift
  let (side : Bool) := (d.scalar (s := .integral _) (t := .finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)
    (PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m))
    (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩) side).commShift
  let (side : Bool) := (d.scalar z.change z.allowed side).commShift
  let (side : Bool) := (d.scalar d₀ hd₀ side).commShift
  exact selectedLeftCompat_of_cocycles
    (transport.reconstruction E true).equivalence.functor
    (transport.reconstruction E false).equivalence.functor
    (transport.reconstruction L true).equivalence.functor
    (transport.reconstruction L false).equivalence.functor
    ((transport.reconstruction E true).evaluation z.n)
    ((transport.reconstruction E false).evaluation z.n)
    ((transport.reconstruction L true).evaluation z.m)
    ((transport.reconstruction L false).evaluation z.m)
    (core.scalar true) (core.scalar false) (transport.F E) (transport.F L)
    (operation (.integral E)).F (operation (.integral L)).F
    (operation (.finite E ⟨z.n + 1, Nat.succ_pos z.n⟩)).F
    (operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)).F
    _ _ _ _ _ _ _ _ _ _
    (core.reduction true) (core.reduction false)
    ((red E z.n).evaluation true) ((red E z.n).evaluation false)
    ((red L z.m).evaluation true) ((red L z.m).evaluation false)
    (selected e he z true) (selected e he z false) core.q
    (transport.reductionF E) (transport.reductionF L)
    (transport.evaluationF E z.n) (transport.evaluationF L z.m)
    (Mates.q l Ω d _ (Allowed.integral E L i))
    (Mates.q l Ω d _ (Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩))
    (Mates.q l Ω d _ (Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩))
    (Mates.q l Ω d z.change z.allowed) (Mates.q l Ω d d₀ hd₀)
    (α₁ true).iso (α₁ false).iso (α₂ true).iso (α₂ false).iso
    core.q_reduction (red E z.n).q_evaluation (red L z.m).q_evaluation
    (d.cocycle _ _ d₀ h₁ _ _ hd₀).left (d.cocycle _ _ d₀ h₂ _ _ hd₀).left
    (bal true) (bal false) N

end WeilConjectures.ExceptionalIntegralScalar
