/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralSystemScalarCoreData

/-! # Proper/open compatibility of the normalized selected scalar comparison
Source: Zheng, Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-system-selected-left-compat)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem inverse_coordinates {C : Type*} [Category C] {X Y Z W V : C}
    (f : X ≅ Y) (g : Y ≅ Z) (h : X ≅ W) (i : W ≅ V) (j : V ≅ Z)
    (eqn : f.hom ≫ g.hom = h.hom ≫ i.hom ≫ j.hom) :
    f.inv = g.hom ≫ j.inv ≫ i.inv ≫ h.inv := by
  apply (cancel_epi f.hom).1
  simp only [Iso.hom_inv_id, ← Category.assoc]
  rw [eqn]
  simp only [Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The normalized selected comparison intertwines the left scalar mates.
Source: Zheng, Lemma 5.22 and Proposition 5.26, the coefficient projection square.
Proof: first precompose both paths with reconstruction over E. Its essential
surjectivity will recover the equality on every normalized sequence. Expand the
selected comparison using selected_balanced; the finite inclusion is faithful, and
the surrounding reduction comparison factors are invertible. Substitute
core.q_reduction on the whole-system side and red.q_evaluation on the finite
reduction sides. The remaining square is precisely the left comparison cocycle
for the two coefficient paths, whose scalar associators are fixed by
d.scalarComposition.normalized. The normalized proper coefficient projection and
open balancing comparisons identify its composite coefficient maps. Cancel the
common associator and red factors to get the equality on reconstructed objects.
For an arbitrary N use the reconstruction counit isomorphism; naturality of each
comparison transports the equality along that isomorphism. This argument uses
faithfulness only of the full inclusion and equivalence, never of evaluation.
(blueprint: lem-sf-exceptional-integral-system-selected-left-compat). -/
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
  intro e he z
  let a : PurCompactSupport.Change
      ((RingStage.integral E).coefficients l) ((RingStage.integral L).coefficients l) :=
    PurCompactSupport.completedChange l E.carrier L.carrier i
  let s : PurCompactSupport.Change
      ((RingStage.integral L).coefficients l)
      ((RingStage.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩).coefficients l) :=
    PurCompactSupport.reduction l L.carrier (z.m + 1) (Nat.succ_pos z.m)
  let r : PurCompactSupport.Change
      ((RingStage.integral E).coefficients l)
      ((RingStage.finite E ⟨z.n + 1, Nat.succ_pos z.n⟩).coefficients l) :=
    PurCompactSupport.reduction l E.carrier (z.n + 1) (Nat.succ_pos z.n)
  let b := z.change
  let ha := Allowed.integral E L i
  let hs := Allowed.reduction L ⟨z.m + 1, Nat.succ_pos z.m⟩
  let hr := Allowed.reduction E ⟨z.n + 1, Nat.succ_pos z.n⟩
  let hb := z.allowed
  let v : PurCompactSupport.Change
      ((RingStage.integral E).coefficients l)
      ((RingStage.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩).coefficients l) :=
    { map := fun T ↦ a.map T ≫ s.map T
      square := fun g ↦ by
        rw [← Category.assoc, a.square g, Category.assoc, s.square g,
          Functor.map_comp, Category.assoc] }
  have hv := Allowed.comp a s v (fun _ ↦ rfl) ha hs
  let α (side : Bool) := d.scalarComposition a s v (fun _ ↦ rfl) ha hs hv side
  let β (side : Bool) := d.scalarComposition r b v
    (fun T ↦ (selected_square e he z T).symm) hr hb hv side
  let θ (side : Bool) := (α side).iso ≪≫ (β side).iso.symm
  have hθ (side : Bool) (K : C.{u} l Ω (endpoint X Y side) (.integral E)) :
      ((red L z.m).evaluation side).hom.app ((d.scalar a ha side).functor.obj K) ≫
        ((transport.reconstruction L side).evaluation z.m).map
          ((core.reduction side).hom.app K) ≫
        (selected e he z side).hom.app
          ((transport.reconstruction E side).equivalence.functor.obj K) ≫
        (d.scalar b hb side).functor.map (((red E z.n).evaluation side).inv.app K) =
      (θ side).hom.app K := by
    let I := (finiteTorConstructible l L.carrier (z.m + 1) (Nat.succ_pos z.m)
      (endpoint X Y side)).ι
    have hα := (α side).normalized K
    have hβ := (β side).normalized K
    have hmap : I.map ((θ side).hom.app K) =
        (d.scalar s hs side).realization.hom.app ((d.scalar a ha side).functor.obj K) ≫
        (pbcDerivedExtend (s.map (endpoint X Y side))).map
          ((d.scalar a ha side).realization.hom.app K) ≫
        (PurCompactSupport.tensorSquare (a.map (endpoint X Y side))
          (b.map (endpoint X Y side)) (r.map (endpoint X Y side))
          (s.map (endpoint X Y side)) (selected_square e he z (endpoint X Y side))).hom.app
          K.obj ≫
        (pbcDerivedExtend (b.map (endpoint X Y side))).map
          ((d.scalar r hr side).realization.inv.app K) ≫
        (d.scalar b hb side).realization.inv.app ((d.scalar r hr side).functor.obj K) := by
      have hβ' := inverse_coordinates (I.mapIso ((β side).iso.app K))
        ((d.scalar v hv side).realization.app K)
        ((d.scalar b hb side).realization.app ((d.scalar r hr side).functor.obj K))
        ((pbcDerivedExtend (b.map (endpoint X Y side))).mapIso
          ((d.scalar r hr side).realization.app K))
        ((PurCompactSupport.tensorComposition (r.map (endpoint X Y side))
          (b.map (endpoint X Y side)) (v.map (endpoint X Y side))
          (selected_square e he z (endpoint X Y side)).symm).app K.obj) hβ
      dsimp only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom] at hβ'
      simp only [θ, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, I.map_comp]
      rw [hβ', ← Category.assoc]
      erw [hα]
      simp only [PurCompactSupport.tensorSquare, Iso.trans_hom, NatTrans.comp_app,
        Iso.symm_hom, Category.assoc]
      rfl
    apply I.map_injective
    apply eq_of_heq
    have hbal := selected_balanced e he z side K
    simp only [← I.map_comp, I] at hbal
    refine hbal.trans ?_
    rw [hmap]
    simp only [d.finiteScalar_normalized]
    simp only [eqToIso, eqToHom_app, eqToHom_map, ← Category.assoc,
      heq_comp_eqToHom_iff]
    simp only [Category.assoc, heq_eqToHom_comp_iff]
    rfl
  let A := operation (.integral E)
  let D₀ := operation (.finite L ⟨z.m + 1, Nat.succ_pos z.m⟩)
  let Sa (side : Bool) := (d.scalar a ha side).functor
  let Ss (side : Bool) := (d.scalar s hs side).functor
  let Sr (side : Bool) := (d.scalar r hr side).functor
  let Sb (side : Bool) := (d.scalar b hb side).functor
  let qa := Mates.q l Ω d a ha
  let qs := Mates.q l Ω d s hs
  let qr := Mates.q l Ω d r hr
  let qb := Mates.q l Ω d b hb
  have hraw (K : C.{u} l Ω X (.integral E)) :
      (Ss false).map (qa.hom.app K) ≫ qs.hom.app ((Sa true).obj K) ≫
        D₀.F.map ((θ true).hom.app K) =
      (θ false).hom.app (A.F.obj K) ≫ (Sb false).map (qr.hom.app K) ≫
        qb.hom.app ((Sr true).obj K) := by
    let := (d.scalar a ha true).commShift
    let := (d.scalar a ha false).commShift
    let := (d.scalar s hs true).commShift
    let := (d.scalar s hs false).commShift
    let := (d.scalar r hr true).commShift
    let := (d.scalar r hr false).commShift
    let := (d.scalar b hb true).commShift
    let := (d.scalar b hb false).commShift
    let := (d.scalar v hv true).commShift
    let := (d.scalar v hv false).commShift
    have hα := (d.cocycle a s v (fun _ ↦ rfl) ha hs hv).left K
    have hβ := (d.cocycle r b v
      (fun T ↦ (selected_square e he z T).symm) hr hb hv).left K
    apply (cancel_mono (D₀.F.map ((β true).iso.hom.app K))).1
    dsimp only [θ, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp, Iso.inv_hom_id_app,
      Category.comp_id]
    erw [hβ]
    have hβcancel := (β false).iso.inv_hom_id_app (A.F.obj K)
    erw [reassoc_of% hβcancel]
    exact hα
  let RX := transport.reconstruction E true
  let LY := transport.reconstruction L false
  let mY := LY.evaluation z.m
  let nX := RX.evaluation z.n
  let x := selected e he z true
  let y := selected e he z false
  let fL := transport.evaluationF L z.m
  let fE := transport.evaluationF E z.n
  let eLY := (red L z.m).evaluation false
  let eEX := (red E z.n).evaluation true
  have hmain (K : C.{u} l Ω X (.integral E)) :
      mY.map (core.q.hom.app (RX.equivalence.functor.obj K)) ≫
        fL.hom.app ((core.scalar true).obj (RX.equivalence.functor.obj K)) ≫
        D₀.F.map (x.hom.app (RX.equivalence.functor.obj K)) =
      y.hom.app ((transport.F E).obj (RX.equivalence.functor.obj K)) ≫
        (Sb false).map (fE.hom.app (RX.equivalence.functor.obj K)) ≫
        qb.hom.app (nX.obj (RX.equivalence.functor.obj K)) := by
    have hh := congrArg (fun t ↦ t ≫ D₀.F.map
      ((Sb true).map (eEX.hom.app K))) (hraw K)
    rw [← hθ true K, ← hθ false (A.F.obj K)] at hh
    simp only [Functor.map_comp, Category.assoc] at hh
    have hcancel : D₀.F.map ((Sb true).map (eEX.inv.app K)) ≫
        D₀.F.map ((Sb true).map (eEX.hom.app K)) = 𝟙 _ := by
      rw [← D₀.F.map_comp, ← (Sb true).map_comp, Iso.inv_hom_id_app,
        (Sb true).map_id, D₀.F.map_id]
    erw [hcancel] at hh
    erw [Category.comp_id] at hh
    have hqb := qb.hom.naturality (eEX.hom.app K)
    dsimp only [Functor.comp_map] at hqb
    erw [← hqb] at hh
    have hrq := congrArg (Sb false).map ((red E z.n).q_evaluation K)
    simp only [Functor.map_comp] at hrq
    erw [reassoc_of% hrq] at hh
    erw [← (Sb false).map_comp_assoc, Iso.inv_hom_id_app,
      (Sb false).map_id, Category.id_comp] at hh
    rw [reassoc_of% ((red L z.m).q_evaluation ((Sa true).obj K))] at hh
    have heLY := eLY.hom.naturality (qa.hom.app K)
    dsimp only [Functor.comp_map] at heLY
    rw [reassoc_of% heLY] at hh
    have hfL := fL.hom.naturality ((core.reduction true).hom.app K)
    dsimp only [Functor.comp_map] at hfL
    rw [← reassoc_of% hfL] at hh
    rw [← mY.map_comp_assoc, ← mY.map_comp_assoc] at hh
    simp only [Category.assoc] at hh
    erw [core.q_reduction K] at hh
    simp only [Functor.map_comp, Category.assoc] at hh
    have hy := y.hom.naturality ((transport.reductionF E).hom.app K)
    dsimp only [Functor.comp_map] at hy
    rw [← reassoc_of% hy] at hh
    apply (cancel_epi (eLY.hom.app ((Sa false).obj (A.F.obj K)) ≫
      mY.map ((core.reduction false).hom.app (A.F.obj K)) ≫
      mY.map ((core.scalar false).map ((transport.reductionF E).hom.app K)))).1
    simpa only [Category.assoc, Sa, Ss, Sb, eLY, mY, RX, A, D₀, nX, x, y,
      fL, fE, Functor.comp_obj, Functor.comp_map] using hh
  let lhs : transport.F E ⋙ core.scalar false ⋙ mY ⟶
      (nX ⋙ Sb true) ⋙ D₀.F :=
    whiskerRight core.q.hom mY ≫ whiskerLeft (core.scalar true) fL.hom ≫
      whiskerRight x.hom D₀.F
  let rhs : transport.F E ⋙ core.scalar false ⋙ mY ⟶
      (nX ⋙ Sb true) ⋙ D₀.F :=
    whiskerLeft (transport.F E) y.hom ≫ whiskerRight fE.hom (Sb false) ≫
      whiskerLeft nX qb.hom
  have heq : lhs = rhs := by
    apply ((Functor.whiskeringLeft _ _ _).obj RX.equivalence.functor).map_injective
    apply NatTrans.ext
    funext K
    exact hmain K
  intro N
  exact congr_app heq N

end WeilConjectures.ExceptionalIntegralScalar
