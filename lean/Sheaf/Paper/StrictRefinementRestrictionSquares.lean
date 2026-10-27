/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps

import Sheaf.Paper.StrictRefinementSeedRestriction
import Sheaf.Paper.StrictProperCompositionRestriction

/-! # Restriction squares for the normalized strict refinement

Source: Stacks 0F7B--0F7D, 07A6 and 0940; auxiliary comparison Step 7.
(blueprint: lem-pur-strict-refinement-restriction-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local instance 5000] AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtale.StrictTower.towers_hasDerivedCategory
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] U J R G
  properRestriction openRestriction reindexProper reindexOpen rId rComp gamma

-- Keep the pasting calculation abstract to avoid expanding the derived functors
-- when checking their component equations.
private theorem map_three_eq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {V W X Y Z : C} {a : V ⟶ W} {b : W ⟶ X} {c : X ⟶ Z}
    {d : V ⟶ Y} {e : Y ⟶ Z} (h : a ≫ b ≫ c = d ≫ e) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e := by
  simpa only [Functor.map_comp] using congrArg (fun z ↦ F.map z) h

private theorem restriction_paste
    {C : Type*} [Category C] {V W W' Z Z' P Q S T T' : C}
    {s : V ⟶ W} {t : W ⟶ Z} {a : Z ⟶ Z'} {p : Z' ⟶ S}
    {a' : W ⟶ W'} {t' : W' ⟶ Z'} {p' : W' ⟶ P}
    {q : P ⟶ Q} {v : Q ⟶ S} {b : V ⟶ T} {u : T ⟶ P}
    {q' : T ⟶ T'} {u' : T' ⟶ Q} {w : T' ⟶ S}
    (ha : a' ≫ t' = t ≫ a) (hp : p' ≫ q ≫ v = t' ≫ p)
    (hs : s ≫ a' ≫ p' = b ≫ u) (hq : u ≫ q = q' ≫ u')
    (hv : u' ≫ v = w) :
    (s ≫ t) ≫ (a ≫ p) = (b ≫ q') ≫ w := by
  simp only [Category.assoc]
  rw [← reassoc_of% ha, ← hp]
  try simp only [Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hq, hv]

private theorem reindex_paste
    {C : Type*} [Category C] {V W Z P Q S T T' W' Z' : C}
    {s : V ⟶ W} {t : W ⟶ Z} {p : Z ⟶ P} {a : P ⟶ S}
    {q : W ⟶ Q} {r : Q ⟶ T} {v : T ⟶ P}
    {r' : T ⟶ T'} {v' : T' ⟶ S} {q' : V ⟶ W'}
    {u : W' ⟶ Q} {b : W' ⟶ Z'} {u' : Z' ⟶ T'} {w : V ⟶ Z}
    (hp : t ≫ p = q ≫ r ≫ v) (ha : r' ≫ v' = v ≫ a)
    (hq : s ≫ q = q' ≫ u) (hs : u ≫ r ≫ r' = b ≫ u')
    (hw : w = s ≫ t) :
    w ≫ (p ≫ a) = (q' ≫ b) ≫ (u' ≫ v') := by
  rw [hw]
  simp only [Category.assoc]
  rw [reassoc_of% hp, ← ha, reassoc_of% hq]
  try simp only [Category.assoc]
  rw [reassoc_of% hs]

private theorem coefficient_functor_paste
    {CX CW CT CY DX DW DT DY : Type*}
    [Category CX] [Category CW] [Category CT] [Category CY]
    [Category DX] [Category DW] [Category DT] [Category DY]
    {Jc : CX ⥤ CW} {Jd : CX ⥤ CT} {Sc : DX ⥤ DW} {Sd : DX ⥤ DT}
    {Rc : CW ⥤ CT} {Rg : CT ⥤ CY} {Rq : CW ⥤ CY}
    {Pc : DW ⥤ DT} {Pg : DT ⥤ DY} {Pq : DW ⥤ DY}
    (Ux : DX ⥤ CX) (Uw : DW ⥤ CW) (Ut : DT ⥤ CT) (Uy : DY ⥤ CY)
    (sA : 𝟭 CX ⋙ Jd ⟶ Jc ⋙ Rc) (sB : 𝟭 DX ⋙ Sd ⟶ Sc ⋙ Pc)
    (tA : Rc ⋙ Rg ⟶ Rq) (tB : Pc ⋙ Pg ⟶ Pq)
    (oc : Ux ⋙ Jc ⟶ Sc ⋙ Uw) (od : Ux ⋙ Jd ⟶ Sd ⋙ Ut)
    (pr : Uw ⋙ Rc ⟶ Pc ⋙ Ut) (pd : Ut ⋙ Rg ⟶ Pg ⋙ Uy)
    (pq : Uw ⋙ Rq ⟶ Pq ⋙ Uy)
    (hs : ∀ N, sA.app (Ux.obj N) ≫ Rc.map (oc.app N) ≫ pr.app (Sc.obj N) =
      od.app N ≫ Ut.map (sB.app N))
    (hp : ∀ M, Rg.map (pr.app M) ≫ pd.app (Pc.obj M) ≫ Uy.map (tB.app M) =
      tA.app (Uw.obj M) ≫ pq.app M) (N : DX) :
    (Rg.map (sA.app (Ux.obj N)) ≫ tA.app (Jc.obj (Ux.obj N))) ≫
        (Rq.map (oc.app N) ≫ pq.app (Sc.obj N)) =
      (Rg.map (od.app N) ≫ pd.app (Sd.obj N)) ≫
        Uy.map (Pg.map (sB.app N) ≫ tB.app (Sc.obj N)) := by
  exact restriction_paste (tA.naturality (oc.app N)) (hp (Sc.obj N))
    (map_three_eq Rg (hs N)) (pd.naturality (sB.app N))
    (Uy.map_comp _ _).symm

private theorem selection_functor_paste
    {CX CW CT CY : Type*}
    [Category CX] [Category CW] [Category CT] [Category CY]
    {Jc : CX ⥤ CW} {Jd : CX ⥤ CT}
    {Rr : CW ⥤ CT} {Rg : CT ⥤ CY} {Rq : CW ⥤ CY}
    (Px : CX ⥤ CX) (Pw : CW ⥤ CW) (Pt : CT ⥤ CT) (Py : CY ⥤ CY)
    (s : 𝟭 CX ⋙ Jd ⟶ Jc ⋙ Rr) (t : Rr ⋙ Rg ⟶ Rq)
    (oc : Jc ⋙ Pw ⟶ Px ⋙ Jc) (od : Jd ⋙ Pt ⟶ Px ⋙ Jd)
    (pr : Rr ⋙ Pt ⟶ Pw ⋙ Rr) (pd : Rg ⋙ Py ⟶ Pt ⋙ Rg)
    (pq : Rq ⋙ Py ⟶ Pw ⋙ Rq)
    (hs : ∀ N, Pt.map (s.app N) ≫ pr.app (Jc.obj N) ≫ Rr.map (oc.app N) =
      od.app N ≫ s.app (Px.obj N))
    (hp : ∀ M, Py.map (t.app M) ≫ pq.app M =
      pd.app (Rr.obj M) ≫ Rg.map (pr.app M) ≫ t.app (Pw.obj M)) (N : CX) :
    Py.map (Rg.map (s.app N) ≫ t.app (Jc.obj N)) ≫
        (pq.app (Jc.obj N) ≫ Rq.map (oc.app N)) =
      (pd.app (Jd.obj N) ≫ Rg.map (od.app N)) ≫
        (Rg.map (s.app (Px.obj N)) ≫ t.app (Jc.obj (Px.obj N))) := by
  exact reindex_paste (hp (Jc.obj N)) (t.naturality (oc.app N))
    (pd.naturality (s.app N)) (map_three_eq Rg (hs N)) (Py.map_comp _ _)

private theorem coefficient_square_paste
    {CX CW CT CY DX DW DT DY : Type*}
    [Category CX] [Category CW] [Category CT] [Category CY]
    [Category DX] [Category DW] [Category DT] [Category DY]
    {Jc : CX ⥤ CW} {Jd : CX ⥤ CT} {Sc : DX ⥤ DW} {Sd : DX ⥤ DT}
    {Rc : CW ⥤ CT} {Rg : CT ⥤ CY} {Rq : CW ⥤ CY}
    {Pc : DW ⥤ DT} {Pg : DT ⥤ DY} {Pq : DW ⥤ DY}
    (Ux : DX ⥤ CX) (Uw : DW ⥤ CW) (Ut : DT ⥤ CT) (Uy : DY ⥤ CY)
    (sA : 𝟭 CX ⋙ Jd ⟶ Jc ⋙ Rc) (sB : 𝟭 DX ⋙ Sd ⟶ Sc ⋙ Pc)
    (tA : Rc ⋙ Rg ⟶ Rq) (tB : Pc ⋙ Pg ⟶ Pq)
    (oc : Ux ⋙ Jc ⟶ Sc ⋙ Uw) (od : Ux ⋙ Jd ⟶ Sd ⋙ Ut)
    (pr : Uw ⋙ Rc ⟶ Pc ⋙ Ut) (pd : Ut ⋙ Rg ⟶ Pg ⋙ Uy)
    (pq : Uw ⋙ Rq ⟶ Pq ⋙ Uy)
    (hs : ∀ N, sA.app (Ux.obj N) ≫ Rc.map (oc.app N) ≫ pr.app (Sc.obj N) =
      od.app N ≫ Ut.map (sB.app N))
    (hp : ∀ M, Rg.map (pr.app M) ≫ pd.app (Pc.obj M) ≫ Uy.map (tB.app M) =
      tA.app (Uw.obj M) ≫ pq.app M) :
    Functor.whiskerLeft Ux
        (Functor.whiskerRight sA Rg ≫ Functor.whiskerLeft Jc tA) ≫
        (Functor.whiskerRight oc Rq ≫ Functor.whiskerLeft Sc pq) =
      (Functor.whiskerRight od Rg ≫ Functor.whiskerLeft Sd pd) ≫
        Functor.whiskerRight
          (Functor.whiskerRight sB Pg ≫ Functor.whiskerLeft Sc tB) Uy := by
  apply NatTrans.ext
  funext N
  exact coefficient_functor_paste Ux Uw Ut Uy sA sB tA tB oc od pr pd pq hs hp N

private theorem selection_square_paste
    {CX CW CT CY : Type*}
    [Category CX] [Category CW] [Category CT] [Category CY]
    {Jc : CX ⥤ CW} {Jd : CX ⥤ CT}
    {Rr : CW ⥤ CT} {Rg : CT ⥤ CY} {Rq : CW ⥤ CY}
    (Px : CX ⥤ CX) (Pw : CW ⥤ CW) (Pt : CT ⥤ CT) (Py : CY ⥤ CY)
    (s : 𝟭 CX ⋙ Jd ⟶ Jc ⋙ Rr) (t : Rr ⋙ Rg ⟶ Rq)
    (oc : Jc ⋙ Pw ⟶ Px ⋙ Jc) (od : Jd ⋙ Pt ⟶ Px ⋙ Jd)
    (pr : Rr ⋙ Pt ⟶ Pw ⋙ Rr) (pd : Rg ⋙ Py ⟶ Pt ⋙ Rg)
    (pq : Rq ⋙ Py ⟶ Pw ⋙ Rq)
    (hs : ∀ N, Pt.map (s.app N) ≫ pr.app (Jc.obj N) ≫ Rr.map (oc.app N) =
      od.app N ≫ s.app (Px.obj N))
    (hp : ∀ M, Py.map (t.app M) ≫ pq.app M =
      pd.app (Rr.obj M) ≫ Rg.map (pr.app M) ≫ t.app (Pw.obj M)) :
    Functor.whiskerRight
        (Functor.whiskerRight s Rg ≫ Functor.whiskerLeft Jc t) Py ≫
        (Functor.whiskerLeft Jc pq ≫ Functor.whiskerRight oc Rq) =
      (Functor.whiskerLeft Jd pd ≫ Functor.whiskerRight od Rg) ≫
        Functor.whiskerLeft Px
          (Functor.whiskerRight s Rg ≫ Functor.whiskerLeft Jc t) := by
  apply NatTrans.ext
  funext N
  exact selection_functor_paste Px Pw Pt Py s t oc od pr pd pq hs hp N

/-- Coefficient restriction and positive arithmetic selection preserve the actual
normalized proper/open refinement arrow on constant-coefficient strict towers.
Source: Stacks 0F7B--0F7D, 07A6 and 0940; auxiliary comparison Step 7.
(blueprint: lem-pur-strict-refinement-restriction-squares).
Proof: expand compositionC as the identity proper compositor, the proper mate of
alpha, and the proper composition identification. Restriction of coefficients
commutes with inverse image, open extension and direct image. On the pulled-back
open unit its comparison is the same section; on the clopen projector it is
identity on the section component and zero on the complement. Hence it carries
the specified alpha to alpha. Taking the proper adjunction mate, retaining the
ordered composite counit, gives its gamma square. Paste with the proper identity
and composition squares to obtain the first equation, whose horizontal maps are
exactly pastedRestriction. For the second equation, arithmetic selection is exact
and preserves K-injectives for positive e. It commutes termwise with open extension
and direct image, and hence with the same units, clopen projection and compositors.
The unit-normalized derived composite comparisons are precisely reindexImage.
Pasting these squares gives the second equation in the derived category of strict
towers itself; neither equation is deduced from finite derived evaluations. -/
theorem strictRefinementRestrictionSquares
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    [QuasiCompact c.i] [QuasiCompact d.i] (r : c.Refinement d) :
    (Functor.whiskerLeft (U l E F i X)
        (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r) ≫
        (pastedRestriction l E F i c).hom =
      (pastedRestriction l E F i d).hom ≫ Functor.whiskerRight
        (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r)
        (U l E F i Y)) ∧
    ∀ (e : ℕ) (he : 1 ≤ e),
      Functor.whiskerRight
          (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r)
          (subsequence l F Y e) ≫ (reindexImage l F c e he).hom =
        (reindexImage l F d e he).hom ≫ Functor.whiskerLeft (subsequence l F X e)
          (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r) := by
  let sA := Functor.whiskerRight (rId (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    X).inv (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) d.i) ≫
    gamma (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.i (𝟙 X) r.hom d.i
      (r.i_hom.trans (Category.id_comp d.i).symm)
  let sB := Functor.whiskerRight (rId (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))
    X).inv (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) d.i) ≫
    gamma (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c.i (𝟙 X) r.hom d.i
      (r.i_hom.trans (Category.id_comp d.i).symm)
  let tA := (rComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r.hom d.g).hom ≫
    (eqToIso (congrArg (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) r.hom_g)).hom
  let tB := (rComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r.hom d.g).hom ≫
    (eqToIso (congrArg (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))) r.hom_g)).hom
  have hseedData := strictRefinementSeedRestriction l E F i c.i d.i r.hom
    (r.i_hom.trans (Category.id_comp d.i).symm)
  have hs := hseedData.1
  have hs' := hseedData.2
  have hproperData := strictProperCompositionRestriction l E F i r.hom d.g c.g r.hom_g
  have ht := hproperData.1
  have ht' := hproperData.2
  constructor
  · exact coefficient_square_paste
      (U l E F i X) (U l E F i c.Z) (U l E F i d.Z) (U l E F i Y)
      sA sB tA tB (openRestriction l E F i c.i).hom (openRestriction l E F i d.i).hom
      (properRestriction l E F i r.hom).inv (properRestriction l E F i d.g).inv
      (properRestriction l E F i c.g).inv hs ht
  · intro e he
    exact selection_square_paste
      (subsequence l F X e) (subsequence l F c.Z e)
      (subsequence l F d.Z e) (subsequence l F Y e)
      sB tB (reindexOpen l F c.i e).hom (reindexOpen l F d.i e).hom
      (reindexProper l F r.hom e he).hom (reindexProper l F d.g e he).hom
      (reindexProper l F c.g e he).hom (hs' e he) (ht' e he)

end WeilConjectures.PurStrictScalar
