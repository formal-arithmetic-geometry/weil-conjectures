module

public import Sheaf.Paper.RingedRefinementData
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.RingedRefinementCore
import Sheaf.Paper.RingedRefinementClopen
public import Sheaf.Paper.RingedProperOpenPullbackCoefficients
import Sheaf.Paper.RingedRefinementMate
import Sheaf.AlgebraicGeometry.ProperOpenClopenProjector

/-!
# Arbitrary ring-sheaf coefficients and the proper/open mate

Source: Stacks Project, more-etale.tex, Tag 0F7B (open case), and the
agent coefficient-change supplement, on ordinary and vertical sequence sites
(blueprint: lem-pur-ringed-proper-open-coefficient-square).

The ringed-site operations and their normalizations are the existing
`RingedRefinement` interfaces. The four-sided square below has arbitrary proper
left vertical map; it is not restricted to refinement triangles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory

namespace SheafOfModules.RingedProperOpen

/-- The unit/pullback-map/counit formula for a square with two adjunctions.
Source: Stacks 07A6, coefficient supplement Steps 4--5
(blueprint: def-pur-ringed-proper-open-mate-formula). -/
def properOpenMate
    {U V W Z : Type*} [Category U] [Category V] [Category W] [Category Z]
    {lp : Z ⥤ V} {rp : V ⥤ Z} {lr : W ⥤ U} {rr : U ⥤ W}
    (ap : lp ⊣ rp) (ar : lr ⊣ rr) (i : W ⥤ Z) (k : U ⥤ V)
    (ta : i ⋙ lp ⟶ lr ⋙ k) : rr ⋙ i ⟶ k ⋙ rp :=
  Functor.whiskerLeft (rr ⋙ i) ap.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft rr ta) rp ≫
    Functor.whiskerRight (Functor.whiskerRight ar.counit k) rp

/-- The scalar and mate composite on one side of a proper/open coefficient square.
Source: Stacks 07A6, coefficient supplement Steps 4--5
(blueprint: def-pur-ringed-proper-open-mate-formula). -/
def properOpenLeft
    {UA VA WA ZA UB VB WB ZB : Type*}
    [Category UA] [Category VA] [Category WA] [Category ZA]
    [Category UB] [Category VB] [Category WB] [Category ZB]
    {lpA : ZA ⥤ VA} {rpA : VA ⥤ ZA} {lpB : ZB ⥤ VB} {rpB : VB ⥤ ZB}
    {lrA : WA ⥤ UA} {rrA : UA ⥤ WA} {lrB : WB ⥤ UB} {rrB : UB ⥤ WB}
    (apA : lpA ⊣ rpA) (apB : lpB ⊣ rpB)
    (arA : lrA ⊣ rrA) (_arB : lrB ⊣ rrB)
    {su : UA ⥤ UB} {sv : VA ⥤ VB} {sw : WA ⥤ WB} {sz : ZA ⥤ ZB}
    {iA : WA ⥤ ZA} {iB : WB ⥤ ZB} {kA : UA ⥤ VA} {kB : UB ⥤ VB}
    (cp : sz ⋙ lpB ⟶ lpA ⋙ sv) (_cr : sw ⋙ lrB ⟶ lrA ⋙ su)
    (_di : iA ⋙ sz ⟶ sw ⋙ iB) (dk : kA ⋙ sv ⟶ su ⋙ kB)
    (ta : iA ⋙ lpA ⟶ lrA ⋙ kA) (_tb : iB ⋙ lpB ⟶ lrB ⋙ kB) :
    rrA ⋙ iA ⋙ sz ⟶ su ⋙ kB ⋙ rpB :=
  Functor.whiskerRight (properOpenMate apA arA iA kA ta) sz ≫
    Functor.whiskerLeft kA
      (mateEquiv apA apB (TwoSquare.mk _ _ _ _ cp)).natTrans ≫
    Functor.whiskerRight dk rpB

/-- The scalar and mate composite on one side of a proper/open coefficient square.
Source: Stacks 07A6, coefficient supplement Steps 4--5
(blueprint: def-pur-ringed-proper-open-mate-formula). -/
def properOpenRight
    {UA VA WA ZA UB VB WB ZB : Type*}
    [Category UA] [Category VA] [Category WA] [Category ZA]
    [Category UB] [Category VB] [Category WB] [Category ZB]
    {lpA : ZA ⥤ VA} {rpA : VA ⥤ ZA} {lpB : ZB ⥤ VB} {rpB : VB ⥤ ZB}
    {lrA : WA ⥤ UA} {rrA : UA ⥤ WA} {lrB : WB ⥤ UB} {rrB : UB ⥤ WB}
    (_apA : lpA ⊣ rpA) (apB : lpB ⊣ rpB)
    (arA : lrA ⊣ rrA) (arB : lrB ⊣ rrB)
    {su : UA ⥤ UB} {sv : VA ⥤ VB} {sw : WA ⥤ WB} {sz : ZA ⥤ ZB}
    {iA : WA ⥤ ZA} {iB : WB ⥤ ZB} {kA : UA ⥤ VA} {kB : UB ⥤ VB}
    (_cp : sz ⋙ lpB ⟶ lpA ⋙ sv) (cr : sw ⋙ lrB ⟶ lrA ⋙ su)
    (di : iA ⋙ sz ⟶ sw ⋙ iB) (_dk : kA ⋙ sv ⟶ su ⋙ kB)
    (_ta : iA ⋙ lpA ⟶ lrA ⋙ kA) (tb : iB ⋙ lpB ⟶ lrB ⋙ kB) :
    rrA ⋙ iA ⋙ sz ⟶ su ⋙ kB ⋙ rpB :=
  Functor.whiskerLeft rrA di ≫
    Functor.whiskerRight
      (mateEquiv arA arB (TwoSquare.mk _ _ _ _ cr)).natTrans iB ≫
    Functor.whiskerLeft su (properOpenMate apB arB iB kB tb)

private theorem proper_open_coefficient_mate
    {UA VA WA ZA UB VB WB ZB : Type*}
    [Category UA] [Category VA] [Category WA] [Category ZA]
    [Category UB] [Category VB] [Category WB] [Category ZB]
    {lpA : ZA ⥤ VA} {rpA : VA ⥤ ZA} {lpB : ZB ⥤ VB} {rpB : VB ⥤ ZB}
    {lrA : WA ⥤ UA} {rrA : UA ⥤ WA} {lrB : WB ⥤ UB} {rrB : UB ⥤ WB}
    (apA : lpA ⊣ rpA) (apB : lpB ⊣ rpB)
    (arA : lrA ⊣ rrA) (arB : lrB ⊣ rrB)
    {su : UA ⥤ UB} {sv : VA ⥤ VB} {sw : WA ⥤ WB} {sz : ZA ⥤ ZB}
    {iA : WA ⥤ ZA} {iB : WB ⥤ ZB} {kA : UA ⥤ VA} {kB : UB ⥤ VB}
    (cp : sz ⋙ lpB ⟶ lpA ⋙ sv) (cr : sw ⋙ lrB ⟶ lrA ⋙ su)
    (di : iA ⋙ sz ⟶ sw ⋙ iB) (dk : kA ⋙ sv ⟶ su ⋙ kB)
    (ta : iA ⋙ lpA ⟶ lrA ⋙ kA) (tb : iB ⋙ lpB ⟶ lrB ⋙ kB)
    (hc : ∀ N, cp.app (iA.obj N) ≫ sv.map (ta.app N) ≫ dk.app (lrA.obj N) =
      lpB.map (di.app N) ≫ tb.app (sw.obj N) ≫ kB.map (cr.app N))
    (M : UA) :
    sz.map (apA.homEquiv _ _ (ta.app (rrA.obj M) ≫ kA.map (arA.counit.app M))) ≫
        (mateEquiv apA apB (TwoSquare.mk _ _ _ _ cp)).app (kA.obj M) ≫
        rpB.map (dk.app M) =
      (di.app (rrA.obj M) ≫
        iB.map ((mateEquiv arA arB (TwoSquare.mk _ _ _ _ cr)).app M)) ≫
      apB.homEquiv _ _ (tb.app (rrB.obj (su.obj M)) ≫
        kB.map (arB.counit.app (su.obj M))) := by
  apply refinement_coefficient_mate apA apB cp
  simp only [Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => exact dk.naturality (arA.counit.app M)
  dsimp only [Functor.comp_map]
  slice_lhs 1 3 => exact hc (rrA.obj M)
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    rw [← kB.map_comp, ← mateEquiv_counit arA arB (TwoSquare.mk _ _ _ _ cr) M,
      kB.map_comp]
  slice_lhs 2 3 =>
    exact (tb.naturality ((mateEquiv arA arB (TwoSquare.mk _ _ _ _ cr)).app M)).symm
  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]

private theorem mate_formula
    {U V W Z : Type*} [Category U] [Category V] [Category W] [Category Z]
    {lp : Z ⥤ V} {rp : V ⥤ Z} {lr : W ⥤ U} {rr : U ⥤ W}
    (ap : lp ⊣ rp) (ar : lr ⊣ rr) (i : W ⥤ Z) (k : U ⥤ V)
    (ta : i ⋙ lp ⟶ lr ⋙ k) (M : U) :
    (properOpenMate ap ar i k ta).app M =
    ap.homEquiv _ _ (ta.app (rr.obj M) ≫ k.map (ar.counit.app M)) := by
  simp only [properOpenMate, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]

private theorem proper_open_coefficient_mate_formula
    {UA VA WA ZA UB VB WB ZB : Type*}
    [Category UA] [Category VA] [Category WA] [Category ZA]
    [Category UB] [Category VB] [Category WB] [Category ZB]
    {lpA : ZA ⥤ VA} {rpA : VA ⥤ ZA} {lpB : ZB ⥤ VB} {rpB : VB ⥤ ZB}
    {lrA : WA ⥤ UA} {rrA : UA ⥤ WA} {lrB : WB ⥤ UB} {rrB : UB ⥤ WB}
    (apA : lpA ⊣ rpA) (apB : lpB ⊣ rpB)
    (arA : lrA ⊣ rrA) (arB : lrB ⊣ rrB)
    {su : UA ⥤ UB} {sv : VA ⥤ VB} {sw : WA ⥤ WB} {sz : ZA ⥤ ZB}
    {iA : WA ⥤ ZA} {iB : WB ⥤ ZB} {kA : UA ⥤ VA} {kB : UB ⥤ VB}
    (cp : sz ⋙ lpB ⟶ lpA ⋙ sv) (cr : sw ⋙ lrB ⟶ lrA ⋙ su)
    (di : iA ⋙ sz ⟶ sw ⋙ iB) (dk : kA ⋙ sv ⟶ su ⋙ kB)
    (ta : iA ⋙ lpA ⟶ lrA ⋙ kA) (tb : iB ⋙ lpB ⟶ lrB ⋙ kB)
    (hc : ∀ N, cp.app (iA.obj N) ≫ sv.map (ta.app N) ≫ dk.app (lrA.obj N) =
      lpB.map (di.app N) ≫ tb.app (sw.obj N) ≫ kB.map (cr.app N))
    (M : UA) :
    sz.map ((properOpenMate apA arA iA kA ta).app M) ≫
        (mateEquiv apA apB (TwoSquare.mk _ _ _ _ cp)).app (kA.obj M) ≫
        rpB.map (dk.app M) =
      (di.app (rrA.obj M) ≫
        iB.map ((mateEquiv arA arB (TwoSquare.mk _ _ _ _ cr)).app M)) ≫
      (properOpenMate apB arB iB kB tb).app (su.obj M) := by
  simpa only [mate_formula, Functor.comp_obj, Functor.id_obj] using
    proper_open_coefficient_mate apA apB arA arB cp cr di dk ta tb hc M

private theorem proper_open_coefficient_mate_nattrans
    {UA VA WA ZA UB VB WB ZB : Type*}
    [Category UA] [Category VA] [Category WA] [Category ZA]
    [Category UB] [Category VB] [Category WB] [Category ZB]
    {lpA : ZA ⥤ VA} {rpA : VA ⥤ ZA} {lpB : ZB ⥤ VB} {rpB : VB ⥤ ZB}
    {lrA : WA ⥤ UA} {rrA : UA ⥤ WA} {lrB : WB ⥤ UB} {rrB : UB ⥤ WB}
    (apA : lpA ⊣ rpA) (apB : lpB ⊣ rpB)
    (arA : lrA ⊣ rrA) (arB : lrB ⊣ rrB)
    {su : UA ⥤ UB} {sv : VA ⥤ VB} {sw : WA ⥤ WB} {sz : ZA ⥤ ZB}
    {iA : WA ⥤ ZA} {iB : WB ⥤ ZB} {kA : UA ⥤ VA} {kB : UB ⥤ VB}
    (cp : sz ⋙ lpB ⟶ lpA ⋙ sv) (cr : sw ⋙ lrB ⟶ lrA ⋙ su)
    (di : iA ⋙ sz ⟶ sw ⋙ iB) (dk : kA ⋙ sv ⟶ su ⋙ kB)
    (ta : iA ⋙ lpA ⟶ lrA ⋙ kA) (tb : iB ⋙ lpB ⟶ lrB ⋙ kB)
    (hc : PullbackCompatibility cp cr di dk ta tb) :
    properOpenLeft apA apB arA arB cp cr di dk ta tb =
      properOpenRight apA apB arA arB cp cr di dk ta tb := by
  unfold properOpenLeft properOpenRight
  apply NatTrans.ext
  funext M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj]
  simpa only [Category.assoc] using
    proper_open_coefficient_mate_formula apA apB arA arB cp cr di dk ta tb hc.equation M

open CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization SheafOfModules.RingedRefinement

/-- The proper mate is the actual unit, clopen-map, counit composite. The left
proper map is arbitrary; neither this map nor a coefficient mate is inverted.
Source: Stacks 0F7B and 07A6
(blueprint: lem-pur-ringed-proper-open-coefficient-square). -/
def gamma {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) (R : Rings m T) :
    (o.operation r R).right ⋙ o.shriek i R ⟶
      o.shriek k R ⋙ (o.operation p R).right :=
  properOpenMate (o.operation p R).derivedAdjunction
    (o.operation r R).derivedAdjunction (o.shriek i R) (o.shriek k R)
    (t e k r p i d R)

/-- The left side of the coefficient square, as a natural transformation on the
whole ordinary derived category of module sheaves (also in sequence mode).
Source: Stacks 0F7B, agent coefficient identity
(blueprint: lem-pur-ringed-proper-open-coefficient-square). -/
def left {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) {A B : Rings m T} (a : A ⟶ B) :
    (o.operation r A).right ⋙ o.shriek i A ⋙ (o.scalar Z a).T ⟶
      (o.scalar U a).T ⋙ o.shriek k B ⋙ (o.operation p B).right :=
  properOpenLeft
    (UA := category c U A) (VA := category c V A)
    (WA := category c W A) (ZA := category c Z A)
    (UB := category c U B) (VB := category c V B)
    (WB := category c W B) (ZB := category c Z B)
    (lpA := (o.operation p A).left) (rpA := (o.operation p A).right)
    (lpB := (o.operation p B).left) (rpB := (o.operation p B).right)
    (lrA := (o.operation r A).left) (rrA := (o.operation r A).right)
    (lrB := (o.operation r B).left) (rrB := (o.operation r B).right)
    (su := (o.scalar U a).T) (sv := (o.scalar V a).T)
    (sw := (o.scalar W a).T) (sz := (o.scalar Z a).T)
    (iA := o.shriek i A) (iB := o.shriek i B)
    (kA := o.shriek k A) (kB := o.shriek k B)
    (o.operation p A).derivedAdjunction (o.operation p B).derivedAdjunction
    (o.operation r A).derivedAdjunction (o.operation r B).derivedAdjunction
    (sc.pull p a).hom (sc.pull r a).hom (sc.delta i a).hom (sc.delta k a).hom
    (t e k r p i d A) (t e k r p i d B)

/-- The right side: open coefficient comparison, coefficient mate for r, then
Gamma for B. The coefficient mate is the recorded counit transpose of lambda.
Source: Stacks 0F7B and 07A6, agent coefficient identity
(blueprint: lem-pur-ringed-proper-open-coefficient-square). -/
def right {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    (sc : ScalarComparisons o) {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) {A B : Rings m T} (a : A ⟶ B) :
    (o.operation r A).right ⋙ o.shriek i A ⋙ (o.scalar Z a).T ⟶
      (o.scalar U a).T ⋙ o.shriek k B ⋙ (o.operation p B).right :=
  properOpenRight
    (UA := category c U A) (VA := category c V A)
    (WA := category c W A) (ZA := category c Z A)
    (UB := category c U B) (VB := category c V B)
    (WB := category c W B) (ZB := category c Z B)
    (lpA := (o.operation p A).left) (rpA := (o.operation p A).right)
    (lpB := (o.operation p B).left) (rpB := (o.operation p B).right)
    (lrA := (o.operation r A).left) (rrA := (o.operation r A).right)
    (lrB := (o.operation r B).left) (rrB := (o.operation r B).right)
    (su := (o.scalar U a).T) (sv := (o.scalar V a).T)
    (sw := (o.scalar W a).T) (sz := (o.scalar Z a).T)
    (iA := o.shriek i A) (iB := o.shriek i B)
    (kA := o.shriek k A) (kB := o.shriek k B)
    (o.operation p A).derivedAdjunction (o.operation p B).derivedAdjunction
    (o.operation r A).derivedAdjunction (o.operation r B).derivedAdjunction
    (sc.pull p a).hom (sc.pull r a).hom (sc.delta i a).hom (sc.delta k a).hom
    (t e k r p i d A) (t e k r p i d B)

private theorem factorization_exists {T : Scheme.{u}} {U V W Z : Over T}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    [QuasiCompact k.left] [QuasiCompact i.left] [IsProper r.left] [IsProper p.left]
    (h : k ≫ p = r ≫ i) : Nonempty (Factorization k r p i) := by
  let h' : k.left ≫ p.left = r.left ≫ i.left := congrArg (fun a ↦ a.left) h
  let P := Limits.pullback p.left i.left
  let b : P ⟶ V.left := pullback.fst _ _
  let q : P ⟶ W.left := pullback.snd _ _
  let s := ProEtale.StrictTower.squareLift k.left r.left p.left i.left h'
  have hb : b ≫ V.hom = q ≫ W.hom := by
    rw [← Over.w p, ← Category.assoc, pullback.condition, Category.assoc, Over.w i]
  let H : Over T := Over.mk (b ≫ V.hom)
  let b' : H ⟶ V := Over.homMk b
  let q' : H ⟶ W := Over.homMk q hb.symm
  have hsb : s ≫ b = k.left := pullback.lift_fst _ _ _
  let s' : U ⟶ H := Over.homMk s (by simp [H, ← Category.assoc, hsb])
  obtain ⟨hsopen, hsclosed, _, hsq, _⟩ :=
    ProEtale.StrictTower.properOpen_clopen_geometry k.left r.left p.left i.left h'
  have : IsOpenImmersion s := hsopen
  have : IsClosedImmersion s := hsclosed
  refine ⟨{ H := H
            b := b'
            q := q'
            s := s'
            pullback := ?_
            schemePullback := IsPullback.of_hasPullback _ _
            sb := ?_
            sq := ?_
            b_open := (inferInstance : IsOpenImmersion (pullback.fst p.left i.left))
            s_open := hsopen
            clopen := ?_ }⟩
  · have comm : b' ≫ p = q' ≫ i := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    refine ⟨⟨comm⟩, ⟨?_⟩⟩
    refine PullbackCone.IsLimit.mk comm (fun t ↦
      Over.homMk (pullback.lift t.fst.left t.snd.left
        (congrArg (fun a ↦ a.left) t.condition)) ?_) ?_ ?_ ?_
    · change pullback.lift _ _ _ ≫ (b ≫ V.hom) = t.pt.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w t.fst
    · intro t
      apply Over.OverMorphism.ext
      exact pullback.lift_fst t.fst.left t.snd.left _
    · intro t
      apply Over.OverMorphism.ext
      exact pullback.lift_snd t.fst.left t.snd.left _
    · intro t a ha hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext (f := p.left) (g := i.left)
      · exact (congrArg (fun a ↦ a.left) ha).trans
          (pullback.lift_fst (f := p.left) (g := i.left) t.fst.left t.snd.left _).symm
      · exact (congrArg (fun a ↦ a.left) hb).trans
          (pullback.lift_snd (f := p.left) (g := i.left) t.fst.left t.snd.left _).symm
  · apply Over.OverMorphism.ext
    exact hsb
  · apply Over.OverMorphism.ext
    exact hsq
  · exact ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩

set_option backward.isDefEq.respectTransparency true

private theorem square_of_pullback {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} {o : Calculus c} (sc : ScalarComparisons o)
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) {A B : Rings m T} (a : A ⟶ B) :
    left sc e k r p i d a = right sc e k r p i d a := by
  unfold left right
  exact proper_open_coefficient_mate_nattrans
    (UA := category c U A) (VA := category c V A)
    (WA := category c W A) (ZA := category c Z A)
    (UB := category c U B) (VB := category c V B)
    (WB := category c W B) (ZB := category c Z B)
    (lpA := (o.operation p A).left) (rpA := (o.operation p A).right)
    (lpB := (o.operation p B).left) (rpB := (o.operation p B).right)
    (lrA := (o.operation r A).left) (rrA := (o.operation r A).right)
    (lrB := (o.operation r B).left) (rrB := (o.operation r B).right)
    (su := (o.scalar U a).T) (sv := (o.scalar V a).T)
    (sw := (o.scalar W a).T) (sz := (o.scalar Z a).T)
    (iA := o.shriek i A) (iB := o.shriek i B)
    (kA := o.shriek k A) (kB := o.shriek k B)
    (o.operation p A).derivedAdjunction (o.operation p B).derivedAdjunction
    (o.operation r A).derivedAdjunction (o.operation r B).derivedAdjunction
    (sc.pull p a).hom (sc.pull r a).hom (sc.delta i a).hom (sc.delta k a).hom
    (t e k r p i d A) (t e k r p i d B)
    (clopenPullback_coefficients sc e k r p i d a)

/-- Arbitrary ring-sheaf coefficient change preserves the clopen-normalized proper/open
mate, naturally on the entire ordinary unbounded derived category.
Source: Stacks 0F7B (fixed-ring construction), agent coefficient-change supplement
(blueprint: lem-pur-ringed-proper-open-coefficient-square).

Proof:
1. Proper/open geometry makes the canonical lift into the fibre product clopen.
   Ringed clopen module gluing splits modules into the open and complementary
   factors. Apply it on the vertical site itself for systems; exact localization
   and product localization give the derived product decomposition. Hence pi is
   (identity, zero), and maps from b_!F to k_!G are determined by restriction to U.
2. On flat-term K-flat representatives, geometric and coefficient pullbacks preserve
   the resolving classes. The cochain pullback/tensor comparison and compositors
   send each local tensor b tensor x to itself. Localization descends their
   balancing cocycle, including pk=ir, bs=k and qs=r.
3. Restrict both routes of delta_k S(t_A) lambda_p =
   k_!(lambda_r) t_B p_B^*(delta_i) to U. Open-unit normalization makes beta,
   delta and the clopen projector identities there. The two routes are the
   balancing cocycle from Step 2. The restriction bijection of Step 1 proves
   their equality, including the zero complementary component.
4. Transpose the desired coefficient square under p_B^* adjoint to Rp_*,B.
   The adjunct-counit identity replaces the transpose of chi_v by
   S(epsilon_v,A) lambda_v. The actual gamma formula replaces
   epsilon_p,D p_D^*(Gamma_D) by k_!(epsilon_r,D) t_D.
   Naturality moves lambda_p and delta_k through these maps.
5. Apply Step 3 with N=Rr_*,A M. Both transposes become
   k_!,B(S_U(epsilon_r,A) lambda_r) t_B p_B^*(delta_i).
   Counit naturality gives the same word for the right route, so injectivity
   of the adjunction bijection proves equality. All maps are natural
   transformations on the chosen site. No evaluation, total limit, flatness,
   boundedness, constructibility, cartesianness or inversion of chi or Gamma
   enters this calculation. -/
theorem ringedProperOpenCoefficientSquare (m : Mode) (T : Scheme.{u}) :
    ∃ (c : Coefficients m T) (o : Calculus c) (sp : Spatial o)
      (sc : ScalarComparisons o) (e : OpenComparisons sp),
      ∀ {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k.left] [IsOpenImmersion i.left]
        [QuasiCompact k.left] [QuasiCompact i.left] [IsProper r.left] [IsProper p.left]
        (_h : k ≫ p = r ≫ i),
        ∃ d : Factorization k r p i,
          ∀ {A B : Rings m T} (a : A ⟶ B),
            left sc e k r p i d a = right sc e k r p i d a := by
  obtain ⟨o, sp, sc, ⟨ac⟩⟩ := ringedRefinementCore m T
  obtain ⟨e, _, _, _⟩ := ringedRefinementClopen o sp sc ac
  refine ⟨canonicalCoefficients m T, o, sp, sc, e, ?_⟩
  intro U V W Z k r p i _ _ _ _ _ _ h
  obtain ⟨d⟩ := factorization_exists k r p i h
  exact ⟨d, fun a ↦ square_of_pullback sc e k r p i d a⟩

end SheafOfModules.RingedProperOpen
