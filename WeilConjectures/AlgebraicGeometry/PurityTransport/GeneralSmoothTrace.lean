/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic

/-! # General-field smooth trace interfaces

Source: current blueprint `sk-def-sp-trace` and `det-sp-trace-basic`
(blueprint: sk-def-sp-trace).

The constructions below use arbitrary fields of characteristic different from the
coefficient prime.  They retain the native condensed coefficient objects and the
compact-support and derived-module functors from the existing interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

variable (ell : ℕ) [Fact ell.Prime]

/-- A smooth separated finite-type morphism over an arbitrary field.
Source: current blueprint `sk-def-sp-trace` (blueprint: sk-def-sp-trace). -/
structure GeneralSmoothDatum (k : Type u) [Field k]
where
  X : Over (Spec (.of k))
  Y : Over (Spec (.of k))
  [xFinite : LocallyOfFiniteType X.hom]
  [xQuasiCompact : QuasiCompact X.hom]
  [xSeparated : IsSeparated X.hom]
  [yFinite : LocallyOfFiniteType Y.hom]
  [yQuasiCompact : QuasiCompact Y.hom]
  [ySeparated : IsSeparated Y.hom]
  map : X.left ⟶ Y.left
  [isOver : map.IsOver (Spec (.of k))]
  [separated : IsSeparated map]
  [finiteType : LocallyOfFiniteType map]
  [quasiCompact : QuasiCompact map]
  dim : ℕ
  [smooth : SmoothOfRelativeDimension dim map]
  compactification : Compactification map

attribute [instance] GeneralSmoothDatum.xFinite GeneralSmoothDatum.xQuasiCompact
  GeneralSmoothDatum.xSeparated GeneralSmoothDatum.yFinite
  GeneralSmoothDatum.yQuasiCompact GeneralSmoothDatum.ySeparated
  GeneralSmoothDatum.isOver GeneralSmoothDatum.separated
  GeneralSmoothDatum.finiteType GeneralSmoothDatum.quasiCompact
  GeneralSmoothDatum.smooth

/-- The restricted exceptional adjunction for a general-field smooth morphism.
Source: `sk-def-sp-trace` (blueprint: sk-def-sp-trace). -/
structure GeneralExplicitAdjunction (k : Type u) [Field k]
    (c : Coefficient ell) (s : GeneralSmoothDatum k) where
  support_closed : ∀ K, property ell c s.X.left K → property ell c s.Y.left
    ((CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj K)
  source_closed : ∀ K, property ell c s.Y.left K → property ell c s.X.left
    ((c.smoothSource ell s.map s.dim).obj K)
  adjunction : support ell c s.compactification support_closed ⊣
    source ell c s.map s.dim source_closed

/-- The counit component of an explicit smooth adjunction. When the input
belongs to a family satisfying `GeneralPurityTransport`, its Brown counit
equation identifies this with the normalized purity composite.
Source: the displayed trace composite in `sk-def-sp-trace`
(blueprint: sk-def-sp-trace). -/
def generalSmoothTrace {k : Type u} [Field k]
    {c : Coefficient ell} {s : GeneralSmoothDatum k}
    (a : GeneralExplicitAdjunction ell k c s)
    (K : c.ctf ell s.Y.left) :=
  (a.adjunction.counit.app K).hom

/-- A family of general-field smooth adjunctions.
Source: current blueprint `sk-def-sp-trace` (blueprint: sk-def-sp-trace). -/
abbrev GeneralAdjunctionFamily (k : Type u) [Field k] :=
  ∀ (c : Coefficient ell) (s : GeneralSmoothDatum k),
    GeneralExplicitAdjunction ell k c s

/-- Literal Cartesian base change of a general-field smooth datum, retaining the
specified compactification.  Source: smooth-purity base change
(blueprint: sk-thm-purity-transport). -/
def GeneralSmoothDatum.baseChange {k : Type u} [Field k]
    (s : GeneralSmoothDatum k) (Y' : Over (Spec (.of k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of k))] : GeneralSmoothDatum k := by
  let f' := pullback.snd s.map v
  letI : (pullback s.map v).Over (Spec (.of k)) :=
    ⟨f' ≫ (Y'.left ↘ Spec (.of k))⟩
  letI : f'.IsOver (Spec (.of k)) := ⟨rfl⟩
  let X' : Over (Spec (.of k)) := Over.mk (f' ≫ Y'.hom)
  letI : LocallyOfFiniteType X'.hom := by
    change LocallyOfFiniteType (f' ≫ Y'.hom)
    infer_instance
  letI : QuasiCompact X'.hom := by
    change QuasiCompact (f' ≫ Y'.hom)
    infer_instance
  letI : IsSeparated X'.hom := by
    change IsSeparated (f' ≫ Y'.hom)
    infer_instance
  exact
    { X := X'
      Y := Y'
      map := f'
      dim := s.dim
      compactification := s.compactification.baseChange v }

/-- Composition datum used by the general composition compatibility clause.
Source: smooth-purity composition (blueprint: sk-thm-purity-transport). -/
def GeneralSmoothDatum.comp {k : Type u} [Field k]
    (s : GeneralSmoothDatum k) (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)) :
    GeneralSmoothDatum k :=
  { X := s.X
    Y := Z
    map := s.map ≫ g
    dim := s.dim + e
    compactification := compositeCompactification s.compactification cg cr }

/-- The Brown comparison and its counit-compatible purity isomorphism for a
general-field smooth datum, quantified over every specified localizing
adjunction. This is the counit equation; the additional scalar, geometric and
affine-line conditions in `GeneralPurityTransport` fix the normalization of the
family. Source: `sk-def-sp-trace` and the Brown comparison
clause of `sk-thm-purity-transport` (blueprint: sk-def-sp-trace). -/
def GeneralBrownComparison {k : Type u} [Field k]
    (a : GeneralAdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : GeneralSmoothDatum k)
    (hL : ∀ K, localizing ell c s.X.left K → localizing ell c s.Y.left
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (c.obj ell) s.compactification).obj K))
    (G : (localizing ell c s.Y.left).FullSubcategory ⥤
      (localizing ell c s.X.left).FullSubcategory)
    (b : (localizing ell c s.Y.left).lift
      ((localizing ell c s.X.left).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification)
      (fun K ↦ hL K.obj K.property) ⊣ G),
    ∃ hG : ∀ K : c.ctf ell s.Y.left,
      property ell c s.X.left (G.obj ((inclusion ell c s.Y.left).obj K)).obj,
    ∃ bctf : support ell c s.compactification (a c s).support_closed ⊣ exceptional ell c G hG,
      (∀ K : c.ctf ell s.Y.left,
        HEq (bctf.counit.app K).hom
          (b.counit.app ((inclusion ell c s.Y.left).obj K)).hom) ∧
      ∃! gamma : source ell c s.map s.dim (a c s).source_closed ≅ exceptional ell c G hG,
        CounitCompatible (a c s).adjunction bctf gamma

/-- Naturality of the general-field smooth trace.
Source: det-sp-trace-basic, clause (1) (blueprint: det-sp-trace-basic). -/
def GeneralTraceNaturality {k : Type u} [Field k]
    (a : GeneralAdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : GeneralSmoothDatum k)
    (K L : c.ctf ell s.Y.left) (v : K ⟶ L),
    (source ell c s.map s.dim (a c s).source_closed ⋙
      support ell c s.compactification (a c s).support_closed).map v ≫
        (a c s).adjunction.counit.app L =
      (a c s).adjunction.counit.app K ≫ (𝟭 _).map v

/-- The affine projection regarded as a `GeneralSmoothDatum`; this is the
general-field counterpart of `traceAffineDatum`.
Source: the affine projection in clause (2) (blueprint: det-sp-trace-basic). -/
def generalTraceAffineDatum (k : Type u) [Field k]
    (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj Y.left d)) : GeneralSmoothDatum k :=
  letI : (iteratedAffineLine Y.left d).Over (Spec (.of k)) :=
    ⟨iteratedAffineLineProj Y.left d ≫ Y.hom⟩
  letI : (iteratedAffineLineProj Y.left d).IsOver (Spec (.of k)) := ⟨rfl⟩
  letI := WeilConjectures.PurityFiniteSetting.projection_smooth Y.left d
  let X : Over (Spec (.of k)) := Over.mk (iteratedAffineLineProj Y.left d ≫ Y.hom)
  letI : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (iteratedAffineLineProj Y.left d ≫ Y.hom))
  letI : QuasiCompact X.hom :=
    inferInstanceAs (QuasiCompact (iteratedAffineLineProj Y.left d ≫ Y.hom))
  letI : IsSeparated X.hom :=
    inferInstanceAs (IsSeparated (iteratedAffineLineProj Y.left d ≫ Y.hom))
  { X := X
    Y := Y
    map := iteratedAffineLineProj Y.left d
    dim := d
    compactification := cf }

/-- The coefficient-unit endomorphism used in affine integration, with the
general-field smooth trace supplied by `a`.
Source: the origin and coordinate products in clause (2)
(blueprint: det-sp-trace-basic). -/
def generalTraceAffineValue (k : Type u) [Field k]
    (a : GeneralAdjunctionFamily ell k) (C : TraceCartierFamily.{u} ell) (negative : Bool)
    (c : Coefficient ell) (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj Y.left d))
    (hi : ∀ x : iteratedAffineLine Y.left d,
      Invertible (ell : (iteratedAffineLine Y.left d).residueField x))
    (hT : IsUnit (ell : Γ(iteratedAffineLine Y.left d, ⊤)))
    (hu : property ell c Y.left (unit ell c Y.left))
    (α : traceProductSource ell c Y.left d (List.finRange d) ≅
      (actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj (unit ell c Y.left))
    (β : unit ell c Y.left ≅
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).obj
        ((actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj
          (unit ell c Y.left))) : unit ell c Y.left ⟶ unit ell c Y.left :=
  β.hom ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).map
      (α.inv ≫ @traceProductMap ell inferInstance C negative c Y.left d hi hT
        (List.finRange d) ≫
        (eqToIso (congrArg (c.derivedLine ell (iteratedAffineLine Y.left d))
          (List.length_finRange (n := d)))).hom ≫
        (sourceUnit ell c (iteratedAffineLineProj Y.left d) d).inv) ≫
    generalSmoothTrace ell (a c (generalTraceAffineDatum k Y d cf)) ⟨_, hu⟩

/-- The affine-space normalization predicate for a general-field trace family.
Source: det-sp-trace-basic, clause (2) (blueprint: det-sp-trace-basic). -/
def GeneralTraceAffine {k : Type u} [Field k]
    (a : GeneralAdjunctionFamily ell k) (C : TraceCartierFamily.{u} ell) : Prop :=
  ∀ (c : Coefficient ell) (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj Y.left d)),
    ∃ (hi : ∀ x : iteratedAffineLine Y.left d,
        Invertible (ell : (iteratedAffineLine Y.left d).residueField x))
      (hT : IsUnit (ell : Γ(iteratedAffineLine Y.left d, ⊤)))
      (hu : property ell c Y.left (unit ell c Y.left))
      (α : traceProductSource ell c Y.left d (List.finRange d) ≅
        (actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj
          (unit ell c Y.left))
      (β : unit ell c Y.left ≅
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).obj
          ((actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj
            (unit ell c Y.left))),
      traceProductUnit ell c Y.left d (List.finRange d) ≫ α.hom =
        traceSupportedUnit ell c (AffineZeroPurity.zero Y.left d) ∧
      β.inv = traceOriginSupport ell c Y.left d cf ∧
      generalTraceAffineValue ell k a C false c Y d cf hi hT hu α β = 𝟙 _ ∧
      generalTraceAffineValue ell k a C true c Y d cf hi hT hu α β = (-1 : ℤ) ^ d • 𝟙 _

/-- The finite-etale fibre-summation predicate for a general-field trace family.
Source: det-sp-trace-basic, clause (3) (blueprint: det-sp-trace-basic). -/
def GeneralTraceFiniteEtale {k : Type u} [Field k]
    (a : GeneralAdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : GeneralSmoothDatum k)
    [IsFinite s.map] [Etale s.map] (_hzero : s.dim = 0),
    ∃ b : CondensedRing.lowerStar (c.obj.{u} ell) s.map ⊣
      CondensedRing.upperStar (c.obj.{u} ell) s.map,
      (∀ P, FiniteEtaleTraceFormula (c.obj.{u} ell) s.map P (b.counit.app P)) ∧
      (∀ K : c.derived ell s.X.left,
        IsIso (traceShriekToStar ell c s.compactification K)) ∧
      ∀ K : c.ctf ell s.Y.left,
        generalSmoothTrace ell (a c s) K =
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj.{u} ell) s.compactification).map
              ((eqToIso (congrArg (fun d ↦ (c.smoothSource ell s.map d).obj K.obj)
                _hzero)).hom ≫ (traceSourceZero ell c s.map K.obj).hom) ≫
          traceShriekToStar ell c s.compactification
            ((actualPull (c.obj.{u} ell) s.map).obj K.obj) ≫
          traceDerivedFiniteSum ell c s.map b K.obj

/-- Change of coefficients for the very same smooth counits. The left arrow is
proper direct-image mate after open extension, and the source arrow is the
normalized scalar/pullback/tensor comparison, also for nonflat finite maps.
Source: coefficient compatibility (blueprint: sk-thm-purity-transport). -/
def GeneralScalarCompatible {k : Type u} [Field k]
    (b : GeneralAdjunctionFamily ell k) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∀ s : GeneralSmoothDatum k,
    ∃ p : ScalarLineCoordinates ell a ha s.X.left,
    ∀ K : c.ctf ell s.Y.left,
    ∃ hK : property ell c' s.Y.left ((scalarSixChange a s.Y.left).obj K.obj),
      (scalarSixChange a s.Y.left).map (generalSmoothTrace ell (b c s) K) =
        (scalarSupportMap a s.compactification).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              (sourceScalar ell a s.map s.dim ha p K.obj) ≫
          generalSmoothTrace ell (b c' s) ⟨_, hK⟩

/-- Base change of the same counit through the canonical proper/open exchange.
The normalized open comparison has inverse the recorded open base-change arrow.
Source: smooth-purity base change (blueprint: sk-thm-purity-transport). -/
def GeneralBaseChangeCompatible {k : Type u} [Field k]
    (a : GeneralAdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : GeneralSmoothDatum k)
    (Y' : Over (Spec (.of k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of k))],
    ∃ p : LinePullCoordinates ell c (pullback.fst s.map v),
    ∃ o :
      (actualOpen (c.obj ell) s.compactification.i) ⋙
        (actualPull (c.obj ell)
          (pullback.fst s.compactification.g v)) ≅
      (actualPull (c.obj ell) (pullback.fst s.map v)) ⋙
        (actualOpen (c.obj ell)
          (s.compactification.baseChange v).i),
    o.inv =
      ((fun (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          [MonObj R] [IsCommMonObj R] ↦
       let cf := s.compactification
       let h := pullback.fst s.map v
       let k := pullback.fst cf.g v
       let L := (actualOpen R cf.i)
       let L' :=
         (actualOpen R (cf.baseChange v).i)
       let U := (actualPull R h)
       let V := (actualPull R k)
       let sq := cf.isPullback_i_ofIsPullback (IsPullback.of_hasPullback s.map v)
       let theta := CondensedRing.condensedAmbientPullbackComparison R
         { toCommSq := sq.toCommSq
           isoPullback := sq.isoPullback
           hom_fst := sq.isoPullback_hom_fst
           hom_snd := sq.isoPullback_hom_snd }
       (Functor.leftUnitor _).inv ≫
         Functor.whiskerRight
           (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R cf.i).unit
           (U ⋙ L') ≫
         (Functor.squareTransport L L'
           (Functor.isoWhiskerRight
               (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R cf.i).symm U ≪≫
             theta.symm ≪≫
             Functor.isoWhiskerLeft V
               (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R
                 (cf.baseChange v).i))).hom ≫
         Functor.whiskerLeft (L ⋙ V)
           (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R
             (cf.baseChange v).i).counit ≫
         (Functor.rightUnitor _).hom) (c.obj ell)) ∧
    ∀ K : c.ctf ell s.Y.left,
      ∃ hK : property ell c Y'.left
        ((actualPull (c.obj ell) v).obj K.obj),
      (actualPull (c.obj ell) v).map (generalSmoothTrace ell (a c s) K) =
        (CondensedRing.condensedAmbientExchange (c.obj ell)
          { toCommSq := ⟨pullback.condition⟩
            isoPullback := Iso.refl _
            hom_fst := Category.id_comp _
            hom_snd := Category.id_comp _ }).app
              ((CondensedRing.openImmersionLowerShriek
                (c.obj ell) s.compactification.i).mapDerivedCategory.obj
                  ((c.smoothSource ell s.map s.dim).obj K.obj)) ≫
          (actualPush (c.obj ell)
            (pullback.snd s.compactification.g v)).map
              (o.hom.app ((c.smoothSource ell s.map s.dim).obj K.obj)) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) (s.compactification.baseChange v)).map
              (sourceBaseChange ell c s.map v s.dim p K.obj).hom ≫
          generalSmoothTrace ell (a c (s.baseChange Y' v)) ⟨_, hK⟩

/-- Composition of the same smooth counits, on the specified proper/open model.
The interchange is fixed by its restriction equation. Quantifying over every such
interchange expresses the canonical compositor without selecting an unrelated map.
Source: smooth trace composition (blueprint: sk-thm-purity-transport). -/
def GeneralCompositionCompatible {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (a : GeneralAdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : GeneralSmoothDatum k)
    (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)),
    letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
      fun x ↦ (by
        simpa using ((CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime)
          (Fact.out : ringChar k ≠ ell)).isUnit).map
          ((s.X.left ↘ Spec (.of k)).residueFieldAlgebraMap x) :
            IsUnit (ell : s.X.left.residueField x)).invertible
    let t : GeneralSmoothDatum k :=
      { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }
    ∃ p : LinePullCoordinates ell c s.map,
    ∀ (K : c.ctf ell Z.left)
      (m : (actualOpen (c.obj ell) cg.i).obj
        ((actualPush (c.obj ell) s.compactification.g).obj
          ((CondensedRing.openImmersionLowerShriek
            (c.obj ell) s.compactification.i).mapDerivedCategory.obj
            ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj))) ⟶
        (actualPush (c.obj ell) cr.obj.obj.g).obj
          ((actualOpen (c.obj ell) cr.obj.obj.i).obj
            ((CondensedRing.openImmersionLowerShriek
            (c.obj ell) s.compactification.i).mapDerivedCategory.obj
              ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj))))
      (_hm :
        let R := c.obj ell
        letI : MonObj R := inferInstance
        letI : IsCommMonObj R := inferInstance
        let q := s.compactification.g
        let i := cg.i
        let j := cr.obj.obj.i
        let r := cr.obj.obj.g
        let A := (CondensedRing.openImmersionLowerShriek R s.compactification.i)
          |>.mapDerivedCategory.obj ((c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K.obj)
        let B := (actualOpen R j).obj A
        let theta :=
          (Functor.mapDerivedCategoryCompIso
            (CondensedRing.upperStar R i) (CondensedRing.upperStar R q)).symm ≪≫
          Functor.mapDerivedCategoryNatIso
            ((CondensedRing.upperStarComp R q i).symm ≪≫
              eqToIso (congrArg (CondensedRing.upperStar R) cr.obj.obj.comm) ≪≫
              CondensedRing.upperStarComp R j r) ≪≫
          Functor.mapDerivedCategoryCompIso
            (CondensedRing.upperStar R r) (CondensedRing.upperStar R j)
        let rho :=
          ((CondensedRing.derivedUpperStarLowerStarAdjunction R q).ofNatIsoLeft
            (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R q)).homEquiv _ _
              (theta.hom.app ((actualPush R r).obj B) ≫
                (CondensedRing.upperStar R j).mapDerivedCategory.map
                  (((CondensedRing.derivedUpperStarLowerStarAdjunction R r).ofNatIsoLeft
                    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R r)).counit.app B))
        (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R i).homEquiv
            _ _ m ≫ rho =
          (actualPush R q).map
            ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction R j).unit.app A)),
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification).map
              (sourceComp ell c s.map g s.dim e p K.obj).hom) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          (generalSmoothTrace ell (a c s)
            ⟨(c.smoothSource ell g e).obj K.obj, (a c t).source_closed K.obj K.property⟩) ≫
        generalSmoothTrace ell (a c t) K =
      supportComp (c.obj ell)
          s.compactification cg cr _ m ≫
        generalSmoothTrace ell (a c (s.comp Z g e cg cr)) K

/-- The actual affine-line projection with its standard projective compactification.
Source: affine-line normalization (blueprint: sk-thm-purity-transport). -/
def generalAffineDatum (k : Type u) [Field k]
    (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] : GeneralSmoothDatum k := by
  let p := AffineSpace PUnit.{u + 1} Y.left ↘ Y.left
  letI : (AffineSpace PUnit.{u + 1} Y.left).Over (Spec (.of k)) := ⟨p ≫ Y.hom⟩
  letI : p.IsOver (Spec (.of k)) := ⟨rfl⟩
  let X : Over (Spec (.of k)) := Over.mk (p ≫ Y.hom)
  letI : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (p ≫ Y.hom)
    infer_instance
  letI : QuasiCompact X.hom := by
    change QuasiCompact (p ≫ Y.hom)
    infer_instance
  letI : IsSeparated X.hom := by
    change IsSeparated (p ≫ Y.hom)
    infer_instance
  letI : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_unique] using
      AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} Y.left
  exact
    { X := X
      Y := Y
      map := p
      dim := 1
      compactification := affineTraceLineCompactification Y.left }

end AlgebraicGeometry.ProEtale.PurityTransport
