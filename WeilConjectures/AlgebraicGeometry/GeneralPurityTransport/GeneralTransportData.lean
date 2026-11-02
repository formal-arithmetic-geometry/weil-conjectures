/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction

/-! # Smooth purity transport over finite or algebraically closed fields

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Step 3 and the final compatibility paragraph.
(blueprint: def-pur-general-transport-data).

The published coefficients, categories, Tate lines, operation comparisons and
integration maps are reused. Only the geometric indices and their predicates
are generalized from a finite-field datum to a field supplied by the caller.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport

/-- A smooth morphism in the recorded separated finite-type geometric domain,
with its compactification and relative dimension displayed.
Source: sk-def-sfb-dc-setting, standing separated finite-type setting
(blueprint: def-pur-general-transport-data). -/
structure SmoothDatum (k : Type u) [Field k] where
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

attribute [instance] SmoothDatum.xFinite SmoothDatum.xQuasiCompact SmoothDatum.xSeparated
  SmoothDatum.yFinite SmoothDatum.yQuasiCompact SmoothDatum.ySeparated
  SmoothDatum.isOver SmoothDatum.separated SmoothDatum.finiteType
  SmoothDatum.quasiCompact SmoothDatum.smooth

/-- An explicit restricted adjunction at one geometric index. Its two membership
fields supply only proofs: both functors are the literal operations already recorded.
Source: proof Step 3, the restricted adjunction (blueprint: def-pur-general-transport-data). -/
structure ExplicitAdjunction (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (c : Coefficient ell) (s : SmoothDatum k) where
  support_closed : ∀ K, property ell c s.X.left K → property ell c s.Y.left
    ((CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj K)
  source_closed : ∀ K, property ell c s.Y.left K → property ell c s.X.left
    ((c.smoothSource ell s.map s.dim).obj K)
  adjunction : support ell c s.compactification support_closed ⊣
    source ell c s.map s.dim source_closed

/-- The ambient counit of this same explicit adjunction.
Source: smooth trace (blueprint: def-pur-general-transport-data). -/
def ExplicitAdjunction.trace {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] {c : Coefficient ell} {s : SmoothDatum k}
    (a : ExplicitAdjunction ell k c s) (K : c.ctf ell s.Y.left) :=
  (a.adjunction.counit.app K).hom

variable (ell : ℕ) [Fact ell.Prime]

/-- A family indexed only by smooth separated finite-type morphisms over the
arbitrary field. Source: smooth purity (blueprint: def-pur-general-transport-data). -/
abbrev AdjunctionFamily (k : Type u) [Field k] :=
  ∀ (c : Coefficient ell) (s : SmoothDatum k), ExplicitAdjunction ell k c s

/-- The natural isomorphism with every specified Brown adjoint restriction,
uniquely characterized by its counit equation. The same explicit adjunction from
the family occurs in that equation.
Source: proof Step 3, the counit-preserving comparison
(blueprint: def-pur-general-transport-data). -/
def BrownComparison (k : Type u) [Field k]
    (a : AdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum k)
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

/-- Base change retains the literal fibre product and its recorded compactification.
Source: base-change clause (blueprint: def-pur-general-transport-data). -/
def SmoothDatum.baseChange {k : Type u} [Field k]
    (s : SmoothDatum k) (Y' : Over (Spec (.of k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of k))] : SmoothDatum k := by
  let f' := pullback.snd s.map v
  letI : (pullback s.map v).Over (Spec (.of k)) := ⟨f' ≫ (Y'.left ↘ Spec (.of k))⟩
  letI : f'.IsOver (Spec (.of k)) := ⟨rfl⟩
  let X' : Over (Spec (.of k)) :=
    Over.mk (f' ≫ Y'.hom)
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

/-- Composition retains its specified proper/open compactification model.
Source: composition clause (blueprint: def-pur-general-transport-data). -/
def SmoothDatum.comp {k : Type u} [Field k]
    (s : SmoothDatum k) (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)) :
    SmoothDatum k :=
  { X := s.X
    Y := Z
    map := s.map ≫ g
    dim := s.dim + e
    compactification := compositeCompactification s.compactification cg cr }

/-- The actual affine-line projection with its standard projective compactification.
Source: affine-line normalization (blueprint: def-pur-general-transport-data). -/
def affineDatum (k : Type u) [Field k]
    (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] : SmoothDatum k := by
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

variable (ell : ℕ) [Fact ell.Prime]

/-- Change of coefficients for the very same smooth counits. The left arrow is
proper direct-image mate after open extension, and the source arrow is the
normalized scalar/pullback/tensor comparison, also for nonflat finite maps.
Source: coefficient compatibility (blueprint: def-pur-general-transport-data). -/
def ScalarCompatible (k : Type u) [Field k]
    (b : AdjunctionFamily ell k) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∀ s : SmoothDatum k,
    ∃ p : ScalarLineCoordinates ell a ha s.X.left,
    ∀ K : c.ctf ell s.Y.left,
    ∃ hK : property ell c' s.Y.left ((scalarSixChange a s.Y.left).obj K.obj),
      (scalarSixChange a s.Y.left).map ((b c s).trace K) =
        (scalarSupportMap a s.compactification).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              (sourceScalar ell a s.map s.dim ha p K.obj) ≫
          (b c' s).trace ⟨_, hK⟩

variable (ell : ℕ) [Fact ell.Prime]

/-- Base change of the same counit through the canonical proper/open exchange.
The normalized open comparison has inverse the recorded open base-change arrow.
Source: smooth-purity base change (blueprint: def-pur-general-transport-data). -/
def BaseChangeCompatible (k : Type u) [Field k]
    (a : AdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum k)
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
      (actualPull (c.obj ell) v).map ((a c s).trace K) =
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
          (a c (s.baseChange Y' v)).trace ⟨_, hK⟩

/-- Composition of the same smooth counits, on the specified proper/open model.
The interchange is fixed by its restriction equation. Quantifying over every such
interchange expresses the canonical compositor without selecting an unrelated map.
Source: smooth trace composition (blueprint: def-pur-general-transport-data). -/
def CompositionCompatible (k : Type u) [Field k]
    (hEll : IsUnit (ell : k)) (a : AdjunctionFamily ell k) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum k)
    (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)),
    letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
      fun x ↦ (by
        simpa using hEll.map
          ((s.X.left ↘ Spec (.of k)).residueFieldAlgebraMap x) :
            IsUnit (ell : s.X.left.residueField x)).invertible
    let t : SmoothDatum k :=
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
          ((a c s).trace
            ⟨(c.smoothSource ell g e).obj K.obj, (a c t).source_closed K.obj K.property⟩) ≫
        (a c t).trace K =
      supportComp (c.obj ell)
          s.compactification cg cr _ m ≫
        (a c (s.comp Z g e cg cr)).trace K

variable (ell : ℕ) [Fact ell.Prime]

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
