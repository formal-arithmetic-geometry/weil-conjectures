module

public import Sheaf.Paper.AffineLinePurityComparison
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import Sheaf.Paper.CompactSupportProjectionRightUnit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! # Evaluation of base-changed affine-line integration

Source: main-20261015, sec-smooth-purity/sk-prop-an, Integration paragraph
(blueprint: lem-pur-base-changed-line-trace-evaluation).

The comparison C, its projection-factorization D, and the augmentation b are actual
composites of the canonical compactification exchange, projection and line integration.
The recorded compositor `originComposition` is expressed in the same compactification
coordinates by the canonical changes of compactification.

## Main definitions

* `originChange` and `composition`: alpha in the given compactification coordinates.
* `comparisonC` and `comparisonD`: the two specified projection/exchange composites.
* `trace` and `normalizedPulledTrace`: normalized line integration in these coordinates.
* `TraceCompatible` and `Evaluation`: the displayed trace equation and evaluation equality.

## Main statements

* `baseChangedLineTraceEvaluation`: equality of the two displayed evaluation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.BaseChangedLineTrace
open AffineLinePurity VectorIntegrationSite

attribute [local irreducible] derivedTensor

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Existing fixed-module small pro-etale derived category, only abbreviated.
Source: finite coefficient convention
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
abbrev D (S : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))

/-- The line compactification pulled back along f, on the literal affine-space square.
Source: P = A¹_X, with its specified exchange square
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
abbrev lineCompactification {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (affineTraceLineCompactification Y).ofIsPullback (AffineSpace.isPullback_map f)

variable (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)

/-- The shifted Tate coefficient in the recorded affine-chart coordinates.
Source: T = A(1)[2] and canonical Tate pullback
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
abbrev coefficient (S : Scheme.{u}) : D A (AffineSpace PUnit.{u + 1} S) :=
  (comparison A _).obj ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart S)).obj
    ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))

/-- Canonical Tate coordinate identification, induced by the roots-normalized pullback.
Source: canonical Tate pullback in the node
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def lineCoordinate (S : Scheme.{u}) (hS : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    coefficient A N hA S ≅ (comparison A _).obj
      ((Etale.ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} S))⟦(2 : ℤ)⟧) :=
  comparedLinePullback A N hN hA (ProjectiveLine.affineChart S) hS

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual canonical Tate comparison Lr*T ≅ T_X, with all three pullbacks fixed.
Source: canonical Tate pullback in the node
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def linePullback (hX : IsUnit (N : Γ(ProjectiveLine X, ⊤)))
    (hY : IsUnit (N : Γ(ProjectiveLine Y, ⊤)))
    (hAY : IsUnit (N : Γ(AffineSpace PUnit.{u + 1} Y, ⊤))) :
    (geoP1Pullback A (AffineSpace.map PUnit.{u + 1} f)).obj (coefficient A N hA Y) ≅
      coefficient A N hA X :=
  (geoP1Pullback A (AffineSpace.map PUnit.{u + 1} f)).mapIso
      (lineCoordinate A N hN hA Y hY) ≪≫
    (geoP1PullComparison A (AffineSpace.map PUnit.{u + 1} f)).app _ ≪≫
    comparedLinePullback A N hN hA (AffineSpace.map PUnit.{u + 1} f) hAY ≪≫
    (lineCoordinate A N hN hA X hX).symm

/-- U = Ra_!T on the specified line compactification.
Source: U display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
abbrev lineImage :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (affineTraceLineCompactification Y)).obj (coefficient A N hA Y)

/-- The specified compact-support exchange E at T, not an arbitrary isomorphism.
Source: Ex_! display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def exchange :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
    (AffineSpace.isPullback_map f) (affineTraceLineCompactification Y)).app (coefficient A N hA Y)

/-- Literal Lr*T.
Source: W display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
abbrev pulledLine :=
  (geoP1Pullback A (AffineSpace.map PUnit.{u + 1} f)).obj (coefficient A N hA Y)

/-- W = Lq*M tensor Lr*T, with coefficient-first tensor order.
Source: W display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
abbrev source (M : D A X) : D A (AffineSpace PUnit.{u + 1} X) :=
  projectionSourceObject A (AffineSpace PUnit.{u + 1} X ↘ X) (pulledLine A N hA f) M

/-- The normalized t_X, transported to the base-changed compactification and literal Lr*T.
The input is the actual normalized integration on the standard line over X.
Source: t_X with its canonical Tate identification
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def pulledTrace [QuasiCompact f]
    (hX : IsUnit (N : Γ(ProjectiveLine X, ⊤)))
    (hY : IsUnit (N : Γ(ProjectiveLine Y, ⊤)))
    (hAY : IsUnit (N : Γ(AffineSpace PUnit.{u + 1} Y, ⊤)))
    (tX : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification X)).obj (coefficient A N hA X) ⟶ unit A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (lineCompactification f)).obj (pulledLine A N hA f) ⟶ unit A X :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (lineCompactification f)).map
      ((linePullback A N hN hA f hX hY hAY).hom ≫ (lineCoordinate A N hN hA X hX).hom) ≫
    (rightDerivedLowerShriekOfCompactificationOriginIso A (lineCompactification f)
      (affineTraceLineCompactification X)).hom.app
        ⟨(Etale.ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} X))⟦(2 : ℤ)⟧,
          ⟨-2, _root_.DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩⟩ ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification X)).map (lineCoordinate A N hN hA X hX).inv ≫ tX

/-- The actual proper-counit/open-tensor projection P_U.
Source: P_U display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def projectionU (cf : Compactification f) (M : D A X) :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) cf).app M).app
    (lineImage A N hA (Y := Y))

/-- Canonical change of compactification on a bounded-below etale-origin object:
the upstream etale-origin comparison, evaluated at a representative of the object.
It is natural in the representative, so it does not depend on that choice.
Source: compactification independence of Rf_! in thm-sf-comp-composition
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def originChange {Z S : Scheme.{u}} {g : Z ⟶ S} [QuasiCompact g]
    (c d : Compactification g) (W : D A Z)
    (hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z W) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj W ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj W :=
  let L : _root_.DerivedCategory.Plus _ := ⟨hW.choose, hW.choose_spec.1⟩
  let e := hW.choose_spec.2.some
  ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso e).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationOriginIso A c d).app L ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso e

/-- The normalized compositor alpha of thm-sf-comp-composition (`originComposition`),
written in the three given compactification coordinates by the canonical changes of
compactification. Source: thm-sf-comp-composition, normalized alpha
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def composition {Z : Scheme.{u}} {q : Z ⟶ X} [QuasiCompact q] [QuasiCompact f]
    (cq : Compactification q) (cf : Compactification f) (ch : Compactification (q ≫ f))
    (W : D A Z) (hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z W) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cq).obj W) ≅
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch).obj W :=
  haveI := cq.hasCompactification
  haveI := cf.hasCompactification
  haveI := ch.hasCompactification
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).mapIso
      (originChange A cq (HasCompactification.compactification q) W hW) ≪≫
    originChange A cf (HasCompactification.compactification f) _
      (DerivedCategory.plusEtaleOrigin.rightDerivedLowerShriek_obj q hW) ≪≫
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Y).ι.mapIso
      ((originComposition A q f).app ⟨W, hW⟩) ≪≫
    originChange A (HasCompactification.compactification (q ≫ f)) ch W hW

/-- C: alpha inverse, image of inverse projection, then image of tensor of inverse exchange.
Source: C display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def comparisonC [QuasiCompact f] (cf : Compactification f)
    (ch : Compactification ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ f)) (M : D A X)
    (hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} X) (source A N hA f M))
    [IsIso (exchange A N hA f)]
    (hq : ProjectionInvertible A (lineCompactification f) (pulledLine A N hA f) M) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch).obj
        (source A N hA f M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((geoP1Pullback A f).obj (lineImage A N hA (Y := Y)))) := by
  let e := inverseProjection A (lineCompactification f) (pulledLine A N hA f) M hq
  unfold projectionTargetObject at e
  exact (composition A f (lineCompactification f) cf ch (source A N hA f M) hW).inv ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map e.hom ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map (inv (exchange A N hA f)))

/-- D = C followed by the inverse of the specified P_U.
Source: D display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def comparisonD [QuasiCompact f] (cf : Compactification f)
    (ch : Compactification ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ f)) (M : D A X)
    (hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} X) (source A N hA f M))
    [IsIso (exchange A N hA f)]
    [IsIso (projectionU A N hA f cf M)]
    (hq : ProjectionInvertible A (lineCompactification f) (pulledLine A N hA f) M) :=
  comparisonC A N hA f cf ch M hW hq ≫ inv (projectionU A N hA f cf M)

/-- Compatibility of the actual traces, including the canonical pullback unit map.
Source: Lf* t_Y = t_X E, with suppressed unit identification restored
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
def TraceCompatible
    (tY : lineImage A N hA (Y := Y) ⟶ unit A Y)
    (tX : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (lineCompactification f)).obj (pulledLine A N hA f) ⟶ unit A X) : Prop :=
  (geoP1Pullback A f).map tY ≫ (pullbackUnit A f).hom = exchange A N hA f ≫ tX

/-- The literal evaluation equality, with the compositor's origin witness supplied.
Source: the final displayed equality, using the displayed definitions of C, D and b
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
def Evaluation [QuasiCompact f] (cf : Compactification f)
    (ch : Compactification ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ f)) (M : D A X)
    [IsIso (exchange A N hA f)] [IsIso (projectionU A N hA f cf M)]
    (hq : ProjectionInvertible A (lineCompactification f) (pulledLine A N hA f) M)
    (tY : lineImage A N hA (Y := Y) ⟶ unit A Y)
    (tX : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (lineCompactification f)).obj (pulledLine A N hA f) ⟶ unit A X) : Prop :=
  ∃ hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} X) (source A N hA f M),
  (composition A f (lineCompactification f) cf ch (source A N hA f M) hW).inv ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
      (projectionTensorTrace A (lineCompactification f) (pulledLine A N hA f) M tX hq) =
  comparisonD A N hA f cf ch M hW hq ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)).map tY ≫
    (moduleRightUnit A Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)).hom

private theorem trace_evaluation {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (TX : C ⥤ C) (TY : D ⥤ D) (S : D ⥤ C)
    {U I : D} {B J K Z : C} {T : D}
    (alpha : T ⟶ F.obj Z) (e : Z ⟶ TX.obj B)
    (E : S.obj U ⟶ B) [IsIso E]
    (p : TY.obj U ⟶ F.obj (TX.obj (S.obj U))) [IsIso p]
    (pI : TY.obj I ⟶ F.obj (TX.obj (S.obj I)))
    (tY : U ⟶ I) (tX : B ⟶ J) (ux : S.obj I ⟶ J)
    (rx : TX.obj J ⟶ K) (ry : TY.obj I ⟶ F.obj K)
    (ht : S.map tY ≫ ux = E ≫ tX)
    (hn : TY.map tY ≫ pI = p ≫ F.map (TX.map (S.map tY)))
    (hu : pI ≫ F.map (TX.map ux ≫ rx) = ry) :
    alpha ≫ F.map (e ≫ TX.map tX ≫ rx) =
      alpha ≫ F.map e ≫ F.map (TX.map (inv E)) ≫ inv p ≫ TY.map tY ≫ ry := by
  have he : inv E ≫ S.map tY ≫ ux = tX := by
    rw [ht, IsIso.inv_hom_id_assoc]
  have hp : inv p ≫ TY.map tY ≫ ry = F.map (TX.map (S.map tY) ≫ TX.map ux ≫ rx) := by
    rw [← hu, ← Category.assoc (TY.map tY), hn]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← F.map_comp]
  rw [hp]
  simp only [← F.map_comp]
  have hc : TX.map (inv E) ≫ TX.map (S.map tY) ≫ TX.map ux ≫ rx =
      TX.map tX ≫ rx := by
    simpa only [TX.map_comp, Category.assoc] using
      congrArg (fun z ↦ TX.map z ≫ rx) he
  exact congrArg (fun z ↦ alpha ≫ F.map (e ≫ z)) hc.symm

private theorem source_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    (s : ℕ) (hA : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (hX : IsUnit ((P.coefficients.l ^ (s + 1) : ℕ) : Γ(ProjectiveLine X, ⊤)))
    (hY : IsUnit ((P.coefficients.l ^ (s + 1) : ℕ) : Γ(ProjectiveLine Y, ⊤)))
    (hAY : IsUnit ((P.coefficients.l ^ (s + 1) : ℕ) :
      Γ(AffineSpace PUnit.{u + 1} Y, ⊤)))
    (M : D (Ring P) X)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) X M) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} X) (source (Ring P) (P.coefficients.l ^ (s + 1)) hA f M) := by
  obtain ⟨⟨Me, hMe, ⟨eM⟩⟩, a, b, ht⟩ := hM
  have hMet : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) X Me :=
    ⟨hMe, a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b Me).1
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso eM.symm ht)⟩
  let W := sourceWitness P.coefficients.l P.extension (P.level - 1) X s hA M Me hMet eM
  have hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} X)
      (AffineLinePurity.source P.coefficients.l P.extension (P.level - 1) X s hA M) :=
    ⟨W.complex.obj, W.complex.property, ⟨W.iso⟩⟩
  let e := linePullback (Ring P) (P.coefficients.l ^ (s + 1))
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA f hX hY hAY
  have ec : coefficient (Ring P) (P.coefficients.l ^ (s + 1)) hA X =
      AffineLinePurity.coefficient P.coefficients.l P.extension (P.level - 1) X s hA := by
    rw [AffineLinePurity.coefficient_comparison_eq, etaleCoefficient_eq]
  let e' := ((derivedTensor (ModuleCat.{u + 1} (Ring P))
    (AffineSpace PUnit.{u + 1} X)).obj
      ((geoP1Pullback (Ring P) (AffineSpace PUnit.{u + 1} X ↘ X)).obj M)).mapIso
        (e ≪≫ eqToIso ec)
  apply (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P)) _).prop_of_iso _ hW
  unfold AffineLinePurity.source source projectionSourceObject
  exact e'.symm

private theorem evaluation_of_origin [QuasiCompact f]
    (cf : Compactification f)
    (ch : Compactification ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ f)) (M : D A X)
    (hW : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} X) (source A N hA f M))
    [IsIso (exchange A N hA f)] [IsIso (projectionU A N hA f cf M)]
    (hq : ProjectionInvertible A (lineCompactification f) (pulledLine A N hA f) M)
    (tY : lineImage A N hA (Y := Y) ⟶ unit A Y)
    (tX : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (lineCompactification f)).obj (pulledLine A N hA f) ⟶ unit A X)
    (ht : TraceCompatible A N hA f tY tX) :
    Evaluation A N hA f cf ch M hq tY tX := by
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf
  let TX := (derivedTensor (ModuleCat.{u + 1} A) X).obj M
  let TY := (derivedTensor (ModuleCat.{u + 1} A) Y).obj (F.obj M)
  let S := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let E := exchange A N hA f
  let u := TX.map (pullbackUnit A f).hom ≫ (moduleRightUnit A X M).hom
  refine ⟨hW, ?_⟩
  have hn : TY.map tY ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) cf).app M).app (unit A Y) =
      projectionU A N hA f cf M ≫ F.map (TX.map (S.map tY)) := by
    have h := ((projectionMapOfCompactification (ModuleCat.{u + 1} A) cf).app M).naturality tY
    dsimp only [derivedTensorRightDerivedLowerShriek,
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
      Functor.comp_map, Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight] at h
    unfold projectionU
    dsimp only [derivedTensorRightDerivedLowerShriek,
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
      Functor.comp_map, Functor.postcompose₂, Functor.whiskeringLeft₂,
      Functor.whiskeringLeft, Functor.whiskeringRight]
    exact h
  have hu :
      ((projectionMapOfCompactification (ModuleCat.{u + 1} A) cf).app M).app (unit A Y) ≫
        F.map u = (moduleRightUnit A Y (F.obj M)).hom :=
    compactSupportProjection_rightUnit A cf M
  unfold comparisonD comparisonC projectionTensorTrace
  dsimp only
  let e := inverseProjection A (lineCompactification f) (pulledLine A N hA f) M hq
  unfold projectionTargetObject at e
  simpa only [F, TX, TY, S, E, e, Category.assoc, geoP1Pullback,
    derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map, Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight] using trace_evaluation F TX TY S
    (composition A f (lineCompactification f) cf ch (source A N hA f M) hW).inv e.hom
    E (projectionU A N hA f cf M) _ tY tX
    (pullbackUnit A f).hom (moduleRightUnit A X M).hom
    (moduleRightUnit A Y (F.obj M)).hom ht hn hu


variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The recorded normalized affine-line integration, with no extra Noetherian hypothesis.
Source: normalized line integration
(blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def trace (s : ℕ) (hA : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification S)).obj
        (coefficient (Ring P) (P.coefficients.l ^ (s + 1)) hA S) ⟶ unit (Ring P) S :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
    (affineTraceLineCompactification S)).map
      ((comparison (Ring P) _).map
        (eqToHom (etaleCoefficient_eq P.coefficients.l P.extension (P.level - 1) S s hA).symm)) ≫
    integration P.coefficients.l P.extension (P.level - 1) S s hA (primeUnit P S aS)

/-- The statement's t_X with all canonical Tate and compactification identifications inserted.
Source: t_X display (blueprint: lem-pur-base-changed-line-trace-evaluation). -/
@[irreducible]
def normalizedPulledTrace (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (s : ℕ) (hA : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType (f ≫ aY)] [QuasiCompact (f ≫ aY)] :=
  pulledTrace (Ring P) (P.coefficients.l ^ (s + 1))
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA f
    (by simpa only [Nat.cast_pow] using
      (primeUnit P (ProjectiveLine X) ((ProjectiveLine X ↘ X) ≫ f ≫ aY)).pow (s + 1))
    (by simpa only [Nat.cast_pow] using
      (primeUnit P (ProjectiveLine Y) ((ProjectiveLine Y ↘ Y) ≫ aY)).pow (s + 1))
    (by simpa only [Nat.cast_pow] using
      (primeUnit P (AffineSpace PUnit.{u + 1} Y)
        ((AffineSpace PUnit.{u + 1} Y ↘ Y) ≫ aY)).pow (s + 1))
    (trace P s hA X (f ≫ aY))

/-- Evaluation of the base-changed normalized line integration through projection.
Source: main-20261015, sec-smooth-purity/sk-prop-an, Integration paragraph
(blueprint: lem-pur-base-changed-line-trace-evaluation).
Proof, following the four steps of the node:
1. Write F = Rp_* j_!. Naturality of the counit-defined proper projection and of
   the open tensor comparison gives F(1 tensor Sv) P_B = P_B' (1 tensor v).
   These are the actual components, on the ambient unbounded categories, using
   lem-weil-pbc-ringed-projection-mate-exact and lem-sf-open-tensor-normalization.
2. At the coefficient unit the proper projection mate is the right unitor.
   The open comparison restricts to the identity; full faithfulness of j_!
   identifies its unit component. Pullback-unit composition then gives
   F(u_M) P_1 = rho_V, without inverting P_1. The unit-composition compatibility
   is lem-pur-derived-pullback-tensor-iso.
3. Insert the assumed equality S(t_Y) followed by the pullback unit = E then t_X.
   Bifunctoriality and invertibility of E identify the contraction of C with
   F(b_q,M) after alpha inverse.
4. Substitute C = P_U D. Naturality at t_Y and the unit equation of step 2
   turn this contraction into (1_V tensor t_Y) followed by rho_V after D.
The existential hW records the typing domain of the already specified compositor:
choose a bounded finite-Tor ordinary representative of M; its inverse image tensored
with the shifted Tate line is bounded and has comparison image W. Thus W has the
required origin property. No additional domain hypothesis is imposed.
No exceptional inverse image or Kunneth identification is used. -/
theorem baseChangedLineTraceEvaluation
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType (f ≫ aY)] [QuasiCompact (f ≫ aY)] [IsSeparated (f ≫ aY)]
    (cf : Compactification f)
    (ch : Compactification ((AffineSpace PUnit.{u + 1} X ↘ X) ≫ f))
    (s : ℕ) (hA : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0)
    (M : D (Ring P) X)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) X M)
    (hV : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P)) cf).obj M))
    (hU : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} (Ring P)) Y
      (lineImage (Ring P) (P.coefficients.l ^ (s + 1)) hA (Y := Y)))
    [IsIso (exchange (Ring P) (P.coefficients.l ^ (s + 1)) hA f)]
    [IsIso (projectionU (Ring P) (P.coefficients.l ^ (s + 1)) hA f cf M)]
    (hq : ProjectionInvertible (Ring P) (lineCompactification f)
      (pulledLine (Ring P) (P.coefficients.l ^ (s + 1)) hA f) M)
    (ht : TraceCompatible (Ring P) (P.coefficients.l ^ (s + 1)) hA f
      (trace P s hA Y aY) (normalizedPulledTrace P f s hA aY)) :
    Evaluation (Ring P) (P.coefficients.l ^ (s + 1)) hA f cf ch M hq
      (trace P s hA Y aY) (normalizedPulledTrace P f s hA aY) := by
  have _ := hV
  have _ := hU
  have hW := source_origin f P s hA
    (by simpa only [Nat.cast_pow] using
      (primeUnit P (ProjectiveLine X) ((ProjectiveLine X ↘ X) ≫ f ≫ aY)).pow (s + 1))
    (by simpa only [Nat.cast_pow] using
      (primeUnit P (ProjectiveLine Y) ((ProjectiveLine Y ↘ Y) ≫ aY)).pow (s + 1))
    (by simpa only [Nat.cast_pow] using
      (primeUnit P (AffineSpace PUnit.{u + 1} Y)
        ((AffineSpace PUnit.{u + 1} Y ↘ Y) ≫ aY)).pow (s + 1)) M hM
  exact evaluation_of_origin (Ring P) (P.coefficients.l ^ (s + 1)) hA f cf ch M hW hq
    (trace P s hA Y aY) (normalizedPulledTrace P f s hA aY) ht

end AlgebraicGeometry.ProEtale.BaseChangedLineTrace
