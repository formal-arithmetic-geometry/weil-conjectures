/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.LciCotangentPresentation
public import Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant
public import Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import Sheaf.TraceFormula.AffineTwoTermDeterminant
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler

/-! # Descent and smooth normalization of the lci cotangent determinant

Source: Stacks Project, Perfect Complexes, Tags 0FJX and 0FJY; Cotangent Complex,
Tags 08SL and 08R5; Morphisms of Schemes, Tag 02G1; More on Algebra, Tag 0FJI.
(blueprint: lem-trf-lci-determinant-descent-smooth).

The auxiliary records unpack the hypotheses and the comparisons in this one statement.
All local lines use the existing exterior powers, internal Hom and tensor pullback.
Transitions are defined through the single intrinsic determinant on arbitrary common opens.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Algebra.CotangentResolution AlgebraicGeometry.Scheme.Modules
open scoped ZeroObject

namespace AlgebraicGeometry.LciDeterminantDescent

variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- One of the polynomial presentations in the hypothesis, retaining the actual ideal,
its Koszul-regular generators of length c, and the assumed conormal rank. No flatness,
Noetherian or separation condition is imposed.
Source: Stacks, Tags 08SL and 0FJX
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
structure Presentation {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (U : X.Opens) where
  P : Scheme.{u}
  i : U.toScheme ⟶ P
  p : P ⟶ S
  lci : CotangentPresentation.LciPresentation i p
  c : ℕ
  rank_eq : lci.dimension = c + d
  factor : i ≫ p = U.ι ≫ f
  length : ∀ x : U.toScheme, ∃ W : P.affineOpens, i x ∈ W.1 ∧
    ∃ a : Fin c → Γ(P, W.1), RingTheory.Sequence.IsKoszulRegular a ∧
      Ideal.span (Set.range a) = i.ker.ideal W
  conormal_free : (CotangentPresentation.conormalTerm i).IsFiniteLocallyFreeOfRank c

/-- The displayed local line, in dual-first order with the actual sheaf dual.
Source: Stacks, Tag 0FJX
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def Presentation.line {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : Presentation f d U) : U.toScheme.Modules :=
  dual (exteriorSheaf (CotangentPresentation.conormalTerm C.i) C.c) ⊗
    exteriorSheaf (CotangentPresentation.ambientDifferentials C.i C.p) C.lci.dimension

variable {A : Coherence.{u}} (D : CotangentPresentation.System A)
  (F : CotangentPresentation.AffineIdentifications D) (κ : Naive.Comparison A)
  (E : CotangentPresentation.LciIdentifications D F κ)

/-- The conormal differential transported from the recorded conormal model, hence [a] ↦ da.
Source: Stacks, Tag 08SL
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def differential {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : Presentation f d U) : CotangentPresentation.conormalTerm C.i ⟶
      CotangentPresentation.ambientDifferentials C.i C.p :=
  (E.identification C.i C.p C.lci).model.negative.inv ≫
    (E.identification C.i C.p C.lci).model.complex.d (-1) 0 ≫
      (E.identification C.i C.p C.lci).model.zero.hom

/-- The existing two-term determinant model, with the conormal and ambient ranks.
Source: Stacks, Tags 08SL and 0FJX
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def model {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : Presentation f d U)
    (hV : (CotangentPresentation.ambientDifferentials C.i C.p).IsFiniteLocallyFreeOfRank
      C.lci.dimension) : TwoTermDeterminantModel U.toScheme :=
  ⟨_, _, differential D F κ E C, C.c, C.lci.dimension, C.conormal_free, hV⟩

/-- The canonical restriction square, with the base unchanged.
Source: Stacks, Tags 08T3 and 08SL
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def restrictionSquare {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : Presentation f d U) :
    CotangentPresentation.BaseSquare f (C.i ≫ C.p) U.ι (𝟙 S) :=
  D.square f (C.i ≫ C.p) U.ι (𝟙 S) (by simpa using C.factor.symm)

/-- Realizing the recorded conormal complex as the displayed double complex. The two
component equations fix this bridge; it is not an arbitrary derived isomorphism.
Source: Stacks, Tags 08SL and 08T3
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
structure Realization {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : Presentation f d U) where
  ambient_free : (CotangentPresentation.ambientDifferentials C.i C.p).IsFiniteLocallyFreeOfRank
    C.lci.dimension
  comparison : (model D F κ E C ambient_free).complex ≅
    (E.identification C.i C.p C.lci).model.complex
  negative : comparison.hom.f (-1) ≫ (E.identification C.i C.p C.lci).model.negative.hom =
    (HomologicalComplex.doubleXIso₀ (differential D F κ E C) (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide)).hom
  zero : comparison.hom.f 0 ≫ (E.identification C.i C.p C.lci).model.zero.hom =
    (HomologicalComplex.doubleXIso₁ (differential D F κ E C) (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide) (by decide)).hom
  restriction_iso : IsIso (CotangentPresentation.derivedChange D (restrictionSquare D C))

/-- The specified λ: first the fixed bridge, then the dependency's conormal comparison,
then the inverse of intrinsic cotangent restriction.
Source: Stacks, Tags 08SL and 08T3
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def Realization.lambda {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : Presentation f d U} (H : Realization D F κ E C) :
    DerivedCategory.Q.obj (model D F κ E C H.ambient_free).complex ≅
      (derivedPullback U.ι).obj (CotangentPresentation.cotangent (D.model f)) :=
  DerivedCategory.Q.mapIso H.comparison ≪≫ (E.identification C.i C.p C.lci).iso ≪≫
    (@asIso _ _ _ _ (CotangentPresentation.derivedChange D (restrictionSquare D C))
      H.restriction_iso).symm

/-- The exterior-model comparison followed by det(λ) and inverse determinant restriction.
Source: Stacks, Tags 0FJX and 0FJY
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def Realization.alpha {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : Presentation f d U} (H : Realization D F κ E C)
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) :
    C.line ≅ (tensorPullback U.ι).obj
      (twoTermDeterminantValue (T.functor X) (CotangentPresentation.cotangent (D.model f)) hL) :=
  (T.modelIso (model D F κ E C H.ambient_free)).symm ≪≫
    twoTermDeterminantIso (T.functor U.toScheme)
      (T.model_mem (model D F κ E C H.ambient_free)) (T.pullback_mem U.ι _ hL)
      (H.lambda D F κ E) ≪≫ (T.pullbackIso U.ι _ hL).symm

/-- Restrict α to any smaller open, using the section-normalized composition comparison.
Source: Stacks, Tag 0FJY
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def Realization.alphaOn {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    {C : Presentation f d U} (H : Realization D F κ E C)
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f)))
    {W : X.Opens} (h : W ≤ U) :
    (tensorPullback (X.homOfLE h)).obj C.line ≅ (tensorPullback W.ι).obj
      (twoTermDeterminantValue (T.functor X) (CotangentPresentation.cotangent (D.model f)) hL) :=
  (tensorPullback (X.homOfLE h)).mapIso (H.alpha D F κ E T hL) ≪≫
    (tensorPullbackSectionComp (X.homOfLE h) U.ι).symm.app _ ≪≫
      eqToIso (congrArg (fun g ↦ (tensorPullback g).obj _) (X.homOfLE_ι h))

/-- Comparisons on a common open, which may be nonaffine. Inserting any third
presentation means composing two such maps through the same determinant line.
Source: Stacks, Tags 0FJX and 0FJY
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def transition {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U V : X.Opens}
    {C : Presentation f d U} {C' : Presentation f d V}
    (H : Realization D F κ E C) (H' : Realization D F κ E C')
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f)))
    {W : X.Opens} (h : W ≤ U) (h' : W ≤ V) :
    (tensorPullback (X.homOfLE h)).obj C.line ≅
      (tensorPullback (X.homOfLE h')).obj C'.line :=
  H.alphaOn D F κ E T hL h ≪≫ (H'.alphaOn D F κ E T hL h').symm

/-- The canonical identification between successive and direct restriction of a module.
Source: Stacks, Tag 0097
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def restrictionComp {X : Scheme.{u}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V)
    (M : U.toScheme.Modules) :
    (tensorPullback (X.homOfLE k)).obj ((tensorPullback (X.homOfLE h)).obj M) ≅
      (tensorPullback (X.homOfLE (k.trans h))).obj M :=
  (tensorPullbackSectionComp (X.homOfLE k) (X.homOfLE h)).symm.app M ≪≫
    eqToIso (congrArg (fun g ↦ (tensorPullback g).obj M) (X.homOfLE_homOfLE k h))

/-- The degree-zero model of the smooth differential sheaf, with its zero term explicit.
Source: Stacks, Tags 08R5 and 0FJX
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def smoothModel {Y S : Scheme.{u}} (f : Y ⟶ S) (d : ℕ)
    (h0 : (0 : Y.Modules).IsFiniteLocallyFreeOfRank 0)
    (hW : f.relativeDifferentials.IsFiniteLocallyFreeOfRank d) : TwoTermDeterminantModel Y :=
  ⟨0, f.relativeDifferentials, 0, 0, d, h0, hW⟩

/-- The smooth comparison is induced by the actual canonical cotangent augmentation.
The line comparison is fixed by evaluation on the empty negative wedge, including d=0.
Source: Stacks, Tags 08R5, 02G1 and 0FJX
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
structure SmoothComparison {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) (U : X.Opens) where
  rank : (U.ι ≫ f).relativeDifferentials.IsFiniteLocallyFreeOfRank d
  zero_rank : (0 : U.toScheme.Modules).IsFiniteLocallyFreeOfRank 0
  single : (smoothModel (U.ι ≫ f) d zero_rank rank).complex ≅
    (HomologicalComplex.single _ (.up ℤ) 0).obj (U.ι ≫ f).relativeDifferentials
  single_zero : single.hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (U.ι ≫ f).relativeDifferentials).hom =
    (HomologicalComplex.doubleXIso₁ (0 : (0 : U.toScheme.Modules) ⟶
      (U.ι ≫ f).relativeDifferentials) (c := ComplexShape.up ℤ)
      (i₀ := -1) (i₁ := 0) (by decide) (by decide)).hom
  augmentation_iso : IsIso (DerivedCategory.Q.{w}.map (D.augmentation (U.ι ≫ f)))
  square : CotangentPresentation.BaseSquare f (U.ι ≫ f) U.ι (𝟙 S)
  restriction_iso : IsIso (CotangentPresentation.derivedChange D square)
  exterior : (smoothModel (U.ι ≫ f) d zero_rank rank).line ≅
    exteriorSheaf (U.ι ≫ f).relativeDifferentials d
  exterior_normalization : ∀ (O : U.toScheme.Opens)
    (a : Γ(dual (exteriorSheaf (0 : U.toScheme.Modules) 0), O))
    (b : Fin d → Γ((U.ι ≫ f).relativeDifferentials, O)),
    exterior.hom.app O (tmulSection (X := U.toScheme) a
      (exteriorSheafSection (U.ι ≫ f).relativeDifferentials d O b)) =
    a.app (op (Over.mk (𝟙 O))) (exteriorSheafSection (0 : U.toScheme.Modules) 0 O Fin.elim0) •
      exteriorSheafSection (U.ι ≫ f).relativeDifferentials d O b

/-- β is determinant restriction, determinant of the canonical smooth augmentation,
and the degree-zero exterior-model comparison, in that order.
Source: Stacks, Tags 08R5 and 0FJX
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def SmoothComparison.beta {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    {T : TwoTermPerfectDeterminantData.{u, w}}
    {hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))}
    {U : X.Opens} (B : SmoothComparison D f d T hL U) :
    (tensorPullback U.ι).obj
      (twoTermDeterminantValue (T.functor X) (CotangentPresentation.cotangent (D.model f)) hL) ≅
      exteriorSheaf (U.ι ≫ f).relativeDifferentials d :=
  T.pullbackIso U.ι _ hL ≪≫
    twoTermDeterminantIso (T.functor U.toScheme) (T.pullback_mem U.ι _ hL)
      (T.model_mem (smoothModel (U.ι ≫ f) d B.zero_rank B.rank))
      ((@asIso _ _ _ _ (CotangentPresentation.derivedChange D B.square) B.restriction_iso) ≪≫
        (@asIso _ _ _ _ (DerivedCategory.Q.map (D.augmentation (U.ι ≫ f)))
          B.augmentation_iso) ≪≫ (DerivedCategory.Q.mapIso B.single).symm) ≪≫
    T.modelIso (smoothModel (U.ι ≫ f) d B.zero_rank B.rank) ≪≫ B.exterior

/-- The canonical ambient-to-source differential map, characterized on universal
ambient differentials. The theorem supplies its existence as well as the normalization,
so the smooth formula does not hide an uninhabited class of maps.
Source: Stacks, Tags 01UM and 08SL
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def IsSourceDifferential {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ} {U : X.Opens}
    (C : Presentation f d U)
    (v : CotangentPresentation.ambientDifferentials C.i C.p ⟶ (U.ι ≫ f).relativeDifferentials) :
    Prop :=
  ∀ (O : C.P.Opens) (r : Γ(C.P, O)),
    v.app (C.i ⁻¹ᵁ O) (tensorPullbackSection C.i C.p.relativeDifferentials O
      (C.p.relativeDifferentialsDerivation.d r)) =
    (U.ι ≫ f).relativeDifferentialsDerivation.d (C.i.app O r)

/-- Relation-first smooth normalization, on every open where the presentation is smooth.
The map to Ω is specified on ambient universal differentials, so cannot be arbitrary.
Source: Stacks, More on Algebra, Tag 0FJI; Cotangent Complex, Tag 08R5
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def SmoothComparison.IsRelationFirst {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    {T : TwoTermPerfectDeterminantData.{u, w}}
    {hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))}
    {U : X.Opens} (B : SmoothComparison D f d T hL U)
    (C : Presentation f d U) (H : Realization D F κ E C) : Prop :=
  ∀ v : CotangentPresentation.ambientDifferentials C.i C.p ⟶ (U.ι ≫ f).relativeDifferentials,
    IsSourceDifferential C v →
    ∀ (O : U.toScheme.Opens)
      (a : Fin C.c → Γ(CotangentPresentation.conormalTerm C.i, O))
      (b : Fin d → Γ((U.ι ≫ f).relativeDifferentials, O))
      (l : Fin d → Γ(CotangentPresentation.ambientDifferentials C.i C.p, O))
      (a' : Γ(dual (exteriorSheaf (CotangentPresentation.conormalTerm C.i) C.c), O)),
      a'.app (op (Over.mk (𝟙 O)))
        (exteriorSheafSection (CotangentPresentation.conormalTerm C.i) C.c O a) =
          (1 : Γ(U.toScheme, O)) →
      (∀ j, v.app O (l j) = b j) →
      (B.beta D).hom.app O ((H.alpha D F κ E T hL).hom.app O
        (tmulSection (X := U.toScheme) a'
          (exteriorSheafSection (CotangentPresentation.ambientDifferentials C.i C.p)
            C.lci.dimension O (fun j ↦ Fin.append
              (fun k ↦ (differential D F κ E C).app O (a k)) l (Fin.cast C.rank_eq j))))) =
        exteriorSheafSection (U.ι ≫ f).relativeDifferentials d O b

variable [∀ (Y : Scheme.{u}) (U : Y.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]

/-- The negative component of a canonical map of conormal complexes in the actual
conormal terms, rather than in chosen representatives.
Source: Stacks, Tags 08QL and 08SL
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def conormalMap {U P S U' P' S' : Scheme.{u}}
    {i : U ⟶ P} {p : P ⟶ S} {i' : U' ⟶ P'} {p' : P' ⟶ S'}
    {N : CotangentPresentation.ConormalModel i p}
    {N' : CotangentPresentation.ConormalModel i' p'} {g : U' ⟶ U} {k : P' ⟶ P}
    (m : CotangentPresentation.ConormalChange N N' g k) :
    (tensorPullback g).obj (CotangentPresentation.conormalTerm i) ⟶
      CotangentPresentation.conormalTerm i' :=
  (tensorPullback g).map N.negative.inv ≫ m.map.f (-1) ≫ N'.negative.hom

/-- The degree-zero component in the actual ambient differential terms.
Source: Stacks, Tags 08QL and 08SL
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def ambientMap {U P S U' P' S' : Scheme.{u}}
    {i : U ⟶ P} {p : P ⟶ S} {i' : U' ⟶ P'} {p' : P' ⟶ S'}
    {N : CotangentPresentation.ConormalModel i p}
    {N' : CotangentPresentation.ConormalModel i' p'} {g : U' ⟶ U} {k : P' ⟶ P}
    (m : CotangentPresentation.ConormalChange N N' g k) :
    (tensorPullback g).obj (CotangentPresentation.ambientDifferentials i p) ⟶
      CotangentPresentation.ambientDifferentials i' p' :=
  (tensorPullback g).map N.zero.inv ≫ m.map.f 0 ≫ N'.zero.hom

/-- Restriction of a global module in two steps, with the canonical comparison to its
direct restriction. Source: Stacks, Tag 0097
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
def globalRestriction {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (M : X.Modules) :
    (tensorPullback (X.homOfLE h)).obj ((tensorPullback U.ι).obj M) ≅
      (tensorPullback V.ι).obj M :=
  (tensorPullbackSectionComp (X.homOfLE h) U.ι).symm.app M ≪≫
    eqToIso (congrArg (fun g ↦ (tensorPullback g).obj M) (X.homOfLE_ι h))

/-- All descent assertions, on arbitrary overlaps and refinements. The fields refer to
one determinant line and to the fixed α and β above, rather than unspecified isomorphisms.
Source: Stacks, Tags 0FJX, 0FJY, 08SL, 08R5 and 02G1
(blueprint: lem-trf-lci-determinant-descent-smooth). -/
structure Descent {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (T : TwoTermPerfectDeterminantData.{u, w})
    (hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f))) where
  perfect : Scheme.IsPerfect X (CotangentPresentation.cotangent (D.model f))
  tor : ∀ (M : X.Modules) (j : ℤ), j < -1 ∨ 0 < j →
    IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (CotangentPresentation.tensorModule (CotangentPresentation.cotangent (D.model f)) M))
  invertible : (twoTermDeterminantValue (T.functor X)
    (CotangentPresentation.cotangent (D.model f)) hL).IsInvertible
  chart : ∀ (U : X.Opens) (C : Presentation f d U), Realization D F κ E C
  identity : ∀ (U W : X.Opens) (C : Presentation f d U) (h : W ≤ U),
    transition D F κ E (chart U C) (chart U C) T hL h h = Iso.refl _
  cocycle : ∀ (U V Z W : X.Opens) (C : Presentation f d U) (C' : Presentation f d V)
    (C'' : Presentation f d Z) (h : W ≤ U) (h' : W ≤ V) (h'' : W ≤ Z),
    transition D F κ E (chart U C) (chart V C') T hL h h' ≪≫
      transition D F κ E (chart V C') (chart Z C'') T hL h' h'' =
        transition D F κ E (chart U C) (chart Z C'') T hL h h''
  refinement : ∀ (U V W Z : X.Opens) (C : Presentation f d U) (C' : Presentation f d V)
    (h : W ≤ U) (h' : W ≤ V) (k : Z ≤ W),
    (tensorPullback (X.homOfLE k)).mapIso
        (transition D F κ E (chart U C) (chart V C') T hL h h') ≪≫
        restrictionComp h' k C'.line =
      restrictionComp h k C.line ≪≫
        transition D F κ E (chart U C) (chart V C') T hL (k.trans h) (k.trans h')
  presentation_restriction : ∀ (U V : X.Opens) (C : Presentation f d U)
    (C' : Presentation f d V) (h : V ≤ U) (k : C'.P ⟶ C.P),
    IsOpenImmersion k → IsPullback (X.homOfLE h) C'.i C.i k → k ≫ C.p = C'.p →
    ∀ (hc : C.c = C'.c) (hn : C.lci.dimension = C'.lci.dimension),
    ∃ m : CotangentPresentation.ConormalChange
        (E.identification C.i C.p C.lci).model (E.identification C'.i C'.p C'.lci).model
        (X.homOfLE h) k,
      IsFlatLCIPullbackDeterminantComparison (X.homOfLE h)
        (CotangentPresentation.conormalTerm C.i)
        (CotangentPresentation.ambientDifferentials C.i C.p)
        (CotangentPresentation.conormalTerm C'.i)
        (CotangentPresentation.ambientDifferentials C'.i C'.p)
        C.c C'.c C.lci.dimension C'.lci.dimension hc hn (conormalMap m) (ambientMap m)
        ((chart U C).alphaOn D F κ E T hL h ≪≫ ((chart V C').alpha D F κ E T hL).symm)
  smooth : ∀ (U : X.Opens), Smooth (U.ι ≫ f) → SmoothComparison D f d T hL U
  source_differential : ∀ (U : X.Opens) (C : Presentation f d U),
    ∃ v : CotangentPresentation.ambientDifferentials C.i C.p ⟶ (U.ι ≫ f).relativeDifferentials,
      IsSourceDifferential C v
  relation_first : ∀ (U : X.Opens) (hs : Smooth (U.ι ≫ f)) (C : Presentation f d U),
    (smooth U hs).IsRelationFirst D F κ E C (chart U C)
  smooth_restriction : ∀ (U V : X.Opens) (h : V ≤ U)
    (hs : Smooth (U.ι ≫ f)) (hs' : Smooth (V.ι ≫ f)),
    ∃ (v : (tensorPullback (X.homOfLE h)).obj (U.ι ≫ f).relativeDifferentials ⟶
        (V.ι ≫ f).relativeDifferentials)
      (e : (tensorPullback (X.homOfLE h)).obj
        (exteriorSheaf (U.ι ≫ f).relativeDifferentials d) ≅
          exteriorSheaf (V.ι ≫ f).relativeDifferentials d),
      (∀ (O : U.toScheme.Opens) (r : Γ(U.toScheme, O)),
        v.app ((X.homOfLE h) ⁻¹ᵁ O)
          (tensorPullbackSection (X.homOfLE h) (U.ι ≫ f).relativeDifferentials O
            ((U.ι ≫ f).relativeDifferentialsDerivation.d r)) =
        (V.ι ≫ f).relativeDifferentialsDerivation.d ((X.homOfLE h).app O r)) ∧
      (∀ (O : U.toScheme.Opens) (a : Fin d → Γ((U.ι ≫ f).relativeDifferentials, O)),
        e.hom.app ((X.homOfLE h) ⁻¹ᵁ O)
          (tensorPullbackSection (X.homOfLE h) (exteriorSheaf (U.ι ≫ f).relativeDifferentials d)
            O (exteriorSheafSection (U.ι ≫ f).relativeDifferentials d O a)) =
          exteriorSheafSection (V.ι ≫ f).relativeDifferentials d ((X.homOfLE h) ⁻¹ᵁ O)
            (fun j ↦ v.app ((X.homOfLE h) ⁻¹ᵁ O)
              (tensorPullbackSection (X.homOfLE h) (U.ι ≫ f).relativeDifferentials O (a j)))) ∧
      (tensorPullback (X.homOfLE h)).mapIso ((smooth U hs).beta D) ≪≫ e =
        globalRestriction h (twoTermDeterminantValue (T.functor X)
          (CotangentPresentation.cotangent (D.model f)) hL) ≪≫ (smooth V hs').beta D
  smooth_overlap : ∀ (U V W : X.Opens) (hs : Smooth (W.ι ≫ f))
    (C : Presentation f d U) (C' : Presentation f d V) (h : W ≤ U) (h' : W ≤ V),
    transition D F κ E (chart U C) (chart V C') T hL h h' ≪≫
        (chart V C').alphaOn D F κ E T hL h' ≪≫ (smooth W hs).beta D =
      (chart U C).alphaOn D F κ E T hL h ≪≫ (smooth W hs).beta D

/-- The intrinsic lci determinant descends the conormal lines and has the relation-first
smooth normalization. The determinant's canonicity is the recorded normalized interface:
its signed exact-cone maps are the kernel-normalized T_a of the surjective calculus;
its pullback clause fixes the exterior comparisons on restrictions.
Source: Stacks, Tags 0FJX, 0FJY, 08SL, 08R5 and 02G1
(blueprint: lem-trf-lci-determinant-descent-smooth).

Proof:
1. On affine base opens and principal ambient opens use the polynomial differential
basis (lem-weil-pbc-polynomial-ring-kahler-basis-any-variables) and its localization
(lem-weil-pbc-kahler-differentials-localization). The relative differential sheaf's
canonical affine comparison gives ambient rank n. Conormal rank c is a hypothesis.
2. The canonical conormal identifications of lem-trf-lci-cotangent-presentation give
local two-term finite locally free models. Apply lem-trf-two-term-perfect-determinant
for global perfection, the Tor window and the invertible determinant. Define α by
its model comparison, det(λ), and inverse restriction, exactly as above.
3. On every overlap define t through this same global determinant. Cancellation gives
identity, the cocycle, and independence of an inserted third presentation. The model
comparisons commute with restriction by their normalization. Determinant pullback
composition gives the refinement equation, without affine intersections or separation.
4. On a smooth open the canonical augmentation is invertible by the cotangent theorem.
Smooth differentials are finite locally free by
lem-ag-smooth-relative-differentials-finite-locally-free. The conormal augmentation has
zero kernel in degree -1 and cokernel Ω in degree 0. Locally split the resulting exact
sequence 0 → C → V → Ω → 0 to obtain rank Ω = n-c = d. Apply the determinant to the
augmentation and use its degree-zero exterior model, giving the specified β.
5. On affine trivializing opens compute the degreewise surjective quasi-isomorphism
[C → V] → [0 → Ω]. By lem-trf-affine-two-term-determinant and the fixed normalization,
its determinant is T_q of lem-trf-surjective-two-term-determinant-calculus. Its kernel
is [C → dC]; the kernel differential sends the chosen relation basis to its differential
basis. The kernel-first exact-sequence wedge map therefore sends the relation dual
wedge tensor (d relations wedge quotient lifts) to the quotient wedge, with no extra
sign. This is precisely relation_first. Equality of sheaf maps is local, so the formula
holds on every open, including nonaffine ones.
6. On a smooth overlap compose both α maps with the same β. Cancellation gives
smooth_overlap. The canonical augmentation and determinant restriction also make the
smooth identifications agree on further restrictions. Empty wedges cover c=0 and d=0;
the empty scheme requires no local rank witnesses. -/
theorem exists_lciDeterminantDescentSmooth
    (hD : CotangentPresentation.Properties D F κ E)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (cover : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (Presentation f d U))
    (T : TwoTermPerfectDeterminantData.{u, w}) (hT : T.IsCanonical) :
    ∃ hL : isTwoTermPerfect X (CotangentPresentation.cotangent (D.model f)),
      Nonempty (Descent D F κ E f d T hL) := by
  sorry

end AlgebraicGeometry.LciDeterminantDescent
