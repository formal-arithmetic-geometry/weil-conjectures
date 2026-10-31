/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocusDual
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.AlgebraicGeometry.Scheme

import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.YonedaExtension.YonedaExtensionData
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Functorial equivariant integral extensions of invertible modules

Source: Stacks Project, Tags 02FQ and 03AJ, fibre-over-one construction;
latest blueprint sk-prop-diagonal-tower-system.proof.md (1), relative Cartier quotient
(blueprint: lem-pur-equivariant-line-extension).

Negative powers are tensor powers of the dual. The presentation below specifies
multiplication on nonnegative degrees and evaluation between opposite degrees;
these determine multiplication on all degrees, including mixed signs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme

/-- Integer tensor powers, with negative powers represented by powers of the dual.
Source: Stacks 01CA, 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def lineIntegralPower {T : Scheme.{u}} (L : T.Modules) : ℤ → T.Modules
  | .ofNat n => L.tensorPow n
  | .negSucc n => (Modules.dual L).tensorPow (n + 1)

/-- Frames of a module on the pro-etale site; restriction is pseudofunctorial pullback.
Source: Stacks 01CD, 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrames {T : Scheme.{u}} (L : T.Modules) : T.ProEtᵒᵖ ⥤ Type (u + 1) :=
  (Pseudofunctor.presheafIso (F := modulesPseudofunctor) (ProEt.forget T)
    (Modules.unitObj T) L).toFunctor ⋙ uliftFunctor.{u + 1}

/-- The constant-degree coproduct before sheafification. Its sheafification allows
locally constant, rather than just constant, degrees.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineGradedFrames {T : Scheme.{u}} (L : T.Modules) : T.ProEtᵒᵖ ⥤ Type (u + 1) :=
  ∐ fun a : ℤ => lineFrames (lineIntegralPower L a)

/-- The sheaf of graded frames, with no group law assumed in its definition.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineGradedFrameSheaf {T : Scheme.{u}} (L : T.Modules) :
    Sheaf (ProEt.topology T) (Type (u + 1)) :=
  (presheafToSheaf (ProEt.topology T) (Type (u + 1))).obj (lineGradedFrames L)

/-- The integer sheaf, in the common site coefficient universe.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
abbrev lineIntegerSheaf (T : Scheme.{u}) :=
  (constantSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The constant section of a specified degree.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineDegreeSection (T : Scheme.{u}) (a : ℤ) (U : T.ProEtᵒᵖ) :
    (lineIntegerSheaf T).obj.obj U :=
  (toSheafify (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨a⟩

/-- An actual isomorphism underlying a frame, with the pulled-back unit as source.
Source: Stacks 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrameIso {T : Scheme.{u}} {L : T.Modules} {U : T.ProEtᵒᵖ}
    (p : (lineFrames L).obj U) :
    (Modules.pullback U.unop.hom).obj (Modules.unit T) ≅
      (Modules.pullback U.unop.hom).obj L :=
  @asIso _ _ _ _ p.down.1 p.down.2

/-- A frame as an isomorphism from the structure sheaf of its own scheme.
Source: Stacks 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrameLocalIso {T : Scheme.{u}} {L : T.Modules} {U : T.ProEtᵒᵖ}
    (p : (lineFrames L).obj U) :
    Modules.unit U.unop.left ≅ (Modules.pullback U.unop.hom).obj L :=
  (Modules.pullbackObjUnitIso U.unop.hom).symm ≪≫ lineFrameIso p

/-- Construct a frame from its local isomorphism, without a choice of a basis.
Source: Stacks 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrameOfLocalIso {T : Scheme.{u}} {L : T.Modules} {U : T.ProEtᵒᵖ}
    (p : Modules.unit U.unop.left ≅ (Modules.pullback U.unop.hom).obj L) :
    (lineFrames L).obj U :=
  ⟨⟨((Modules.pullbackObjUnitIso U.unop.hom) ≪≫ p).hom,
    ((Modules.pullbackObjUnitIso U.unop.hom) ≪≫ p).isIso_hom⟩⟩

/-- Degree zero frames are multiplication by units.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineUnitFrame {T : Scheme.{u}} (U : T.ProEtᵒᵖ)
    (g : (proEtaleUnitsSheaf T).obj.obj U) :
    (lineFrames (lineIntegralPower (Modules.unit T) 0)).obj U :=
  ⟨⟨smulMor
    ((modulesPseudofunctor.map U.unop.hom.op.toLoc).toFunctor.obj (Modules.unitObj T))
    ((Additive.toMul g.down : Γ(U.unop.left, ⊤)ˣ) : Γ(U.unop.left, ⊤)),
    Modules.isIso_smulHom_units _ (Additive.toMul g.down)⟩⟩

/-- Tensoring two frames of nonnegative powers, using the monoidal pullback comparison.
Source: Stacks 01CA, 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def linePositiveFrameProduct {T : Scheme.{u}} (L : T.Modules) (a b : ℕ)
    (U : T.ProEtᵒᵖ) (p : (lineFrames (L.tensorPow a)).obj U)
    (q : (lineFrames (L.tensorPow b)).obj U) :
    (lineFrames (L.tensorPow (a + b))).obj U :=
  lineFrameOfLocalIso
    ((λ_ (Modules.unit U.unop.left)).symm ≪≫
      (lineFrameLocalIso p ⊗ᵢ lineFrameLocalIso q) ≪≫
      Functor.Monoidal.μIso (Modules.pullback U.unop.hom) _ _ ≪≫
      (Modules.pullback U.unop.hom).mapIso (Modules.tensorPowAddIso L a b).symm)

/-- Tensor powers of a morphism, using the existing right-recursive tensor powers.
Source: Stacks 01CA (blueprint: lem-pur-equivariant-line-extension). -/
def lineTensorPowerMap {T : Scheme.{u}} {M N : T.Modules} (f : M ⟶ N) :
    (n : ℕ) → M.tensorPow n ⟶ N.tensorPow n
  | 0 => 𝟙 _
  | n + 1 => f ⊗ₘ lineTensorPowerMap f n

/-- The canonical unit identification for a tensor power of the structure sheaf.
Source: Stacks 01CA (blueprint: lem-pur-equivariant-line-extension). -/
def lineUnitTensorPowerIso (T : Scheme.{u}) :
    (n : ℕ) → (Modules.unit T).tensorPow n ≅ Modules.unit T
  | 0 => Iso.refl _
  | n + 1 => (Iso.refl _ ⊗ᵢ lineUnitTensorPowerIso T n) ≪≫ λ_ _

/-- Tensor powers of evaluation, with the symmetry pairing corresponding factors.
Source: Stacks 01CA (blueprint: lem-pur-equivariant-line-extension). -/
def linePowerEvaluation {T : Scheme.{u}} (L : T.Modules) (n : ℕ) :
    L.tensorPow n ⊗ (Modules.dual L).tensorPow n ⟶ Modules.unit T :=
  (Modules.tensorPowTensorObjIso L (Modules.dual L) n).inv ≫
    lineTensorPowerMap (Modules.dualEvaluation L) n ≫ (lineUnitTensorPowerIso T n).hom

/-- The evaluation pairing of frames of a positive power and its inverse power.
Source: Stacks 01CA (blueprint: lem-pur-equivariant-line-extension). -/
def lineOppositeFrameEvaluation {T : Scheme.{u}} (L : T.Modules) (n : ℕ)
    (U : T.ProEtᵒᵖ) (p : (lineFrames (L.tensorPow (n + 1))).obj U)
    (q : (lineFrames ((Modules.dual L).tensorPow (n + 1))).obj U) :
    Modules.unit U.unop.left ⟶ Modules.unit U.unop.left :=
  (λ_ (Modules.unit U.unop.left)).inv ≫
    ((lineFrameLocalIso p).hom ⊗ₘ (lineFrameLocalIso q).hom) ≫
    (Functor.Monoidal.μIso (Modules.pullback U.unop.hom) _ _).hom ≫
    (Modules.pullback U.unop.hom).map (linePowerEvaluation L (n + 1)) ≫
    (Modules.pullbackObjUnitIso U.unop.hom).hom

/-- Degree-one frames of L, viewed as frames of L tensor the tensor unit.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrameDegreeOne {T : Scheme.{u}} {L : T.Modules} {U : T.ProEtᵒᵖ}
    (p : (lineFrames L).obj U) : (lineFrames (lineIntegralPower L 1)).obj U :=
  lineFrameOfLocalIso (lineFrameLocalIso p ≪≫
    (Modules.pullback U.unop.hom).mapIso (ρ_ L).symm)

/-- Postcomposition of a frame by an isomorphism of line bundles.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrameTransport {T : Scheme.{u}} {L M : T.Modules} (e : L ≅ M)
    {U : T.ProEtᵒᵖ} (p : (lineFrames L).obj U) : (lineFrames M).obj U :=
  lineFrameOfLocalIso (lineFrameLocalIso p ≪≫ (Modules.pullback U.unop.hom).mapIso e)

/-- Pulling a frame to the chosen base-change object. This retains the canonical
pullback-composition isomorphisms, rather than choosing a new frame.
Source: Stacks 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def lineFrameBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (U : Y.ProEtᵒᵖ) (p : (lineFrames L).obj U) :
    (lineFrames ((Modules.pullback f).obj L)).obj
      (op ((proEtaleBaseChange f).obj U.unop)) :=
  lineFrameOfLocalIso
    ((Modules.pullbackObjUnitIso (pullback.fst U.unop.hom f)).symm ≪≫
      (Modules.pullback (pullback.fst U.unop.hom f)).mapIso (lineFrameLocalIso p) ≪≫
      (Modules.pullbackComp (pullback.fst U.unop.hom f) U.unop.hom).app L ≪≫
      (Modules.pullbackCongr (pullback.condition (f := U.unop.hom) (g := f))).app L ≪≫
      (Modules.pullbackComp (pullback.snd U.unop.hom f) f).symm.app L)

/-- An extension on the specific sheafified graded frames. Its generating multiplication
laws express tensoring positive frames and inverse dual frames, and so determine all
integer-degree products. The specified degree-one fibre is the actual frame sheaf.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
structure LineFrameExtension (T : Scheme.{u}) (L : T.Modules) where
  middle : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}
  inclusion : proEtaleUnitsSheaf T ⟶ middle
  degree : middle ⟶ lineIntegerSheaf T
  zero : inclusion ≫ degree = 0
  shortExact : (ShortComplex.mk inclusion degree zero).ShortExact
  gradedIso : lineGradedFrameSheaf L ≅
    (sheafCompose (ProEt.topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj middle
  frame (a : ℤ) (U : T.ProEtᵒᵖ) : (lineFrames (lineIntegralPower L a)).obj U →
    middle.obj.obj U
  frame_eq (a : ℤ) (U : T.ProEtᵒᵖ) (p : (lineFrames (lineIntegralPower L a)).obj U) :
    frame a U p = gradedIso.hom.hom.app U
      ((toSheafify (ProEt.topology T) (lineGradedFrames L)).app U
        ((Sigma.ι (fun b : ℤ => lineFrames (lineIntegralPower L b)) a).app U p))
  degree_frame (a : ℤ) (U : T.ProEtᵒᵖ) (p : (lineFrames (lineIntegralPower L a)).obj U) :
    degree.hom.app U (frame a U p) = lineDegreeSection T a U
  unit_frame (U : T.ProEtᵒᵖ) (g : (proEtaleUnitsSheaf T).obj.obj U) :
    frame 0 U (lineUnitFrame U g) = inclusion.hom.app U g
  positive_product (a b : ℕ) (U : T.ProEtᵒᵖ)
      (p : (lineFrames (L.tensorPow a)).obj U) (q : (lineFrames (L.tensorPow b)).obj U) :
    frame (a : ℤ) U p + frame (b : ℤ) U q =
      frame ((a + b : ℕ) : ℤ) U (linePositiveFrameProduct L a b U p q)
  opposite_product (n : ℕ) (U : T.ProEtᵒᵖ)
      (p : (lineFrames (L.tensorPow (n + 1))).obj U)
      (q : (lineFrames ((Modules.dual L).tensorPow (n + 1))).obj U)
      (h : lineOppositeFrameEvaluation L n U p q = 𝟙 _) :
    frame ((n + 1 : ℕ) : ℤ) U p + frame (.negSucc n) U q = 0
  fibre_one (U : T.ProEtᵒᵖ) : Function.Bijective
    (fun p : (lineFrames L).obj U =>
      (⟨frame 1 U (lineFrameDegreeOne p), degree_frame 1 U (lineFrameDegreeOne p)⟩ :
        {x : middle.obj.obj U // degree.hom.app U x = lineDegreeSection T 1 U}))

/-- The degree-one frame inclusion in an extension.
Source: Stacks 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
def LineFrameExtension.frameOne {T : Scheme.{u}} {L : T.Modules}
    (E : LineFrameExtension T L) (U : T.ProEtᵒᵖ) (p : (lineFrames L).obj U) :
    E.middle.obj.obj U :=
  E.frame 1 U (lineFrameDegreeOne p)

/-- A family of actual graded-frame extensions, with their canonical maps. The units
map is specified on every section, and pullback is a pushout before localization.
Source: Stacks 03AJ, 01CD (blueprint: lem-pur-equivariant-line-extension). -/
structure LineFrameExtensionSystem where
  extension (T : Scheme.{u}) (L : T.Modules) [L.IsInvertible] : LineFrameExtension T L
  transport {T : Scheme.{u}} {L M : T.Modules} [L.IsInvertible] [M.IsInvertible]
    (e : L ≅ M) : (extension T L).middle ≅ (extension T M).middle
  transport_inclusion {T : Scheme.{u}} {L M : T.Modules} [L.IsInvertible] [M.IsInvertible]
      (e : L ≅ M) :
    (extension T L).inclusion ≫ (transport e).hom = (extension T M).inclusion
  transport_degree {T : Scheme.{u}} {L M : T.Modules} [L.IsInvertible] [M.IsInvertible]
      (e : L ≅ M) :
    (transport e).hom ≫ (extension T M).degree = (extension T L).degree
  transport_frame {T : Scheme.{u}} {L M : T.Modules} [L.IsInvertible] [M.IsInvertible]
      (e : L ≅ M) (U : T.ProEtᵒᵖ) (p : (lineFrames L).obj U) :
    (transport e).hom.hom.app U ((extension T L).frameOne U p) =
      (extension T M).frameOne U (lineFrameTransport e p)
  transport_id (T : Scheme.{u}) (L : T.Modules) [L.IsInvertible] :
    transport (Iso.refl L) = Iso.refl _
  transport_comp {T : Scheme.{u}} {L M N : T.Modules}
      [L.IsInvertible] [M.IsInvertible] [N.IsInvertible] (e : L ≅ M) (d : M ≅ N) :
    transport (e ≪≫ d) = transport e ≪≫ transport d
  unitsDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleUnitsSheaf Y ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj (proEtaleUnitsSheaf X)
  unitsDirect_value {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEtᵒᵖ)
      (g : (proEtaleUnitsSheaf Y).obj.obj U) :
    (unitsDirect f).hom.app U g =
      ULift.up (Additive.ofMul (Units.map
        (pullback.fst U.unop.hom f).appTop.hom.toMonoidHom (Additive.toMul g.down)))
  unitsPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj (proEtaleUnitsSheaf Y) ⟶
      proEtaleUnitsSheaf X
  unitsPull_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    unitsPull f = ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      (unitsDirect f)
  pull {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).obj (extension Y L).middle ⟶
      (extension X ((Modules.pullback f).obj L)).middle
  pull_inclusion {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map (extension Y L).inclusion ≫
      pull f L = unitsPull f ≫ (extension X ((Modules.pullback f).obj L)).inclusion
  pull_degree {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    pull f L ≫ (extension X ((Modules.pullback f).obj L)).degree =
      (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map (extension Y L).degree ≫
        proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  pull_frame {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible]
      (U : Y.ProEtᵒᵖ) (p : (lineFrames L).obj U) :
    (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _ (pull f L)).hom.app U)
        ((extension Y L).frameOne U p) =
      (extension X ((Modules.pullback f).obj L)).frameOne
        (op ((proEtaleBaseChange f).obj U.unop)) (lineFrameBaseChange f L U p)
  pull_pushout {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) [L.IsInvertible] :
    IsPushout
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} f).map (extension Y L).inclusion)
      (unitsPull f) (pull f L) (extension X ((Modules.pullback f).obj L)).inclusion
  pull_transport {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}
      [L.IsInvertible] [M.IsInvertible] (e : L ≅ M) :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} f).map (transport e).hom ≫ pull f M =
      pull f L ≫ (transport ((Modules.pullback f).mapIso e)).hom
  pull_id (T : Scheme.{u}) (L : T.Modules) [L.IsInvertible] :
    pull (𝟙 T) L ≫ (transport (L := (Modules.pullback (𝟙 T)).obj L) (M := L)
      ((Modules.pullbackId T).app L :
      (Modules.pullback (𝟙 T)).obj L ≅ L)).hom =
      (ProEtale.upperStarId AddCommGrpCat.{u + 1} T).hom.app (extension T L).middle
  pull_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
      (L : Z.Modules) [L.IsInvertible] :
    pull (g ≫ f) L ≫ (transport (L := (Modules.pullback (g ≫ f)).obj L)
      (M := (Modules.pullback g).obj ((Modules.pullback f).obj L))
      ((Modules.pullbackComp g f).symm.app L :
      (Modules.pullback (g ≫ f)).obj L ≅
        (Modules.pullback g).obj ((Modules.pullback f).obj L))).hom =
      (ProEtale.upperStarComp AddCommGrpCat.{u + 1} g f).hom.app (extension Z L).middle ≫
        (ProEtale.upperStar AddCommGrpCat.{u + 1} g).map (pull f L) ≫
          pull g ((Modules.pullback f).obj L)

/-- The induced linearization on the ordinary scheme-module pullback.
Source: Stacks 01CD (blueprint: lem-pur-equivariant-line-extension). -/
def linePullbackLinearization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (σ : Y ≅ Y) (σ' : X ≅ X) (h : σ'.hom ≫ f = f ≫ σ.hom)
    (L : Y.Modules) (lin : (Modules.pullback σ.hom).obj L ≅ L) :
    (Modules.pullback σ'.hom).obj ((Modules.pullback f).obj L) ≅
      (Modules.pullback f).obj L :=
  (Modules.pullbackComp σ'.hom f).app L ≪≫ (Modules.pullbackCongr h).app L ≪≫
    (Modules.pullbackComp f σ.hom).symm.app L ≪≫ (Modules.pullback f).mapIso lin

/-- The canonical commuting comparison for inverse images of an equivariant map.
Source: Stacks 00X6 (blueprint: lem-pur-equivariant-line-extension). -/
@[irreducible]
def lineEquivariantInverseImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (σ : Y ≅ Y) (σ' : X ≅ X) (h : σ'.hom ≫ f = f ≫ σ.hom) :
    ProEtale.upperStar AddCommGrpCat.{u + 1} f ⋙
        ProEtale.upperStar AddCommGrpCat.{u + 1} σ'.hom ≅
      ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom ⋙
        ProEtale.upperStar AddCommGrpCat.{u + 1} f :=
  (ProEtale.upperStarComp AddCommGrpCat.{u + 1} σ'.hom f).symm ≪≫
    ProEtale.upperStarCongr AddCommGrpCat.{u + 1} h ≪≫
      ProEtale.upperStarComp AddCommGrpCat.{u + 1} f σ.hom

/-- The actual short exact sequence in the fixed-pair category. Each structure map is
specified, including its degree-zero and integer normalizations. The middle map is
pullback of frames followed by the given linearization; its tensor powers then specify
all degrees by the multiplication laws of LineFrameExtension.
Source: Stacks 03AJ, 0152 (blueprint: lem-pur-equivariant-line-extension). -/
structure NativeLineFrameExtension (S : LineFrameExtensionSystem.{u})
    (T : Scheme.{u}) (σ : T ≅ T) (L : T.Modules) [L.IsInvertible]
    (lin : (Modules.pullback σ.hom).obj L ≅ L) where
  unitsStructure :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom).obj
      (proEtaleUnitsSheaf T) ≅ proEtaleUnitsSheaf T
  integersStructure :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom).obj
      (lineIntegerSheaf T) ≅ lineIntegerSheaf T
  middleStructure :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom).obj
      (S.extension T L).middle ≅ (S.extension T L).middle
  unitsStructure_eq : unitsStructure.hom = S.unitsPull σ.hom
  integersStructure_eq : integersStructure.hom =
    proEtaleConstantInverseImageMap σ.hom AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  middleStructure_eq : middleStructure.hom = S.pull σ.hom L ≫ (S.transport lin).hom
  inclusion : Endofunctor.IsoAlgebra.mk (proEtaleUnitsSheaf T) unitsStructure ⟶
    Endofunctor.IsoAlgebra.mk (S.extension T L).middle middleStructure
  degree : Endofunctor.IsoAlgebra.mk (S.extension T L).middle middleStructure ⟶
    Endofunctor.IsoAlgebra.mk (lineIntegerSheaf T) integersStructure
  inclusion_value : inclusion.hom.f = (S.extension T L).inclusion
  degree_value : degree.hom.f = (S.extension T L).degree
  zero : inclusion ≫ degree = 0
  shortExact : (ShortComplex.mk inclusion degree zero).ShortExact

/-- The native connecting arrow in the ordinary derived category of the fixed pairs.
The localization used here is HasDerivedCategory.standard, and the arrow is singleδ
of the actual short exact sequence, so it includes the single and shift comparisons.
Source: Stacks 0152 (blueprint: lem-pur-equivariant-line-extension). -/
def NativeLineFrameExtension.boundary {S : LineFrameExtensionSystem.{u}}
    {T : Scheme.{u}} {σ : T ≅ T} {L : T.Modules} [L.IsInvertible]
    {lin : (Modules.pullback σ.hom).obj L ≅ L} (N : NativeLineFrameExtension S T σ L lin) :=
  letI := HasDerivedCategory.standard
    (Endofunctor.IsoAlgebra (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom))
  N.shortExact.singleδ

/-- Equality of the native class after exact forgetting with the class of the actual
underlying extension. The Grothendieck instance supplies small Ext without a hypothesis.
Source: Stacks 0152 (blueprint: lem-pur-equivariant-line-extension). -/
def LineNativeBoundaryForgets {S : LineFrameExtensionSystem.{u}}
    {T : Scheme.{u}} {σ : T ≅ T} {L : T.Modules} [L.IsInvertible]
    {lin : (Modules.pullback σ.hom).obj L ≅ L} (N : NativeLineFrameExtension S T σ L lin) :
    Prop :=
  letI : IsGrothendieckAbelian.{u + 1}
      (Endofunctor.IsoAlgebra (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom)) :=
    Endofunctor.IsoAlgebra.isGrothendieckAbelian _
  N.shortExact.extClass.mapExactFunctor
      (Endofunctor.IsoAlgebra.forget (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom)) =
    (S.extension T L).shortExact.extClass

/-- The Cartier section, transported to a specified isomorphic line bundle.
Source: Stacks 0A45; blueprint diagonal-tower-system (1)
(blueprint: lem-pur-equivariant-line-extension). -/
def lineCartierSection {D T : Scheme.{u}} (i : D ⟶ T) {L : T.Modules}
    (e : L ≅ Modules.dual i.ker.toModules) : Modules.unit T ⟶ L :=
  Modules.dualUnitIso.inv ≫ Modules.dualMap i.ker.toModulesι ≫ e.inv

/-- A frame of the canonical Cartier section on an object off the divisor.
The equality is stated on the actual morphism; it does not choose an equation of D.
Source: Stacks 0A45 (blueprint: lem-pur-equivariant-line-extension). -/
def IsLineCartierComplementFrame {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] {L : T.Modules}
    (e : L ≅ Modules.dual i.ker.toModules) (U : T.ProEtᵒᵖ)
    (p : (lineFrames L).obj U) : Prop :=
  (∃ (v : U.unop.left ⟶ i.openComplement.toScheme), v ≫ i.openComplement.ι = U.unop.hom) ∧
    (lineFrameLocalIso p).hom =
      (Modules.pullbackObjUnitIso U.unop.hom).inv ≫
        (Modules.pullback U.unop.hom).map (lineCartierSection i e)

/-- The relative Cartier extension is the universal quotient killing the canonical
complementary frame. Its supported integer structure is forced by equivariance of the
canonical epic restriction map. The displayed pullback square identifies the whole-space
extension with its pullback, hence identifies the corresponding derived classes.
Source: latest blueprint diagonal-tower-system (1), Stacks 03AJ
(blueprint: lem-pur-equivariant-line-extension). -/
structure NativeLineCartierQuotient {S : LineFrameExtensionSystem.{u}}
    {T : Scheme.{u}} {σ : T ≅ T} {L : T.Modules} [L.IsInvertible]
    {lin : (Modules.pullback σ.hom).obj L ≅ L}
    (N : NativeLineFrameExtension S T σ L lin) {D : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (e : L ≅ Modules.dual i.ker.toModules) where
  supportedStructure :
    (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom).obj
        ((proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).obj (lineIntegerSheaf D)) ≅
      (proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).obj (lineIntegerSheaf D)
  restriction : Endofunctor.IsoAlgebra.mk (lineIntegerSheaf T) N.integersStructure ⟶
    Endofunctor.IsoAlgebra.mk
      ((proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).obj (lineIntegerSheaf D))
      supportedStructure
  restriction_value : restriction.hom.f =
    proEtaleConstantDirectImageMap i AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  middle : Endofunctor.IsoAlgebra
    (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom)
  quotient : Endofunctor.IsoAlgebra.mk (S.extension T L).middle N.middleStructure ⟶ middle
  inclusion : Endofunctor.IsoAlgebra.mk (proEtaleUnitsSheaf T) N.unitsStructure ⟶ middle
  degree : middle ⟶ Endofunctor.IsoAlgebra.mk
    ((proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}).obj (lineIntegerSheaf D))
    supportedStructure
  zero : inclusion ≫ degree = 0
  shortExact : (ShortComplex.mk inclusion degree zero).ShortExact
  inclusion_quotient : N.inclusion ≫ quotient = inclusion
  degree_quotient : quotient ≫ degree = N.degree ≫ restriction
  kills_frame (U : T.ProEtᵒᵖ) (p : (lineFrames L).obj U)
      (hp : IsLineCartierComplementFrame i e U p) :
    quotient.hom.f.hom.app U ((S.extension T L).frameOne U p) = 0
  universal (A : Endofunctor.IsoAlgebra
      (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom))
      (h : Endofunctor.IsoAlgebra.mk (S.extension T L).middle N.middleStructure ⟶ A)
      (hk : ∀ (U : T.ProEtᵒᵖ) (p : (lineFrames L).obj U),
        IsLineCartierComplementFrame i e U p →
          h.hom.f.hom.app U ((S.extension T L).frameOne U p) = 0) :
    ∃! a : middle ⟶ A, quotient ≫ a = h
  pullback : IsPullback quotient N.degree degree restriction

/-- The native short complex, retaining its fixed-pair objects.
Source: Stacks 0152 (blueprint: lem-pur-equivariant-line-extension). -/
def NativeLineFrameExtension.sequence {S : LineFrameExtensionSystem.{u}}
    {T : Scheme.{u}} {σ : T ≅ T} {L : T.Modules} [L.IsInvertible]
    {lin : (Modules.pullback σ.hom).obj L ≅ L} (N : NativeLineFrameExtension S T σ L lin) :
    ShortComplex (Endofunctor.IsoAlgebra
      (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom)) :=
  ShortComplex.mk N.inclusion N.degree N.zero

/-- An actual native comparison of extensions, with specified underlying maps and
an actual pushout square. Abstract category parameters keep the normalization of the
forgetful comparison separate from the construction of a particular inverse image.
Source: Stacks 01CD, 0152 (blueprint: lem-pur-equivariant-line-extension). -/
@[irreducible]
def lineNativePushoutComparison
    {C : Type v} [Category.{w} C] [Preadditive C]
    {D : Type v'} [Category.{w'} D] [Preadditive D]
    {F : C ⥤ C} {G : D ⥤ D} {P : C ⥤ D} [F.Additive] [G.Additive]
    (e : P ⋙ G ≅ F ⋙ P)
    (A : ShortComplex (Endofunctor.IsoAlgebra F))
    (B : ShortComplex (Endofunctor.IsoAlgebra G))
    (k : P.obj A.X₁.carrier ⟶ B.X₁.carrier)
    (m : P.obj A.X₂.carrier ⟶ B.X₂.carrier)
    (q : P.obj A.X₃.carrier ⟶ B.X₃.carrier) : Prop :=
  let H := Endofunctor.IsoAlgebra.mapOfNatIso e
  let c := Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso e
  ∃ (kernelMap : H.obj A.X₁ ⟶ B.X₁)
    (middleMap : H.obj A.X₂ ⟶ B.X₂)
    (quotientMap : H.obj A.X₃ ⟶ B.X₃),
    H.map A.f ≫ middleMap = kernelMap ≫ B.f ∧
    H.map A.g ≫ quotientMap = middleMap ≫ B.g ∧
    kernelMap.hom.f = c.hom.app A.X₁ ≫ k ∧
    middleMap.hom.f = c.hom.app A.X₂ ≫ m ∧
    quotientMap.hom.f = c.hom.app A.X₃ ≫ q ∧
    IsPushout (H.map A.f) kernelMap middleMap B.f

/-- The native pullback comparison is a map of actual sequences and a pushout on
kernels, with all three underlying maps fixed. In particular no arbitrary derived
lift or isomorphism of extension classes replaces the comparison.
Source: Stacks 01CD, 03AJ (blueprint: lem-pur-equivariant-line-extension). -/
@[irreducible]
def NativeLineExtensionPullback {S : LineFrameExtensionSystem.{u}}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ≅ Y) (σ' : X ≅ X)
    (h : σ'.hom ≫ f = f ≫ σ.hom) (L : Y.Modules) [L.IsInvertible]
    (lin : (Modules.pullback σ.hom).obj L ≅ L)
    (N : NativeLineFrameExtension S Y σ L lin)
    (N' : NativeLineFrameExtension S X σ' ((Modules.pullback f).obj L)
      (linePullbackLinearization f σ σ' h L lin)) : Prop :=
  lineNativePushoutComparison (lineEquivariantInverseImageComparison f σ σ' h)
    N.sequence N'.sequence (S.unitsPull f) (S.pull f L)
    (proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The relative Cartier class pulls back along the canonical supported restriction.
Ext is taken in the native fixed-pair category, with its small Grothendieck model.
Source: Stacks 06XU; latest blueprint diagonal-tower-system (1)
(blueprint: lem-pur-equivariant-line-extension). -/
def NativeLineCartierQuotient.classFormula {S : LineFrameExtensionSystem.{u}}
    {T : Scheme.{u}} {σ : T ≅ T} {L : T.Modules} [L.IsInvertible]
    {lin : (Modules.pullback σ.hom).obj L ≅ L}
    {N : NativeLineFrameExtension S T σ L lin} {D : Scheme.{u}} {i : D ⟶ T}
    [IsClosedImmersion i] {e : L ≅ Modules.dual i.ker.toModules}
    (Q : NativeLineCartierQuotient N i e) : Prop :=
  letI : IsGrothendieckAbelian.{u + 1}
      (Endofunctor.IsoAlgebra (ProEtale.upperStar AddCommGrpCat.{u + 1} σ.hom)) :=
    Endofunctor.IsoAlgebra.isGrothendieckAbelian _
  (Ext.mk₀ Q.restriction).comp Q.shortExact.extClass (zero_add 1) = N.shortExact.extClass

/-- The ordinary graded-frame extension system exists by the local frame construction.
Source: Stacks 03AJ, fibre-over-one extension construction
(blueprint: lem-pur-equivariant-line-extension). -/
theorem ordinary_line_frame_extension_system : Nonempty LineFrameExtensionSystem.{u} := by
  sorry

/-- The remaining native, comparison, Picard, and Cartier coherence data for an
ordinary graded-frame system.  This is strictly smaller than the full system
because the ordinary system is supplied.
Source: Stacks 0152, 01CD, 02FQ and latest blueprint diagonal-tower-system (1)
(blueprint: lem-pur-equivariant-line-extension). -/
structure EquivariantLineExtensionRemainder (S : LineFrameExtensionSystem.{u}) where
  native (T : Scheme.{u}) (σ : T ≅ T) (L : T.Modules) [L.IsInvertible]
    (lin : (Modules.pullback σ.hom).obj L ≅ L) : NativeLineFrameExtension S T σ L lin
  forget_boundary (T : Scheme.{u}) (σ : T ≅ T) (L : T.Modules) [L.IsInvertible]
      (lin : (Modules.pullback σ.hom).obj L ≅ L) :
    LineNativeBoundaryForgets (native T σ L lin)
  transport_native (T : Scheme.{u}) (σ : T ≅ T) (L M : T.Modules)
      [L.IsInvertible] [M.IsInvertible]
      (lin : (Modules.pullback σ.hom).obj L ≅ L)
      (μ : (Modules.pullback σ.hom).obj M ≅ M) (e : L ≅ M)
      (he : lin.hom ≫ e.hom = (Modules.pullback σ.hom).map e.hom ≫ μ.hom) :
    ∃ q : (native T σ L lin).sequence ≅ (native T σ M μ).sequence,
      q.hom.τ₁.hom.f = 𝟙 _ ∧ q.hom.τ₂.hom.f = (S.transport e).hom ∧
        q.hom.τ₃.hom.f = 𝟙 _
  pull_native {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ≅ Y) (σ' : X ≅ X)
      (h : σ'.hom ≫ f = f ≫ σ.hom) (L : Y.Modules) [L.IsInvertible]
      (lin : (Modules.pullback σ.hom).obj L ≅ L) :
    NativeLineExtensionPullback f σ σ' h L lin (native Y σ L lin)
      (native X σ' ((Modules.pullback f).obj L)
        (linePullbackLinearization f σ σ' h L lin))
  comparisonConstant (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅ lineIntegerSheaf T
  comparisonConstant_normalization (T : Scheme.{u}) :
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (comparisonConstant T).hom =
      ((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).symm
        (Functor.whiskerLeft (toProEt T).op
          (toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
  comparisonUnits (T : Scheme.{u}) :
    (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T).obj T.gmSheaf ⟶
      proEtaleUnitsSheaf T
  comparisonUnits_normalization (T : Scheme.{u}) :
    (ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
      (comparisonUnits T) = ⟨𝟙 _⟩
  positive_class (T : Scheme.{u}) (L : T.Modules) [L.IsInvertible] :
    (S.extension T L).shortExact.extClass =
      ((Ext.mk₀ (comparisonConstant T).inv).comp
        ((Pic.toCohomologicalPicardGroup T (Pic.ofIsInvertible L)).mapExactFunctor
          (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} T)) (zero_add 1)).comp
            (Ext.mk₀ (comparisonUnits T)) (add_zero 1)
  cartier (T : Scheme.{u}) (σ : T ≅ T) (L : T.Modules) [L.IsInvertible]
      (lin : (Modules.pullback σ.hom).obj L ≅ L) {D : Scheme.{u}} (i : D ⟶ T)
      [IsClosedImmersion i] (hI : i.ker.IsInvertible)
      (e : L ≅ Modules.dual i.ker.toModules)
      (hlin : (Modules.pullback σ.hom).map (lineCartierSection i e) ≫ lin.hom =
        (Modules.pullbackObjUnitIso σ.hom).hom ≫ lineCartierSection i e) :
    NativeLineCartierQuotient (native T σ L lin) i e
  cartier_class (T : Scheme.{u}) (σ : T ≅ T) (L : T.Modules) [L.IsInvertible]
      (lin : (Modules.pullback σ.hom).obj L ≅ L) {D : Scheme.{u}} (i : D ⟶ T)
      [IsClosedImmersion i] (hI : i.ker.IsInvertible)
      (e : L ≅ Modules.dual i.ker.toModules)
      (hlin : (Modules.pullback σ.hom).map (lineCartierSection i e) ≫ lin.hom =
        (Modules.pullbackObjUnitIso σ.hom).hom ≫ lineCartierSection i e) :
    (cartier T σ L lin i hI e hlin).classFormula

/-- The native and comparison coherence data exists by the equivariant frame and
Cartier construction.  The local frame gluing and fixed-pair exactness are
independent obstacles from the ordinary construction.
Source: Stacks 01CD, 0152, 02FQ and latest blueprint diagonal-tower-system (1)
(blueprint: lem-pur-equivariant-line-extension). -/
theorem equivariant_line_extension_remainder (S : LineFrameExtensionSystem.{u}) :
    Nonempty (EquivariantLineExtensionRemainder S) := by
  sorry

end AlgebraicGeometry.Scheme
