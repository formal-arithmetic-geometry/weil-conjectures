/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.PodHomChainCounitFormula
public import Sheaf.Paper.CoefficientGammaRepresentatives

/-! # Coordinates for composition of the Verdier Hom chain

These are the existing canonical constructions, exposed independently of the composition
proof so that its two transpose calculations can be stated without an import cycle.
Source: fix-prop-coherence.proof.md, adjoint-mate sentence
(blueprint: def-sf-verdier-hom-composition-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.VerdierHomChainComposition
open TensorHomCoefficientTransposes

variable {D : FiniteFieldDatum.{u}} {B : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic B.l) E]
  [FiniteDimensional (Padic B.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D B E n hn) (s : PodCoefficientStage)

/-- Naturality in the tensor factor of a presentation of the recorded partial tensor.
Each component is already natural in the test variable. This is the other variable
of the one tensor comparison on a space, including transport along support compositors.
Source: the natural tensor comparisons used in the projection associativity pentagon
(blueprint: def-sf-verdier-hom-composition-coordinates). -/
def TensorPresentationNatural (W : SixFunctorSpace D)
    (C : SixFunctorClosedDomain (PodCoefficientStage.domain S s W)
      (PodCoefficientStage.homPairs (S := S) s W)
      (PodCoefficientStage.internalHom (S := S) s W))
    (tensor : ∀ K : (PodCoefficientStage.domain S s W).FullSubcategory,
      @MonoidalCategory.tensorLeft _ _ C.closed.monoidal K ⋙
        (PodCoefficientStage.domain S s W).ι ≅ (PodCoefficientStage.tensor S s W).obj K.obj) :
    Prop :=
  ∀ (K L T : (PodCoefficientStage.domain S s W).FullSubcategory) (a : K ⟶ L),
    (PodCoefficientStage.domain S s W).ι.map
        (@MonoidalCategory.whiskerRight _ _ C.closed.monoidal.toMonoidalCategoryStruct
          _ _ a T) ≫ (tensor L).hom.app T =
      (tensor K).hom.app T ≫
        ((PodCoefficientStage.tensor S s W).map
          ((PodCoefficientStage.domain S s W).ι.map a)).app T

/-- Identify tensors after equality of the whole closed presentation.
Source: the shared-presentation hypotheses of the composition law
(blueprint: def-sf-verdier-hom-composition-coordinates). -/
def tensorCoordinate {W : SixFunctorSpace D}
    {C C' : SixFunctorClosedDomain (PodCoefficientStage.domain S s W)
      (PodCoefficientStage.homPairs (S := S) s W)
      (PodCoefficientStage.internalHom (S := S) s W)}
    (h : C = C') (M T : (PodCoefficientStage.domain S s W).FullSubcategory) :
    (tensorLeft C.closed.monoidal M).obj T ≅
      (tensorLeft C'.closed.monoidal M).obj T :=
  eqToIso (congrArg (fun A ↦ (tensorLeft A.closed.monoidal M).obj T) h)

section OneMap
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (R : Domain S s f c)

/-- The displayed forward chain, on the actual full finite-Tor test category.
The fourth step of the inverse chain precomposes with PF; consequently this
forward chain precomposes with PF inverse.
Source: node statement and proof step 1 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def chain (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  (PodHomChain.homEquiv S s f c R M N T).symm

/-- Evaluate the specified forward chain on the identity of its representing object.
This is a real arrow; no arbitrary isomorphism is selected.
Source: proof step 2 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def forward (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Y).FullSubcategory) :=
  chain S s f c R M N _ (𝟙 _)

/-- Dualizing specialization of the chain, with the specified comparison in its
second Hom variable. Source: proof step 5
(blueprint: def-sf-verdier-hom-composition-coordinates). -/
def epsilon (omegaY : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (omegaX : (PodCoefficientStage.domain S s X).FullSubcategory)
    (dualizing : R.exceptional.obj omegaY ≅ omegaX)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory) :=
  forward S s f c R M omegaY ≫
    R.direct.map ((PodCtfPairing.homX S s f c R M).map dualizing.hom)

end OneMap

section TwoMaps
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
  [QuasiCompact (f ≫ g).hom.left]
  (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
  (cx : Compactification (f ≫ g).hom.left)
  (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)

/-- Restrict the specified compact-support compositor through the full inclusion.
Source: proof steps 3--4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def supportComposition : Rx.support ≅ Rf.support ⋙ Rg.support :=
  ((PodCoefficientStage.domain S s Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (PodCoefficientStage.domain S s X).ι
      ((PodCoefficientStage.operations S s).composition f g cf cg cx))

/-- Restrict the canonical pullback compositor through the full inclusion.
Source: proof steps 3--4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def pullComposition : Rx.pull ≅ Rg.pull ⋙ Rf.pull :=
  ((PodCoefficientStage.domain S s X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (PodCoefficientStage.domain S s Z).ι
      ((PodCoefficientStage.operations S s).pullComposition f g))

/-- The direct-image compositor is the right-adjoint comparison for the specified
pullback compositor; it has the pasted ordinary counit.
Source: proof step 3 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def directComposition : Rx.direct ≅ Rf.direct ⋙ Rg.direct :=
  Rx.ordinaryAdjunction.rightAdjointUniq
    ((Rg.ordinaryAdjunction.comp Rf.ordinaryAdjunction).ofNatIsoLeft
      (pullComposition S s f g cf cg cx Rf Rg Rx).symm)

/-- Conjugate compact-support composition under the specified exceptional adjunctions.
Source: proof step 4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def exceptionalComposition : Rx.exceptional ≅ Rg.exceptional ⋙ Rf.exceptional :=
  Rx.exceptionalAdjunction.rightAdjointUniq
    ((Rf.exceptionalAdjunction.comp Rg.exceptionalAdjunction).ofNatIsoLeft
      (supportComposition S s f g cf cg cx Rf Rg Rx).symm)

/-- The source coordinate of the pasted chain, using exceptional conjugation in
RHom's second variable, followed by ordinary direct-image composition.
Source: proof steps 3--4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def sourceCoordinate
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Z).FullSubcategory) :
    (PodHomChain.sourceFunctor S s (f ≫ g) cx Rx M).obj N ≅
      Rg.direct.obj ((PodHomChain.sourceFunctor S s f cf Rf M).obj
        (Rg.exceptional.obj N)) :=
  Rx.direct.mapIso ((PodCtfPairing.homX S s (f ≫ g) cx Rx M).mapIso
    ((exceptionalComposition S s f g cf cg cx Rf Rg Rx).app N)) ≪≫
      (directComposition S s f g cf cg cx Rf Rg Rx).app
        ((PodCtfPairing.homX S s f cf Rf M).obj (Rf.exceptional.obj (Rg.exceptional.obj N)))

/-- The target coordinate is contravariant internal Hom applied to the inverse
support compositor. Source: proof steps 3--4
(blueprint: def-sf-verdier-hom-composition-coordinates). -/
def targetCoordinate
    (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N : (PodCoefficientStage.domain S s Z).FullSubcategory) :
    (PodHomChain.targetFunctor S s (f ≫ g) cx Rx M).obj N ≅
      (PodHomChain.targetFunctor S s g cg Rg (Rf.support.obj M)).obj N :=
  ((Functor.curry.obj (sixFunctorDomainHom _ _ _
    Rx.closedY.homPermitted Rx.closedY.homDomain)).flip.obj N).mapIso
      ((supportComposition S s f g cf cg cx Rf Rg Rx).app M).symm.op

/-- Equality on every input arrow of the one-map and successive forward Hom chains.
The test category includes each representing object, so this includes identity tests.
Source: proof steps 3--4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def ChainComposition : Prop :=
  ∀ (M : (PodCoefficientStage.domain S s X).FullSubcategory)
    (N T : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (v : T ⟶ (PodHomChain.targetFunctor S s (f ≫ g) cx Rx M).obj N),
    chain S s (f ≫ g) cx Rx M N T v ≫
        (sourceCoordinate S s f g cf cg cx Rf Rg Rx M N).hom =
      chain S s g cg Rg (Rf.support.obj M) N T
          (v ≫ (targetCoordinate S s f g cf cg cx Rf Rg Rx M N).hom) ≫
        Rg.direct.map (forward S s f cf Rf M (Rg.exceptional.obj N))

/-- The dualizing comparison for a composite in the same composition coordinates.
It is exceptional conjugation followed by f!c_g and c_f, without a new choice.
Source: proof step 5 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def dualizingComposition
    (OX : (PodCoefficientStage.domain S s X).FullSubcategory)
    (OY : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (OZ : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (df : Rf.exceptional.obj OY ≅ OX) (dg : Rg.exceptional.obj OZ ≅ OY) :
    Rx.exceptional.obj OZ ≅ OX :=
  (exceptionalComposition S s f g cf cg cx Rf Rg Rx).app OZ ≪≫
    Rf.exceptional.mapIso dg ≪≫ df

/-- The precise Verdier composition equation, with the ordinary compositor exposed.
The dualizing objects may in particular be the exceptional images of the coefficient
unit along the three structure maps; the conjugate cocycle supplies dualizingComposition.
Source: proof step 5 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def VerdierComposition : Prop :=
  ∀ (OX : (PodCoefficientStage.domain S s X).FullSubcategory)
    (OY : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (OZ : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (df : Rf.exceptional.obj OY ≅ OX) (dg : Rg.exceptional.obj OZ ≅ OY)
    (M : (PodCoefficientStage.domain S s X).FullSubcategory),
    epsilon S s (f ≫ g) cx Rx OZ OX
        (dualizingComposition S s f g cf cg cx Rf Rg Rx OX OY OZ df dg) M ≫
        (directComposition S s f g cf cg cx Rf Rg Rx).hom.app
          ((PodCtfPairing.homX S s f cf Rf M).obj OX) =
      (targetCoordinate S s f g cf cg cx Rf Rg Rx M OZ).hom ≫
        epsilon S s g cg Rg OZ OY dg (Rf.support.obj M) ≫
        Rg.direct.map (epsilon S s f cf Rf OY OX df M)

end TwoMaps

end WeilConjectures.VerdierHomChainComposition
