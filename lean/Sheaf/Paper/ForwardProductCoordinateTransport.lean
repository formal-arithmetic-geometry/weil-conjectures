/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.Paper.FiniteProductCompactification
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.Paper.CompactificationCoherence
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.PfRefinementCompatibility
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.Paper.CompactSupportSiteCoherence
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange

/-! # Coordinates and choice transport of the forward compact-support product

Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, opening and symmetry paragraphs
(blueprint: lem-pur-product-forward-coordinate-transport).

The auxiliary maps below are composites of the existing canonical operations. In particular,
the forward map is the existing six-factor map, not an ordinary external product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ForwardProductCoordinates

variable {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
variable (cf : Compactification f) (cg : Compactification g)

/-- The canonical open i:Xbar times_B Z to Xbar times_B Zbar.
Source: the product diagram (blueprint: lem-pur-product-forward-coordinate-transport). -/
def middleOpen : pullback cf.g g ⟶ pullback cf.g cg.g :=
  pullback.lift (pullback.fst cf.g g) (pullback.snd cf.g g ≫ cg.i)
    (by rw [Category.assoc, ← cg.comm]; exact pullback.condition)

/-- The Cartesian square displaying i as the base change of k.
Source: the product diagram (blueprint: lem-pur-product-forward-coordinate-transport). -/
abbrev middleSquare : IsPullback (pullback.snd cf.g g) (middleOpen cf cg)
    cg.i (pullback.snd cf.g cg.g) :=
  IsPullback.of_bot
    (by simpa only [middleOpen, pullback.lift_fst, ← cg.comm] using
      (IsPullback.of_hasPullback cf.g g).flip)
    (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback cf.g cg.g).flip

/-- Openness follows by base change of the chosen open k.
Source: the product diagram (blueprint: lem-pur-product-forward-coordinate-transport). -/
instance middleOpen_isOpenImmersion : IsOpenImmersion (middleOpen cf cg) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (middleSquare cf cg) inferInstance

/-- The chosen open of g is quasi-compact because g is quasi-compact.
Source: finite-type compactifications
(blueprint: lem-pur-product-forward-coordinate-transport). -/
instance rightOpen_quasiCompact [QuasiCompact g] : QuasiCompact cg.i :=
  cg.quasiCompact_openImmersion inferInstance

/-- Quasi-compactness follows by the same base change; g is finite type.
Source: the finite-type hypotheses (blueprint: lem-pur-product-forward-coordinate-transport). -/
instance middleOpen_quasiCompact [QuasiCompact g] : QuasiCompact (middleOpen cf cg) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (middleSquare cf cg) inferInstance

/-- The commutative proper/open square, with its displayed order of composition.
Source: t i=k v (blueprint: lem-pur-product-forward-coordinate-transport). -/
abbrev middleComm : middleOpen cf cg ≫ pullback.snd cf.g cg.g =
    pullback.snd cf.g g ≫ cg.i :=
  pullback.lift_snd _ _ _

/-- The compactification of h using u=i j_q and c=b t.
Source: the induced product choice (blueprint: lem-pur-product-forward-coordinate-transport). -/
def productChoice : Compactification (pullback.snd f g ≫ g) where
  Z := pullback cf.g cg.g
  i := (cf.ofIsPullback (IsPullback.of_hasPullback f g)).i ≫ middleOpen cf cg
  g := pullback.snd cf.g cg.g ≫ cg.g
  comm := by
    rw [Category.assoc, ← Category.assoc _ (pullback.snd cf.g cg.g) cg.g,
      middleComm, Category.assoc, ← cg.comm, ← Category.assoc,
      Compactification.ofIsPullback_i_snd]
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (M : ProperOpenDerived A X) (N : ProperOpenDerived A Z)

/-- The specified B0, with the canonical pullback compositor P_k P_b=P_g inserted.
Source: B0 in the statement (blueprint: lem-pur-product-forward-coordinate-transport). -/
def exchange :
    (ProperOpenPull A cg.i).obj ((ProperOpenPull A cg.g).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (cf.ofIsPullback (IsPullback.of_hasPullback f g))).obj
        ((ProperOpenPull A (pullback.fst f g)).obj M) :=
  (finiteProductPullTriangleObj (ModuleCat.{u + 1} A) cg.i cg.g g cg.comm.symm _).hom ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback f g) cf).app M

/-- The existing open projection factor of a compactification, evaluated at its inputs.
This exposes delta_j followed by its canonical pullback-composition identification.
Source: def-exchange-projection, chosen-compactification projection formula
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def compactificationOpenFactor {U V : Scheme.{u}} {a : U ⟶ V}
    (c : Compactification a) (Q : ProperOpenDerived A U) (L : ProperOpenDerived A V) :
    ((ProperOpenTensor A c.Z).obj ((ProperOpenShriek A c.i).obj Q)).obj
      ((ProperOpenPull A c.g).obj L) ⟶
    (ProperOpenShriek A c.i).obj
      (((ProperOpenTensor A U).obj Q).obj ((ProperOpenPull A a).obj L)) :=
  finiteProductOpenProjection (ModuleCat.{u + 1} A) c.i Q
      ((ProperOpenPull A c.g).obj L) ≫
    finiteProductOpenMap (ModuleCat.{u + 1} A) c.i
      (finiteProductTensorMapRight (ModuleCat.{u + 1} A) U Q
        ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app L))

/-- The specified nu, including both signed symmetries and the normalized open tensor map.
Source: nu in the statement (blueprint: lem-pur-product-forward-coordinate-transport). -/
def nu :
    ((ProperOpenTensor A cg.Z).obj
      ((ProperOpenPull A cg.g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))).obj
      ((ProperOpenShriek A cg.i).obj N) ⟶
    (ProperOpenShriek A cg.i).obj
      (((ProperOpenTensor A Z).obj
        ((ProperOpenPull A cg.i).obj ((ProperOpenPull A cg.g).obj
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)))).obj N) :=
  finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) cg.Z
    ((ProperOpenPull A cg.g).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))
    ((ProperOpenShriek A cg.i).obj N) ≫
  (properOpenTensorIso A cg.i N ((ProperOpenPull A cg.g).obj
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))).hom ≫
  (ProperOpenShriek A cg.i).map
    (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) Z N
      ((ProperOpenPull A cg.i).obj ((ProperOpenPull A cg.g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))))

/-- The specified z, using the counit-defined proper projection for b and signed swaps.
Source: z in the statement (blueprint: lem-pur-product-forward-coordinate-transport). -/
def z :
    ((ProperOpenTensor A B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N) ⟶
    (ProperOpenPush A cg.g).obj
      (((ProperOpenTensor A cg.Z).obj
        ((ProperOpenPull A cg.g).obj
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))).obj
        ((ProperOpenShriek A cg.i).obj N)) :=
  finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) B
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N) ≫
  properOpenProjection A cg.g ((ProperOpenShriek A cg.i).obj N)
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) ≫
  (ProperOpenPush A cg.g).map
    (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) cg.Z
      ((ProperOpenShriek A cg.i).obj N)
      ((ProperOpenPull A cg.g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)))

/-- Psi is the composite of B0 tensor identity, the proper projection, the proper
image of the normalized open factor, and Gamma. This helper accepts the displayed
proper/open square and its B0 component; route below inserts the actual canonical exchange.
Source: Psi in the statement (blueprint: lem-pur-product-forward-coordinate-transport). -/
def psi {U V T : Scheme.{u}} {q : U ⟶ Z}
    (cq : Compactification q) (i : cq.Z ⟶ T) (t : T ⟶ V) (k : Z ⟶ V)
    [IsOpenImmersion i] [IsOpenImmersion k] [QuasiCompact i] [QuasiCompact k]
    [IsProper t] (h : i ≫ t = cq.g ≫ k)
    (L0 : ProperOpenDerived A V) (Q : ProperOpenDerived A U) (N0 : ProperOpenDerived A Z)
    (B0 : (ProperOpenPull A k).obj L0 ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cq).obj Q) :
    (ProperOpenShriek A k).obj
      (((ProperOpenTensor A Z).obj ((ProperOpenPull A k).obj L0)).obj N0) ⟶
    (ProperOpenPush A t).obj ((ProperOpenShriek A i).obj
      ((ProperOpenShriek A cq.i).obj
        (((ProperOpenTensor A U).obj Q).obj ((ProperOpenPull A q).obj N0)))) :=
  (ProperOpenShriek A k).map (((ProperOpenTensor A Z).map B0).app N0) ≫
  (ProperOpenShriek A k).map
    (properOpenProjection A cq.g ((ProperOpenShriek A cq.i).obj Q) N0) ≫
  (ProperOpenShriek A k).map
    ((ProperOpenPush A cq.g).map (compactificationOpenFactor A cq Q N0)) ≫
  (properOpenMate A i cq.g t k h).app
    ((ProperOpenShriek A cq.i).obj
      (((ProperOpenTensor A U).obj Q).obj ((ProperOpenPull A q).obj N0)))

/-- The coordinate composite kappa inverse R_b(Psi nu) z. The open compositor
i_!j_q!=u_! is inserted before applying kappa inverse.
Source: the displayed coordinate formula
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def route [QuasiCompact g] {U T : Scheme.{u}} {q : U ⟶ Z}
    (cq : Compactification q) (i : cq.Z ⟶ T) (t : T ⟶ cg.Z)
    [IsOpenImmersion i] [QuasiCompact i] [IsProper t]
    (h : i ≫ t = cq.g ≫ cg.i) (Q : ProperOpenDerived A U)
    (B0 : (ProperOpenPull A cg.i).obj ((ProperOpenPull A cg.g).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)) ⟶
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cq).obj Q) :
    ((ProperOpenTensor A B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N) ⟶
    (ProperOpenPush A (t ≫ cg.g)).obj ((ProperOpenShriek A (cq.i ≫ i)).obj
      (((ProperOpenTensor A U).obj Q).obj ((ProperOpenPull A q).obj N))) :=
  z cf cg A M N ≫
  (ProperOpenPush A cg.g).map (nu cf cg A M N ≫
    psi A cq i t cg.i h
      ((ProperOpenPull A cg.g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))
      Q N B0) ≫
  (ProperOpenPush A cg.g).map
    ((ProperOpenPush A t).map ((properOpenShriekComp A cq.i i).hom.app
      (((ProperOpenTensor A U).obj Q).obj ((ProperOpenPull A q).obj N)))) ≫
  (finiteDirectImageComposition A t cg.g).inv.app _

/-- The proper and open factors of PF_g, including P_k P_b=P_g.
Source: the g projection clause
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def gOpenFactor :=
  compactificationOpenFactor A cg N
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)

/-- The exact proper/open factorization of the specified compactification projection.
Both factors are fixed maps, not variables or assumed isomorphisms.
Source: the two projection-factor clauses
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def ProjectionFactorization {U V : Scheme.{u}} {a : U ⟶ V}
    (c : Compactification a) (Q : ProperOpenDerived A U) (L : ProperOpenDerived A V) :
    Prop :=
  finiteForwardProjectionMap (ModuleCat.{u + 1} A) c Q L =
    properOpenProjection A c.g ((ProperOpenShriek A c.i).obj Q) L ≫
      (ProperOpenPush A c.g).map (compactificationOpenFactor A c Q L)

/-- The coordinate equality and the two exact projection factorizations. The final
clause records precisely how the following signed swap changes the g open factor to nu.
Source: coordinate formula and projection-factor paragraphs
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def Expansion [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g]
    (hD : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) (pullback f g)
      (finiteProductExternal (finiteProductGeometry cf cg) (ModuleCat.{u + 1} A) M N)) :
    Prop :=
  letI : HasCompactification (pullback.snd f g ≫ g) := ⟨⟨productChoice cf cg⟩⟩
  HEq (finiteProductChosenForward (finiteProductGeometry cf cg) A cf cg
      (productChoice cf cg) M N hD)
    (route cf cg A M N (cf.ofIsPullback (IsPullback.of_hasPullback f g))
      (middleOpen cf cg) (pullback.snd cf.g cg.g) (middleComm cf cg)
      ((ProperOpenPull A (pullback.fst f g)).obj M) (exchange cf cg A M)) ∧
  ProjectionFactorization A (cf.ofIsPullback (IsPullback.of_hasPullback f g))
    ((ProperOpenPull A (pullback.fst f g)).obj M) N ∧
  ProjectionFactorization A cg N
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M) ∧
  (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) cg.Z
      ((ProperOpenPull A cg.g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))
      ((ProperOpenShriek A cg.i).obj N) ≫
    gOpenFactor cf cg A M N ≫
    (ProperOpenShriek A cg.i).map
      (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) Z N
        ((ProperOpenPull A g).obj
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))) =
    nu cf cg A M N ≫
      (ProperOpenShriek A cg.i).map
        (((ProperOpenTensor A Z).map
          ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) cg).hom.app
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))
          ).app N))

/-- Equality of the actual forward composites for two systems of choices, using
the canonical common-refinement comparisons at all three endpoints. The q compactification
inside each forward composite is the base change of that system's f compactification.
Source: theta_h T1=T2(theta_f tensor theta_g)
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def TransportEquation [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g]
    (cf' : Compactification f) (cg' : Compactification g)
    (ch ch' : Compactification (pullback.snd f g ≫ g))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hN : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z N)
    (hD : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) (pullback f g)
      (finiteProductExternal (finiteProductGeometry cf cg) (ModuleCat.{u + 1} A) M N)) :
    Prop :=
  letI : HasCompactification (pullback.snd f g ≫ g) := ⟨⟨productChoice cf cg⟩⟩
  finiteProductChosenForward (finiteProductGeometry cf cg) A cf cg ch M N hD ≫
    (finiteForwardCompactificationComparison A ch ch').hom.app ⟨_, hD⟩ =
  ((ProperOpenTensor A B).map
    ((finiteForwardCompactificationComparison A cf cf').hom.app ⟨M, hM⟩)).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N) ≫
    ((ProperOpenTensor A B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf').obj M)).map
      ((finiteForwardCompactificationComparison A cg cg').hom.app ⟨N, hN⟩) ≫
    finiteProductChosenForward (finiteProductGeometry cf cg) A cf' cg' ch' M N hD

/-- The expansion and comparison equations on the complete witnessed tensor domain.
Source: all choices and tensor-domain clauses
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def Assertion [HasCompactification f] [HasCompactification g]
    [QuasiCompact f] [QuasiCompact g]
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hN : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z N) : Prop :=
  ∀ (cf : Compactification f) (cg : Compactification g)
    (d : FiniteProductCompactificationDomain (finiteProductGeometry cf cg) A cf cg M N),
    Expansion cf cg A M N d.2.2.2.2.2 ∧
    ∀ (cf' : Compactification f) (cg' : Compactification g)
      (ch ch' : Compactification (pullback.snd f g ≫ g))
      (_d' : FiniteProductCompactificationDomain (finiteProductGeometry cf cg) A cf' cg' M N),
      TransportEquation cf cg A M N cf' cg' ch ch' hM hN d.2.2.2.2.2

end AlgebraicGeometry.ProEtale.ForwardProductCoordinates

namespace AlgebraicGeometry.ProEtale

/-- The finite-field forward-coordinate assertion, with the source's finite-type
and separated hypotheses and the retained antecedents of M and N. The six tensor-domain
conditions are exactly the actual inputs and outputs of the forward composite. Both
systems have these conditions; the endpoint and intermediate comparisons are the normalized
ones, so their common-refinement independence also covers every further refinement.
Source: opening choice-coherence and symmetry paragraphs of lem-sf-kunneth-coherence
(blueprint: lem-pur-product-forward-coordinate-transport). -/
def FiniteForwardCoordinateTransport
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (.of C.field.k))] [X.Over (Spec (.of C.field.k))]
    [Z.Over (Spec (.of C.field.k))]
    [IsSeparated (B ↘ Spec (.of C.field.k))]
    [IsSeparated (X ↘ Spec (.of C.field.k))]
    [IsSeparated (Z ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of C.field.k))]
    [QuasiCompact (B ↘ Spec (.of C.field.k))]
    [QuasiCompact (X ↘ Spec (.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (.of C.field.k))] [g.IsOver (Spec (.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N) : Prop :=
  letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (.of C.field.k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (.of C.field.k))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (.of C.field.k))
  ForwardProductCoordinates.Assertion (f := f) (g := g) C.Coefficient M.obj N.obj
    ⟨wM.complex.obj, wM.complex.property, ⟨wM.iso⟩⟩
    ⟨wN.complex.obj, wN.complex.property, ⟨wN.iso⟩⟩

/-- The forward compact-support product has the specified proper/open coordinates
and commutes with every normalized change of compactification.
Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, opening and symmetry paragraphs
(blueprint: lem-pur-product-forward-coordinate-transport).

Proof, following the ten steps of the DAG node:
1. Use lem-pur-product-exchange-counit-coordinates for the product compactifications
   and alpha=kappa inverse R_b(Gamma), at the witnessed bounded-below object D.
2. Expand PF_g by def-exchange-projection as pi_b followed by R_b(delta_k).
   lem-sf-open-tensor-normalization identifies its canonical open factor with delta_k.
3. Insert the definition of nu and z. Cancel only the inverse pair of signed
   symmetries on L0 and J; functoriality gives the first three arrows as R_b(nu) z.
4. Expand PF_q as pi_v followed by R_v(d), using the same open normalization.
   The intervening exchange is exactly B0 for the base-changed f compactification.
   No exchange for q is inserted into its projection transformation.
5. Substitute alpha and these two expansions; functoriality and associativity give
   kappa inverse R_b(Psi nu) z and the two asserted projection factorizations.
6. Apply lem-pur-pf-refinement-compatibility separately to PF_q and PF_g, with
   the stipulated tensor witnesses. Use naturality in the second projection input.
7. thm-cbc-finite-level-proetale supplies the exchange square. Identify its proper
   mate by lem-weil-pbc-transport-identifies-exchange and its open factor by
   lem-cbc-proetale-extension-zero-comparison and the open normalization. Apply
   lem-sf-class-compact-support-comparison and lem-pur-compact-support-site-coherence
   to identify the transported comparisons with the normalized pro-etale endpoint
   comparisons of prop-compactification-coherence-detailed, also for base-changed q.
8. Use naturality and choice independence of thm-sf-comp-composition for alpha,
   with exactly the same endpoint comparisons and the witnessed object D.
9. Multiply the projection, exchange and composition squares, moving the comparison
   across the two symmetries by naturality. This gives theta_h T1=T2(theta_f tensor theta_g).
10. Common refinements and the cocycle of prop-compactification-coherence-detailed
   make every further refinement give the same equality. No projection or exchange
   is inverted, and no comparison to an ordinary external-product map is used. -/
theorem finiteForward_coordinate_transport
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (.of C.field.k))] [X.Over (Spec (.of C.field.k))]
    [Z.Over (Spec (.of C.field.k))]
    [IsSeparated (B ↘ Spec (.of C.field.k))]
    [IsSeparated (X ↘ Spec (.of C.field.k))]
    [IsSeparated (Z ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of C.field.k))]
    [QuasiCompact (B ↘ Spec (.of C.field.k))]
    [QuasiCompact (X ↘ Spec (.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (.of C.field.k))] [g.IsOver (Spec (.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N) :
    FiniteForwardCoordinateTransport C f g M N wM wN := by
  sorry

end AlgebraicGeometry.ProEtale
