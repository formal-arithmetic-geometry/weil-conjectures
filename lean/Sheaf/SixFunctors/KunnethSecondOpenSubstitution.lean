module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.OpenExternalTensorNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.ExchangeFunctoriality
import Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction
import Sheaf.SixFunctors.CompositionProjectionMate
public import Sheaf.SixFunctors.ProperOpenProjectionMate

/-! # Second-open substitution in the specified Kunneth composite

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, compactification reduction;
Stacks 0F7B, 0F7J, 0F7K (blueprint: lem-sf-kunneth-second-open-substitution).

The three equations are expressed in fixed-scalar coordinates. The final equation
uses the iterated target S_b S_Q J_w; this is precisely the target identification
specified in the node. All arrows are composites of the recorded canonical maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.KunnethSecondOpen

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The two product cones and their induced open square. The three pullback proofs
say exactly U = Xbar times_B Y, W = Xbar times_B Ybar and U = W times_Ybar Y.
Source: the node's geometric diagram
(blueprint: lem-sf-kunneth-second-open-substitution). -/
structure Diagram {X Y Yb B : Scheme.{u}} (a : X ⟶ B) (b : Yb ⟶ B)
    (k : Y ⟶ Yb) (U W : Scheme.{u}) where
  r : U ⟶ X
  s : U ⟶ Y
  P : W ⟶ X
  Q : W ⟶ Yb
  w : U ⟶ W
  barSquare : IsPullback P Q a b
  square : IsPullback r s a (k ≫ b)
  openSquare : IsPullback w s Q k
  left : w ≫ P = r
  [open_w : IsOpenImmersion w]

attribute [instance] Diagram.open_w

/-- The two verticals are proper base changes of a. Source: node proof step 1
(blueprint: lem-sf-kunneth-second-open-substitution). -/
instance Diagram.properQ {X Y Yb B U W : Scheme.{u}} {a : X ⟶ B}
    {b : Yb ⟶ B} {k : Y ⟶ Yb} (d : Diagram a b k U W) [IsProper a] :
    IsProper d.Q :=
  MorphismProperty.of_isPullback (P := @IsProper) d.barSquare inferInstance

/-- Properness of s is the same base-change instance on the open product.
Source: node proof step 1 (blueprint: lem-sf-kunneth-second-open-substitution). -/
instance Diagram.properS {X Y Yb B U W : Scheme.{u}} {a : X ⟶ B}
    {b : Yb ⟶ B} {k : Y ⟶ Yb} (d : Diagram a b k U W) [IsProper a] :
    IsProper d.s :=
  MorphismProperty.of_isPullback (P := @IsProper) d.square inferInstance

/-- The product open is quasi-compact by base change of k. Source: node proof step 1
(blueprint: lem-sf-kunneth-second-open-substitution). -/
instance Diagram.quasiCompactW {X Y Yb B U W : Scheme.{u}} {a : X ⟶ B}
    {b : Yb ⟶ B} {k : Y ⟶ Yb} (d : Diagram a b k U W) [QuasiCompact k] :
    QuasiCompact d.w :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) d.openSquare.flip inferInstance

variable {X Y Yb B U W : Scheme.{u}} {a : X ⟶ B} {b : Yb ⟶ B}
  {k : Y ⟶ Yb} [IsOpenImmersion k]

/-- H = P_P M. Source: the node's definition of H
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def ambient (d : Diagram a b k U W) (M : FiniteD A X) : FiniteD A W :=
  (FiniteOpenProduct.pull A d.P).obj M

/-- N = P_w H tensor P_s L. Source: the node's definition of N
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def inside (d : Diagram a b k U W) (M : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensor A U
    ((FiniteOpenProduct.pull A d.w).obj (ambient A d M))
    ((FiniteOpenProduct.pull A d.s).obj L)

/-- The specified e2: tensor of identity with normalized beta, followed by signed rho.
Source: the node's displayed e2 formula; open-external-tensor-normalization with first
open the identity (blueprint: lem-sf-kunneth-second-open-substitution). -/
def external (d : Diagram a b k U W) (M : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensorMap A W (𝟙 (ambient A d M))
      ((FiniteOpenProduct.beta A d.s d.w k d.Q d.openSquare.flip).hom.app L) ≫
    FiniteOpenProduct.rho A d.w (ambient A d M) ((FiniteOpenProduct.pull A d.s).obj L)

/-- The specified direct-image exchange E_C, in exact inverse-image coordinates.
Source: def-exchange-projection and the node's E_C
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def openExchange (d : Diagram a b k U W) (C : FiniteD A W) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) k).inv.app _ ≫
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) d.openSquare.toCommSq).app C ≫
    (lowerStar (ModuleCat.{u + 1} A) d.s).rightDerivedFunctor.map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) d.w).hom.app C)

/-- The inner T = PF_s (E_H tensor 1), with both factors in the node's order.
Source: the proper/open projection square
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def inner (d : Diagram a b k U W) (M : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensorMap A Y (openExchange A d (ambient A d M)) (𝟙 L) ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) d.s).app
      ((FiniteOpenProduct.pull A d.w).obj (ambient A d M))).app L ≫
    (lowerStar (ModuleCat.{u + 1} A) d.s).rightDerivedFunctor.map
      (FiniteOpenProduct.tensorMap A U (𝟙 _)
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) d.s).hom.app L))

/-- The left side of the proper/open square, S_Q(e2) PF_Q.
Source: the node's second displayed equality
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def squareLeft (d : Diagram a b k U W) (M : FiniteD A X) (L : FiniteD A Y) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) d.Q).app
      (ambient A d M)).app ((finiteShriek A k).obj L) ≫
    (lowerStar (ModuleCat.{u + 1} A) d.Q).rightDerivedFunctor.map
      (FiniteOpenProduct.tensorMap A W (𝟙 _)
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) d.Q).hom.app
            ((finiteShriek A k).obj L)) ≫ external A d M L)

/-- The canonical identification of proper compactification coordinates with Rf_*.
It is just the identity-open comparison, mapped through Rf_*.
Source: the proper convention in the node and thm-sf-comp-composition
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def properCoordinates {V Z : Scheme.{u}} (f : V ⟶ Z) [IsProper f] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper f) ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) V) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- The open compactification coordinates reduce to J by the proper identity comparison.
Source: the open convention in the node and thm-sf-comp-composition
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def openCoordinates {V Z : Scheme.{u}} (j : V ⟶ Z) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsOpenImmersion j) ≅ finiteShriek A j :=
  Functor.isoWhiskerLeft _ (rightDerivedLowerStarId (ModuleCat.{u + 1} A) Z) ≪≫
    Functor.rightUnitor _

/-- The common compactification (w,Q) of k s. Source: the compositor equality
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def commonCompactification (d : Diagram a b k U W) [IsProper d.Q] :
    Compactification (d.s ≫ k) where
  Z := W
  i := d.w
  g := d.Q
  comm := d.openSquare.w.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Alpha_{k,s} with the outer source in J_k R_s coordinates. The etale presentation
only evaluates the fixed canonical compositor; it supplies no arbitrary arrow.
Source: thm-sf-comp-composition, node's first equality
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def alphaKS (d : Diagram a b k U W) [IsProper d.Q] [IsProper d.s]
    [QuasiCompact k] (C : FiniteD A U)
    (O : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (coherenceBoundedSiteFunctor A U).obj O ≅ C) :=
  (finiteShriek A k).map ((properCoordinates A d.s).inv.app C) ≫
    (openCoordinates A k).inv.app _ ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsOpenImmersion k)).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (Compactification.ofIsProper d.s)).map e.inv) ≫
    coherenceProEtaleCompositor A (Compactification.ofIsProper d.s)
      (Compactification.ofIsOpenImmersion k) (commonCompactification d) O ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (commonCompactification d)).map e.hom

/-- Alpha_{Q,w}, with the same target coordinates (w,Q). Source: the first equality
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def alphaQW (d : Diagram a b k U W) [IsProper d.Q] [QuasiCompact d.w]
    (C : FiniteD A U)
    (O : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (coherenceBoundedSiteFunctor A U).obj O ≅ C) :=
  (lowerStar (ModuleCat.{u + 1} A) d.Q).rightDerivedFunctor.map
      ((openCoordinates A d.w).inv.app C) ≫
    (properCoordinates A d.Q).inv.app _ ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper d.Q)).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (Compactification.ofIsOpenImmersion d.w)).map e.inv) ≫
    coherenceProEtaleCompositor A (Compactification.ofIsOpenImmersion d.w)
      (Compactification.ofIsProper d.Q)
      { Z := W, i := d.w, g := d.Q, comm := rfl,
        isProper := inferInstance, isOpenImmersion := inferInstance } O ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (commonCompactification d)).map e.hom


/-- The canonical proper/open mate, specialized to the Cartesian square. Its exact
open-adjunction characterization is included in Assertion below, so this introduces
neither an arbitrary isomorphism nor an unspecified choice of adjunction.
Source: lem-sf-proper-open-tensor-compatibility, first paragraph of the node
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def gamma (d : Diagram a b k U W) [IsProper d.Q] [IsProper d.s]
    [QuasiCompact k] [QuasiCompact d.w] (C : FiniteD A U) :=
  (properOpenMate A d.w d.s d.Q k d.openSquare.w).app C

/-- Signed proper projection Theta_h = S_h(sigma) PF_h sigma.
Source: the node's Theta convention, with h proper
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def properTheta {V Z : Scheme.{u}} (h : V ⟶ Z) (F : FiniteD A Z) (L : FiniteD A V) :=
  FiniteOpenProduct.sigma A Z F
      ((lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj L) ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) h).app L).app F ≫
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.map
      (FiniteOpenProduct.tensorMap A V (𝟙 L)
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app F) ≫
        FiniteOpenProduct.sigma A V L ((FiniteOpenProduct.pull A h).obj F))

/-- Exchange for the proper first map a, at either base-change morphism.
Source: Ex_{a,z} in the defining lambda formula
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def properExchange {T V Z R : Scheme.{u}} {p : T ⟶ V} {q : T ⟶ Z}
    {h : V ⟶ R} {z : Z ⟶ R} (sq : IsPullback p q h z) (M : FiniteD A V) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) z).inv.app _ ≫
    (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M ≫
    (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).hom.app M)

/-- The specified lambda_{a,bk}, before its final outer compositor, transported to
S_b J_k S_s N using Gamma_N. Its initial signed projection is the actual projection
of the compactification (k,b), followed by the canonical pullback composition.
Source: final displayed equality and its stated target identification
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def substituted (d : Diagram a b k U W) [IsProper b] [IsProper d.Q] [IsProper d.s]
    [QuasiCompact k] [QuasiCompact d.w] (M : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.sigma A B
      ((lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctor.obj M)
      ((lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctor.obj
        ((finiteShriek A k).obj L)) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A)
      { Z := Yb, i := k, g := b, comm := rfl,
        isProper := inferInstance, isOpenImmersion := inferInstance }).app L).app
          ((lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctor.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctor.map
      ((finiteShriek A k).map
        (FiniteOpenProduct.tensorMap A Y (𝟙 L)
            ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) (k ≫ b)).hom.app _ ) ≫
          FiniteOpenProduct.sigma A Y L _ ≫
          FiniteOpenProduct.tensorMap A Y (properExchange A d.square M) (𝟙 L) ≫
          ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) d.s).app
            ((FiniteOpenProduct.pull A d.r).obj M)).app L ≫
          (lowerStar (ModuleCat.{u + 1} A) d.s).rightDerivedFunctor.map
            (FiniteOpenProduct.tensorMap A U
              ((FiniteOpenProduct.composeEq A d.w d.P d.r d.left).inv.app M)
              ((leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) d.s).hom.app L))) ≫
        gamma A d (inside A d M L))

/-- The specified lambda_{a,b}(M,J_k L), followed by S_b S_Q(e2), in the same
iterated target. The common outer compositor alpha_{b,Q} is suppressed on both
sides; naturality moves it past e2, exactly as stipulated in the node.
Source: final equality (blueprint: lem-sf-kunneth-second-open-substitution). -/
def extended (d : Diagram a b k U W) (M : FiniteD A X) (L : FiniteD A Y) :=
  properTheta A b ((lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctor.obj M)
      ((finiteShriek A k).obj L) ≫
    (lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctor.map
      (FiniteOpenProduct.tensorMap A Yb (properExchange A d.barSquare M)
          (𝟙 ((finiteShriek A k).obj L)) ≫ squareLeft A d M L)

/-- All three claimed equations, together with the defining adjunct normalization
of Gamma. Origin presentations evaluate only the canonical alpha, and are universally
quantified. No existence of a free comparison or projection arrow is assumed.
Source: the three conclusions of the node
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def Assertion (d : Diagram a b k U W) [IsProper b] [IsProper d.Q] [IsProper d.s]
    [QuasiCompact k] [QuasiCompact d.w] (M : FiniteD A X) (L : FiniteD A Y) : Prop :=
  (∀ C : FiniteD A U,
    (FiniteOpenProduct.adj A k).unit.app
        ((lowerStar (ModuleCat.{u + 1} A) d.s).rightDerivedFunctor.obj C) ≫
      (FiniteOpenProduct.pull A k).map (gamma A d C) ≫
      openExchange A d ((finiteShriek A d.w).obj C) =
    (lowerStar (ModuleCat.{u + 1} A) d.s).rightDerivedFunctor.map
      ((FiniteOpenProduct.adj A d.w).unit.app C)) ∧
  (∀ (C : FiniteD A U)
    (O : _root_.DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (e : (coherenceBoundedSiteFunctor A U).obj O ≅ C),
    gamma A d C ≫ alphaQW A d C O e = alphaKS A d C O e) ∧
  (squareLeft A d M L =
    FiniteOpenProduct.rho A k
        ((lowerStar (ModuleCat.{u + 1} A) d.Q).rightDerivedFunctor.obj (ambient A d M)) L ≫
      (finiteShriek A k).map (inner A d M L) ≫ gamma A d (inside A d M L)) ∧
  substituted A d M L = extended A d M L

/-- State the assertion on exactly the finite-Tor constructible inputs of the node,
using the inverse of the recorded canonical coefficient-realization equivalence.
Source: the finite-field six-functor setting of the node
(blueprint: lem-sf-kunneth-second-open-substitution). -/
def FiniteAssertion
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorDatum D C E n hn)
    {B₀ X₀ Y₀ Yb₀ : SixFunctorSpace D}
    (a₀ : X₀ ⟶ B₀) (b₀ : Yb₀ ⟶ B₀) (k₀ : Y₀ ⟶ Yb₀)
    [IsProper a₀.hom.left] [IsProper b₀.hom.left] [IsOpenImmersion k₀.hom.left]
    {U W : Scheme.{u}} (d : Diagram a₀.hom.left b₀.hom.left k₀.hom.left U W)
    (M : finiteTorConstructibleCategory C.l E n hn X₀.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y₀.obj.left) : Prop :=
  letI : LocallyOfFiniteType Y₀.obj.hom := Y₀.property.1
  letI : QuasiCompact Y₀.obj.hom := Y₀.property.2
  letI : IsNoetherian Y₀.obj.left := isNoetherian_of_locallyOfFiniteType Y₀.obj.hom
  letI : QuasiCompact k₀.hom.left := inferInstance
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  Assertion (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)) d
    ((sixFunctorFiniteRealization D C E n hn X₀).inverse.obj M.obj)
    ((sixFunctorFiniteRealization D C E n hn Y₀).inverse.obj L.obj)

/-- Second-open substitution, including the normalized proper/open projection square
and the compositor formula for its open adjunct.
Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph; Stacks 0F7B, 0F7J, 0F7K
(blueprint: lem-sf-kunneth-second-open-substitution).

Proof, following the five steps of the node:
1. Properness of Q,s is base change of a. The Cartesian-open-adjunction-restriction
lemma identifies E with open restriction, including its counit mate. The normalized
proper/open tensor comparison is therefore the J_k adjoint of inverse E after the
open unit. Apply composition-projection-mate to the compactification (k,identity)
and compatible triangle (identity,w,s,Q); its tower map is Gamma. For (Q,w), use
(identity,Q) and (w,identity,identity,identity); the tower map is identity. The two
compositors thus satisfy Gamma alpha_Qw = alpha_ks. Composition and compactification
independence in thm-sf-comp-composition give the formula for every origin presentation.
Constructible-origin ensures that the finite-Tor inputs lie in this domain.
2. Open-tensor-normalization says that beta and gamma restrict to the identity under
the open units. In the signed variant the two Koszul symmetries cancel. Thus e2 and
Theta_k both restrict to identity, and e2 is the one-open external tensor comparison
of open-external-tensor-normalization.
3. Transpose the two sides of squareLeft = Theta_k J_k(T) Gamma under J_k adjoint to
P_k, and postcompose with E_{J_w N}. Naturality of E at e2 and the base-change clause
of prop-sf-pf-coherence turn the left transpose into T. The right transpose is also T:
E P_k Gamma is identity after the unit, P_k J_k(T) = T, and P_k Theta_k is identity.
Injectivity of the adjunction Hom bijection proves the square. Properness identifies
the direct-image and shriek projection maps.
4. Horizontal exchange pasting in fix-lem-exchanges gives Ex_{a,bk} = E_H P_k Ex_{a,b}.
Expand Theta as signed symmetry, PF, signed symmetry. The projection-composition
pentagon of prop-sf-pf-coherence gives Theta_bk = S_b(Theta_k) Theta_b. Naturality
moves the symmetry through the compositor and the two adjacent signed swaps cancel.
Naturality of Theta_k also moves P_k Ex_{a,b} through it.
5. Expand lambda_{a,bk} by step 4, move Ex by that naturality, and use the square of
step 3. Its result is S_b S_Q(e2) lambda_{a,b}. Insert S_b Gamma_N to identify the two
iterated targets. Step 1 and the associative alpha pentagon identify this insertion
with exactly the target transport in the statement. Naturality moves the common
outer compositor past e2. This gives substituted = extended in these coordinates. -/
theorem kunneth_second_open_substitution
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn)
    {B₀ X₀ Y₀ Yb₀ : SixFunctorSpace D}
    [IsSeparated B₀.obj.hom] [IsSeparated X₀.obj.hom]
    [IsSeparated Y₀.obj.hom] [IsSeparated Yb₀.obj.hom]
    (a₀ : X₀ ⟶ B₀) (b₀ : Yb₀ ⟶ B₀) (k₀ : Y₀ ⟶ Yb₀)
    [IsProper a₀.hom.left] [IsProper b₀.hom.left] [IsOpenImmersion k₀.hom.left]
    {U W : Scheme.{u}} (d : Diagram a₀.hom.left b₀.hom.left k₀.hom.left U W)
    (M : finiteTorConstructibleCategory C.l E n hn X₀.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y₀.obj.left) :
    FiniteAssertion S a₀ b₀ k₀ d M L := by
  sorry

end AlgebraicGeometry.ProEtale.KunnethSecondOpen
