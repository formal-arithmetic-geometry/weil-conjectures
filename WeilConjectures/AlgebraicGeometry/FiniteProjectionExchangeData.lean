/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompactProjectionBaseChange
public import WeilConjectures.AlgebraicGeometry.FixProjectionCompactificationComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.Compactification.RefinementOfIsPullback

/-! # Finite projection/exchange transposes

Source: blueprint sec-six-functors/sk-prop-sf-pf-coherence,
prop-sf-pf-coherence.proof.md, open/proper factor calculation, compactification
independence and identity (blueprint: def-sf-finite-projection-exchange-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Fixed-scalar coordinates on the prescribed small pro-etale derived category.
Source: def-exchange-projection, finite stage
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev Dcat (X : Scheme.{u}) := DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat A))

/-- The existing exact derived inverse image, without any new choice.
Source: def-exchange-projection, finite stage
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat A) f).leftDerivedFunctor

/-- The existing total derived direct image.
Source: def-exchange-projection, finite stage
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat A) f).rightDerivedFunctor

/-- The existing derived tensor in fixed-scalar coordinates.
Source: def-exchange-projection, projection paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev tensor (X : Scheme.{u}) (K L : Dcat A X) := ((derivedTensor (ModuleCat A) X).obj K).obj L

/-- The canonical tensor map on a pair of arrows.
Source: def-exchange-projection, projection paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def tensorMap {X : Scheme.{u}} {K K' L L' : Dcat A X} (a : K ⟶ K') (b : L ⟶ L') :=
  ((derivedTensor (ModuleCat A) X).map a).app L ≫
    ((derivedTensor (ModuleCat A) X).obj K').map b

/-- The canonical pullback/tensor isomorphism, normalized on K-flat representatives.
Source: def-exchange-projection, mu
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev mu {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : Dcat A Y) :=
  leftDerivedUpperStarTensorIso (ModuleCat A) f K L

/-- The existing square comparison, with the orientation F'G to HF.
Source: def-exchange-projection, theta
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev theta {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) :=
  leftDerivedUpperStarSquareIso (ModuleCat A) s

/-- The proper projection is the published counit-defined mate.
Source: def-exchange-projection, a and pi
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev pi {B Y : Scheme.{u}} (p : B ⟶ Y) (M : Dcat A B) (L : Dcat A Y) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat A) p).app M).app L

/-- The proper exchange is the published square mate.
Source: def-exchange-projection, Ex_*
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev exchange {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) (M : Dcat A B) :=
  (derivedBaseChangeMap (ModuleCat A) s).app M

/-- The proper route that projects first and then exchanges, including d.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def properFirst {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) (M : Dcat A B) (L : Dcat A Y) :=
  (pull A g).map (pi A p M L) ≫ exchange A s (tensor A B M ((pull A p).obj L)) ≫
    (push A p').map ((mu A h M ((pull A p).obj L)).hom ≫
      tensorMap A (𝟙 ((pull A h).obj M)) ((theta A s).inv.app L))

/-- The proper route that exchanges first and then projects.
Source: prop-sf-pf-coherence.proof.md, proper-factor paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def exchangeFirst {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) (M : Dcat A B) (L : Dcat A Y) :=
  (mu A g ((push A p).obj M) L).hom ≫
    tensorMap A (exchange A s M) (𝟙 ((pull A g).obj L)) ≫
    pi A p' ((pull A h).obj M) ((pull A g).obj L)

/-- The specified common transpose: the canonical comparisons followed by H epsilon tensor 1.
Source: prop-sf-pf-coherence.proof.md, proper-factor displayed map
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def commonTranspose {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) (M : Dcat A B) (L : Dcat A Y) :=
  (pull A p').map (mu A g ((push A p).obj M) L).hom ≫
    (mu A p' ((pull A g).obj ((push A p).obj M)) ((pull A g).obj L)).hom ≫
    tensorMap A ((theta A s).hom.app ((push A p).obj M))
      (𝟙 ((pull A p').obj ((pull A g).obj L))) ≫
    tensorMap A ((pull A h).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat A) p).counit.app M))
      (𝟙 ((pull A p').obj ((pull A g).obj L)))

/-- Exact termwise open extension, the prescribed J.
Source: def-exchange-projection, chosen compactification
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev ext {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat A) j).mapDerivedCategory

/-- The canonical open tensor map, in the direction used in PF.
Source: def-exchange-projection, gamma
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev gamma {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (K : Dcat A X) (P : Dcat A B) :=
  derivedTensorOpenImmersionLowerShriekIso (ModuleCat A) j K P

/-- The canonical open base-change isomorphism in the direction HJ to J'A.
Source: def-exchange-projection, beta
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev beta {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) :=
  (leftDerivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat A) s).symm

/-- Open-factor route through H gamma and beta.
Source: prop-sf-pf-coherence.proof.md, open-factor paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def openFirst {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :=
  (pull A h).map (gamma A j K P).hom ≫
    (beta A s).hom.app (tensor A X K ((pull A j).obj P)) ≫
    (ext A j').map ((mu A a K ((pull A j).obj P)).hom ≫
      tensorMap A (𝟙 ((pull A a).obj K)) ((theta A s.toCommSq).inv.app P))

/-- Open-factor route through mu_H, beta tensor 1, and gamma'.
Source: prop-sf-pf-coherence.proof.md, open-factor paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def openSecond {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :=
  (mu A h ((ext A j).obj K) P).hom ≫
    tensorMap A ((beta A s).hom.app K) (𝟙 ((pull A h).obj P)) ≫
    (gamma A j' ((pull A a).obj K) ((pull A h).obj P)).hom

/-- Canonical unit identification J*J! to the identity, with J* expressed as L j*.
The inverse is a literal inverse morphism of the open unit, which is invertible.
Source: prop-sf-pf-coherence.proof.md, canonical open units
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def openUnitInv {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] (K : Dcat A X) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).hom.app ((ext A j).obj K) ≫
    @inv _ _ _ _
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit.app K)
      (by
        have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit :=
          (openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat A) j).unit_isIso_of_L_fully_faithful
        have hd : IsIso
            (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit :=
          Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
        infer_instance)

/-- Source identification for the restricted open routes, using square and tensor comparisons
and the open unit alone. Source: prop-sf-pf-coherence.proof.md, open-factor paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def openSource {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :=
  (theta A s.toCommSq).hom.app (tensor A B ((ext A j).obj K) P) ≫
    (pull A a).map (mu A j ((ext A j).obj K) P).hom ≫
    (mu A a ((pull A j).obj ((ext A j).obj K)) ((pull A j).obj P)).hom ≫
    tensorMap A ((pull A a).map (openUnitInv A j K))
      ((theta A s.toCommSq).inv.app P)

/-- The actual compactification projection, with no invertibility asserted.
Source: def-exchange-projection, PF^c
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev pf {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y) :=
  ((projectionMapOfCompactification (ModuleCat A) c).app K).app L

/-- The compactification exchange, with the base-changed compactification retained.
Source: def-exchange-projection, Ex_!^c
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev ex {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) :=
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat A) s c).app K

/-- The canonical target comparison in the compact projection/exchange diamond.
Source: prop-sf-pf-coherence.proof.md, displayed equation
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def target {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g)
    (K : Dcat A X) (L : Dcat A Y) :=
  (mu A a K ((pull A f).obj L)).hom ≫
    tensorMap A (𝟙 ((pull A a).obj K)) ((theta A s.toCommSq).inv.app L)

/-- The first side of the compactification-relative diamond.
Source: prop-sf-pf-coherence.proof.md, displayed equation
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def diamondLeft {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y) :=
  (pull A g).map (pf A c K L) ≫ ex A s c (tensor A X K ((pull A f).obj L)) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat A) (c.ofIsPullback s)).map
      (target A s K L)

/-- The second side, including the source tensor comparison.
Source: prop-sf-pf-coherence.proof.md, displayed equation
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def diamondRight {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y) :=
  (mu A g ((rightDerivedLowerShriekOfCompactification (ModuleCat A) c).obj K) L).hom ≫
    tensorMap A (ex A s c K) (𝟙 ((pull A g).obj L)) ≫
    pf A (c.ofIsPullback s) ((pull A a).obj K) ((pull A g).obj L)

/-- The unit identification R id_* (id_! K) to K.
Source: prop-sf-pf-coherence.proof.md, identity paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def identitySupport (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactification (ModuleCat A)
      (Compactification.ofIsProper (𝟙 X)) ≅ 𝟭 (Dcat A X) :=
  Functor.isoWhiskerLeft (ext A (𝟙 X)) (rightDerivedLowerStarId (ModuleCat A) X) ≪≫
    Functor.rightUnitor _ ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekIdIso (ModuleCat A) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Base change of a refinement: the actual map between the two fibre products. This is the
existing `Compactification.Refinement.ofIsPullback` (the map `r.hom ×_Y Y'`), not a copy.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
abbrev baseRefinement {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g)
    {c d : Compactification f} (r : c.Refinement d) :
    (c.ofIsPullback s).Refinement (d.ofIsPullback s) :=
  r.ofIsPullback s

/-- The recorded refinement comparison evaluated at any presentation of its witnessed input.
The endpoint isomorphism retains the given antecedent, rather than choosing one.
Source: def-fix-six-functor-datum, prop-compactification-coherence-detailed
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def rho [TopologicalSpace A] [DiscreteTopology A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (K : Dcat A X)
    (O : EtaleOriginDerivedCategory X A) (e : refinementFixedObject X A O ≅ K) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat A) c).mapIso e.symm ≪≫
    refinementComparisonAtWitness A r O ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat A) d).mapIso e

/-- Refinement intertwining of both actual words in the diamond. The source comparison
is G(rho_K tensor 1); the target is rho at AK tensor f'^*GL. Every comparison retains
its input's etale-origin witness, including the pulled-back tensor input.
Source: prop-sf-pf-coherence.proof.md, compactification-independence sentence
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def RefinementLaw [TopologicalSpace A] [DiscreteTopology A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g)
    (K : Dcat A X) (L : Dcat A Y) : Prop :=
  ∀ (c d : Compactification f) (r : c.Refinement d)
    (O : EtaleOriginDerivedCategory X A) (e : refinementFixedObject X A O ≅ K)
    (OT : EtaleOriginDerivedCategory X' A)
    (eT : refinementFixedObject X' A OT ≅
      tensor A X' ((pull A a).obj K) ((pull A f').obj ((pull A g).obj L))),
    diamondLeft A s c K L ≫ (rho A (baseRefinement s r) _ OT eT).hom =
      (pull A g).map (tensorMap A (rho A r K O e).hom (𝟙 L)) ≫
        diamondLeft A s d K L ∧
    diamondRight A s c K L ≫ (rho A (baseRefinement s r) _ OT eT).hom =
      (pull A g).map (tensorMap A (rho A r K O e).hom (𝟙 L)) ≫
        diamondRight A s d K L

/-- All conclusions for one square, one compactification and one pair of inputs.
The restrictions compare to the independently constructed open-unit identification;
thus they say that both routes are identities under those units. The proper transpose
is stated separately for each route, without making either route invertible.
Source: prop-sf-pf-coherence.proof.md, open/proper factor calculation
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def SquareLaw [TopologicalSpace A] [DiscreteTopology A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y) : Prop :=
  diamondLeft A s c K L = diamondRight A s c K L ∧
  (ext A (c.ofIsPullback s).i).essImage
    ((pull A (pullback.fst c.g g)).obj
      (tensor A c.Z ((ext A c.i).obj K) ((pull A c.g).obj L))) ∧
  (ext A (c.ofIsPullback s).i).essImage
    ((ext A (c.ofIsPullback s).i).obj
      (tensor A X' ((pull A a).obj K)
        ((pull A (c.ofIsPullback s).i).obj
          ((pull A (pullback.fst c.g g)).obj ((pull A c.g).obj L))))) ∧
  (pull A (c.ofIsPullback s).i).map
      (openFirst A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)) ≫
      openUnitInv A (c.ofIsPullback s).i _ =
    openSource A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L) ∧
  (pull A (c.ofIsPullback s).i).map
      (openSecond A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)) ≫
      openUnitInv A (c.ofIsPullback s).i _ =
    openSource A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L) ∧
  ((derivedUpperStarLowerStarAdjunction (ModuleCat A) (c.ofIsPullback s).g).homEquiv _ _).symm
      (properFirst A (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L) =
    commonTranspose A (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L ∧
  ((derivedUpperStarLowerStarAdjunction (ModuleCat A) (c.ofIsPullback s).g).homEquiv _ _).symm
      (exchangeFirst A (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L) =
    commonTranspose A (c.isPullback_g_ofIsPullback s).flip.toCommSq ((ext A c.i).obj K) L ∧
  RefinementLaw A s K L

/-- Unit-normalized identity projection in fixed-scalar coordinates.
Source: prop-sf-pf-coherence.proof.md, identity paragraph
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def IdentityLaw (X : Scheme.{u}) (K L : Dcat A X) : Prop :=
  tensorMap A ((identitySupport A X).inv.app K) (𝟙 L) ≫
    pf A (Compactification.ofIsProper (𝟙 X)) K L ≫
    (identitySupport A X).hom.app (tensor A X K ((pull A (𝟙 X)).obj L)) ≫
    ((derivedTensor (ModuleCat A) X).obj K).map
      ((leftDerivedUpperStarId (ModuleCat A) X).hom.app L) = 𝟙 (tensor A X K L)

/-- The bounded constructible predicate transported by the published intrinsic realization.
Source: def-fix-six-functor-datum, finite domain
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def finiteBC (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u})
    (K : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  intrinsicFiniteTorsionConstructible l E n hn X
    ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)).functor.obj K)

/-- Only the second input has the recorded finite Tor amplitude condition.
Source: def-fix-six-functor-datum, finite domain
(blueprint: def-sf-finite-projection-exchange-coordinates). -/
def finiteCTF (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u})
    (L : Dcat (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  finiteTorConstructible l E n hn X
    ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)).functor.obj L)

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
