/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison
public import Sheaf.Paper.ProEtaleCompositionTowerDefinitions

/-! # Explicit product exchange coordinates

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry paragraph, reduction to proper maps
(blueprint: def-pur-product-exchange-coordinate-data).

The coordinate names below denote the canonical products, maps and composites in the
statement. In particular rho is derived from sectionwise restriction, independently of
exchange; Gamma is the existing proper/open mate, and alpha is the existing origin
composition transported to the supplied compactifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the specified positive-level coefficient quotient.
Source: def-pur-conventions, A=O_E/(varpi^n), n positive
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
instance productCoordinateRingFinite (C : PurityFiniteSetting.{u}) : Finite C.Ring :=
  Padic.finite_coefficientExtensionRing C.coefficients.l C.extension C.level C.level_pos

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

variable {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
variable (cf : Compactification f) (cg : Compactification g)

/-- W to C, the unique map preserving both projections.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def i : pullback cf.g g ⟶ pullback cf.g cg.g :=
  pullback.lift (pullback.fst cf.g g) (pullback.snd cf.g g ≫ cg.i)
    (by rw [Category.assoc, ← cg.comm]; exact pullback.condition)

/-- The defining Cartesian square of the displayed open i.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
abbrev square : IsPullback (pullback.snd cf.g g) (i cf cg)
    cg.i (pullback.snd cf.g cg.g) :=
  IsPullback.of_bot
    (by simpa only [i, pullback.lift_fst, ← cg.comm] using
      (IsPullback.of_hasPullback cf.g g).flip)
    (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback cf.g cg.g).flip

/-- Openness of the specified base change of k.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
instance i_isOpenImmersion : IsOpenImmersion (i cf cg) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (square cf cg) inferInstance

/-- Quasi-compactness of the given open k follows from finite type of g.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
instance k_quasiCompact [QuasiCompact g] : QuasiCompact cg.i :=
  cg.quasiCompact_openImmersion inferInstance

/-- Quasi-compactness of the specified base change of k.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
instance i_quasiCompact [QuasiCompact g] : QuasiCompact (i cf cg) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (square cf cg) inferInstance

/-- The commutativity equation ti=kv in Lean's composition order.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
abbrev comm : i cf cg ≫ pullback.snd cf.g cg.g = pullback.snd cf.g g ≫ cg.i :=
  pullback.lift_snd _ _ _

/-- The displayed compactification (u,c) of h=gq. Its base-changed first open is j_q.
Source: product diagram (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def compositeChoice : Compactification (pullback.snd f g ≫ g) where
  Z := pullback cf.g cg.g
  i := (cf.baseChange g).i ≫ i cf cg
  g := pullback.snd cf.g cg.g ≫ cg.g
  comm := by
    rw [Category.assoc, ← Category.assoc _ (pullback.snd cf.g cg.g) cg.g,
      comm, Category.assoc, ← cg.comm, ← Category.assoc,
      Compactification.baseChange_i_snd]
  isProper := inferInstance
  isOpenImmersion := inferInstance

variable (A : Type u) [CommRing A] [Finite A]

/-- Sectionwise open restriction, derived by K-injective composition. The coefficient
ring is the standard size lift of A. This is the fixed-scalar coordinate expression of
proEtaleOpenRestrictionComparison, not a definition by the exchange arrow.
Source: Stacks 09BN, normalized restriction
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def rho {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (j : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion k] (sq : IsPullback r k j p) :
    ProperOpenPush (ULift.{u + 1} A) p ⋙ ProperOpenPull (ULift.{u + 1} A) j ≅
      ProperOpenPull (ULift.{u + 1} A) k ⋙ ProperOpenPush (ULift.{u + 1} A) r :=
  let Q := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let S := Functor.isoWhiskerLeft (lowerStar Q p)
      (upperStarIsoOpenImmersionRestriction Q j) ≪≫
    Scheme.sfProperOpenFixedRestrictionIso A r k j p sq ≪≫
    Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction Q k).symm (lowerStar Q r)
  letI := (upperStarLowerStarAdjunction Q p).preservesKInjectiveComplexes
  letI := (openImmersionLowerShriekUpperStarAdjunction Q k).preservesKInjectiveComplexes
  Functor.isoWhiskerLeft (lowerStar Q p).rightDerivedFunctor
      ((Functor.leftDerivedFunctorIsoMapDerivedCategory (upperStar Q j)) ≪≫
        (upperStar Q j).rightDerivedFunctorIsoMapDerivedCategory.symm) ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso S ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      ((upperStar Q k).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        (Functor.leftDerivedFunctorIsoMapDerivedCategory (upperStar Q k)).symm) _

variable (M : ProperOpenDerived (ULift.{u + 1} A) X)

/-- H=j_!M.
Source: coordinates (blueprint: lem-pur-product-exchange-counit-coordinates). -/
abbrev H := (ProperOpenShriek (ULift.{u + 1} A) cf.i).obj M

/-- F=P_r H.
Source: coordinates (blueprint: lem-pur-product-exchange-counit-coordinates). -/
abbrev F := (ProperOpenPull (ULift.{u + 1} A) (pullback.fst cf.g cg.g)).obj (H cf A M)

/-- L0=P_b R_a H.
Source: coordinates (blueprint: lem-pur-product-exchange-counit-coordinates). -/
abbrev L0 := (ProperOpenPull (ULift.{u + 1} A) cg.g).obj
  ((ProperOpenPush (ULift.{u + 1} A) cf.g).obj (H cf A M))

/-- A0 is the actual unit--square--counit exchange on H.
Source: def-exchange-projection (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def A0 := (derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A))
  (IsPullback.of_hasPullback cf.g cg.g).toCommSq).app (H cf A M)

/-- B0 is the actual compactification-relative exchange, with P_k P_b=P_g inserted.
Source: def-exchange-projection (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def B0 :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A))
    cg.i cg.g).symm ≪≫
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A)) cg.comm.symm).hom.app _ ≫
  (rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (IsPullback.of_hasPullback f g) cf).app M

/-- beta, including P_i P_r=P_(ri), is the unit-normalized open base-change map.
Source: lem-sf-open-tensor-normalization
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def beta :
    (ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj (F cf cg A M) ≅
      (ProperOpenShriek (ULift.{u + 1} A) (cf.baseChange g).i).obj
        ((ProperOpenPull (ULift.{u + 1} A) (pullback.fst f g)).obj M) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (i cf cg) (pullback.fst cf.g cg.g)).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (pullback.lift_fst _ _ _)).app (H cf A M) ≪≫
    (properOpenBeta (ULift.{u + 1} A) (pullback.fst f g) (cf.baseChange g).i cf.i
      (pullback.fst cf.g g) (cf.isPullback_i_ofIsPullback
        (IsPullback.of_hasPullback f g))).app M

/-- chi is i_!(beta inverse) followed by the open counit.
Source: counit square (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def chi :=
  (ProperOpenShriek (ULift.{u + 1} A) (i cf cg)).map (beta cf cg A M).inv ≫
    (properOpenAdj (ULift.{u + 1} A) (i cf cg)).counit.app (F cf cg A M)

/-- s is k_!(B0), followed by the existing normalized proper/open mate.
Source: counit square (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def s [QuasiCompact g] :=
  (ProperOpenShriek (ULift.{u + 1} A) cg.i).map (B0 cf cg A M) ≫
    (properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
      (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app _

/-- Lambda uses sectionwise rho followed by the inverse open unit. This definition
is independent of Gamma, so the adjunct assertion below has mathematical content.
Source: explicit counit formulas (blueprint: lem-pur-product-exchange-counit-coordinates). -/
def lambda (Q : ProperOpenDerived (ULift.{u + 1} A) (pullback cf.g g)) :
    (ProperOpenPull (ULift.{u + 1} A) cg.i).obj
      ((ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).obj
        ((ProperOpenShriek (ULift.{u + 1} A) (i cf cg)).obj Q)) ≅
      (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g)).obj Q :=
  (rho A (pullback.snd cf.g g) (i cf cg) cg.i (pullback.snd cf.g cg.g)
    (square cf cg)).app _ ≪≫
  (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g)).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) (i cf cg)).app _ ≪≫
      (towerOpenUnit (ULift.{u + 1} A) (i cf cg)).symm.app Q)

/-- The explicit pair of open-counit identities, with eta_k inserted in the first.
Source: displayed explicit counit equations
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def CounitIdentities [QuasiCompact g] (Q : ProperOpenDerived (ULift.{u + 1} A)
    (pullback cf.g cg.g)) : Prop :=
  (properOpenAdj (ULift.{u + 1} A) cg.i).unit.app
      ((ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g)).obj
        ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q)) ≫
    (ProperOpenPull (ULift.{u + 1} A) cg.i).map
      ((properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
        (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app
          ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q) ≫
        (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).map
          ((properOpenAdj (ULift.{u + 1} A) (i cf cg)).counit.app Q)) ≫
    (rho A (pullback.snd cf.g g) (i cf cg) cg.i
      (pullback.snd cf.g cg.g) (square cf cg)).hom.app Q = 𝟙 _ ∧
  (ProperOpenShriek (ULift.{u + 1} A) cg.i).map
      ((rho A (pullback.snd cf.g g) (i cf cg) cg.i
        (pullback.snd cf.g cg.g) (square cf cg)).hom.app Q) ≫
    (properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
      (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app
        ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj Q) ≫
    (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).map
      ((properOpenAdj (ULift.{u + 1} A) (i cf cg)).counit.app Q) =
    (properOpenAdj (ULift.{u + 1} A) cg.i).counit.app
      ((ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).obj Q)

/-- The three displayed exchange and counit-square equations and the explicit adjunct
normalization. Only rho and beta are isomorphisms here.
Source: product exchange formulas
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def Equations [QuasiCompact g] : Prop :=
  (rho A (pullback.snd cf.g g) (i cf cg) cg.i
    (pullback.snd cf.g cg.g) (square cf cg)).hom.app (F cf cg A M) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (square cf cg).flip.toCommSq).app (F cf cg A M) ∧
  B0 cf cg A M =
    (ProperOpenPull (ULift.{u + 1} A) cg.i).map (A0 cf cg A M) ≫
      (rho A (pullback.snd cf.g g) (i cf cg) cg.i
        (pullback.snd cf.g cg.g) (square cf cg)).hom.app (F cf cg A M) ≫
      (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g)).map (beta cf cg A M).hom ∧
  s cf cg A M ≫
      (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g)).map (chi cf cg A M) =
    (properOpenAdj (ULift.{u + 1} A) cg.i).counit.app (L0 cf cg A M) ≫ A0 cf cg A M ∧
  (properOpenAdj (ULift.{u + 1} A) cg.i).homEquiv _ _
    ((properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
      (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app
        ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj (F cf cg A M))) =
    (lambda cf cg A ((ProperOpenPull (ULift.{u + 1} A) (i cf cg)).obj
      (F cf cg A M))).inv ∧
  CounitIdentities cf cg A (F cf cg A M)

end AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

namespace AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

variable {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
variable (cf : Compactification f) (cg : Compactification g)
variable (A : Type u) [CommRing A] [Finite A]

/-- The existing canonical origin compositor in the three displayed product choices.
The instances assert only existence of the compactifications explicitly provided here;
the actual arrow is conjugated by the canonical candidate comparisons.
Source: thm-sf-comp-composition, chosen coordinates
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def alpha [QuasiCompact f] [QuasiCompact g]
    (Q : ProperOpenDerived (ULift.{u + 1} A) (pullback f g))
    (hQ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (pullback f g) Q) :
    (ProperOpenPush (ULift.{u + 1} A) cg.g).obj
      ((ProperOpenShriek (ULift.{u + 1} A) cg.i).obj
        ((ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g)).obj
          ((ProperOpenShriek (ULift.{u + 1} A) (cf.baseChange g).i).obj Q))) ⟶
    (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g ≫ cg.g)).obj
      ((ProperOpenShriek (ULift.{u + 1} A) ((cf.baseChange g).i ≫ i cf cg)).obj Q) :=
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := (compositeChoice cf cg).hasCompactification
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A)) cg).map
      ((towerCandidateComparison (ULift.{u + 1} A) (cf.baseChange g)
        (HasCompactification.compactification (pullback.snd f g))).hom.app ⟨Q, hQ⟩) ≫
    (towerCandidateComparison (ULift.{u + 1} A) cg
      (HasCompactification.compactification g)).hom.app
        ((originCompactSupport (ULift.{u + 1} A) (pullback.snd f g)).obj ⟨Q, hQ⟩) ≫
    (originCompositionAmbient (ULift.{u + 1} A) (pullback.snd f g) g).hom.app ⟨Q, hQ⟩ ≫
    (towerCandidateComparison (ULift.{u + 1} A)
      (HasCompactification.compactification (pullback.snd f g ≫ g))
      (compositeChoice cf cg)).hom.app ⟨Q, hQ⟩

/-- The prescribed kappa inverse, image of Gamma, and open-extension compositor.
There is no inverse to Gamma in this expression.
Source: final composition-coordinate formula
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def compositionRoute [QuasiCompact g]
    (Q : ProperOpenDerived (ULift.{u + 1} A) (pullback f g)) :=
  (ProperOpenPush (ULift.{u + 1} A) cg.g).map
    ((properOpenMate (ULift.{u + 1} A) (i cf cg) (pullback.snd cf.g g)
      (pullback.snd cf.g cg.g) cg.i (comm cf cg)).app
        ((ProperOpenShriek (ULift.{u + 1} A) (cf.baseChange g).i).obj Q)) ≫
  (finiteDirectImageComposition (ULift.{u + 1} A)
    (pullback.snd cf.g cg.g) cg.g).inv.app _ ≫
  (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g cg.g ≫ cg.g)).map
    ((properOpenShriekComp (ULift.{u + 1} A) (cf.baseChange g).i (i cf cg)).hom.app Q)

/-- All geometric conclusions, with the structure maps of the new products explicit.
Compactification factorization is carried by cf.baseChange g and compositeChoice.
Source: geometric paragraph
(blueprint: lem-pur-product-exchange-counit-coordinates). -/
def Geometry (k : Type u) [Field k] (b : B ⟶ Spec (.of k))
    (x : X ⟶ Spec (.of k)) (z : Z ⟶ Spec (.of k)) : Prop :=
  IsProper (pullback.snd cf.g g) ∧ IsProper (pullback.snd cf.g cg.g) ∧
  IsOpenImmersion (i cf cg) ∧ QuasiCompact (i cf cg) ∧
  IsOpenImmersion (cf.baseChange g).i ∧ QuasiCompact (cf.baseChange g).i ∧
  IsOpenImmersion cg.i ∧ QuasiCompact cg.i ∧
  IsOpenImmersion ((cf.baseChange g).i ≫ i cf cg) ∧
    QuasiCompact ((cf.baseChange g).i ≫ i cf cg) ∧
  IsNoetherian B ∧ IsNoetherian X ∧ IsNoetherian Z ∧
  IsNoetherian cf.Z ∧ IsNoetherian cg.Z ∧
  IsNoetherian (pullback f g) ∧ IsNoetherian (pullback cf.g g) ∧
  IsNoetherian (pullback cf.g cg.g) ∧
  (LocallyOfFiniteType b ∧ QuasiCompact b) ∧
  (LocallyOfFiniteType x ∧ QuasiCompact x) ∧
  (LocallyOfFiniteType z ∧ QuasiCompact z) ∧
  (LocallyOfFiniteType (cf.g ≫ b) ∧ QuasiCompact (cf.g ≫ b)) ∧
  (LocallyOfFiniteType (cg.g ≫ b) ∧ QuasiCompact (cg.g ≫ b)) ∧
  (LocallyOfFiniteType (pullback.fst f g ≫ x) ∧ QuasiCompact (pullback.fst f g ≫ x)) ∧
  (LocallyOfFiniteType (pullback.snd cf.g g ≫ z) ∧ QuasiCompact (pullback.snd cf.g g ≫ z)) ∧
  (LocallyOfFiniteType (pullback.snd cf.g cg.g ≫ cg.g ≫ b) ∧
    QuasiCompact (pullback.snd cf.g cg.g ≫ cg.g ≫ b))

end AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

