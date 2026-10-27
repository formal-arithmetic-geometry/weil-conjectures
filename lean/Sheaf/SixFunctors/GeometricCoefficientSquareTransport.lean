/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.Paper.RingedCoefficientProjectionData
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.DerivedAdjunctionShift
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # The geometric coefficient square and its transport

Source: current blueprint, sec-six-functors-basics, direct-images proof paragraph (3),
scalar-unit refinement; Stacks Tags 07A6, 0D6D, 0D6E, 0FPI, 0B56 and 0DV0
(blueprint: lem-sfb-geometric-coefficient-square-transport).

The existing normalized geometric and scalar presentations supply the actual unbounded
module derived categories. All arrows below are constructed from their adjunctions and
normalized comparisons; no projection is assumed invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r t h uA uB uH vA vB vH uA' uB' vA' vB'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open WeilConjectures.SemilinearSections (Mod D)
namespace SheafOfModules.RingedCoefficientProjection.GeometricSquare

/-- Insert the second scalar unit, then use the normalized scalar associator.
On K-flat representatives this is r tensor x mapped to c(r) tensor x.
Source: Stacks 07A6 and 0D6D
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def unitArrow {A : Type uA} {B : Type uB} {H : Type uH}
    [Category.{vA} A] [Category.{vB} B] [Category.{vH} H]
    (L : A ⥤ B) {M : B ⥤ H} {U : H ⥤ B} (adj : M ⊣ U)
    {N : A ⥤ H} (δ : L ⋙ M ≅ N) : L ⟶ N ⋙ U :=
  (rightUnitor L).inv ≫ whiskerLeft L adj.unit ≫
    (Functor.associator L M U).inv ≫ whiskerRight δ.hom U

/-- The explicit transport law for the adjoints used to specify the arrows.
The comparison data require both unit and counit compatibility; compatibility of
an arbitrary arrow with its transported mate is the conclusion, not an assumption.
Applied to the scalar units, beta adjuncts and comparison mates this identifies
all the transported specified arrows, including m, gamma and kappa.
Source: Stacks 07A6 and 0FPI, scalar-unit refinement step 6
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def AdjunctTransport {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B]
    {L : A ⥤ B} {U : B ⥤ A} (a : L ⊣ U) : Prop :=
  ∀ (A' : Type uA') (B' : Type uB') [Category.{vA'} A'] [Category.{vB'} B']
    (EA : A ≌ A') (EB : B ≌ B') {L' : A' ⥤ B'} {U' : B' ⥤ A'}
    (a' : L' ⊣ U')
    (left : L ⋙ EB.functor ≅ EA.functor ⋙ L')
    (right : U ⋙ EA.functor ≅ EB.functor ⋙ U'),
    (∀ M : A, EA.functor.map (a.unit.app M) ≫ right.hom.app (L.obj M) ≫
      U'.map (left.hom.app M) = a'.unit.app (EA.functor.obj M)) →
    (∀ N : B, L'.map (right.hom.app N) ≫ a'.counit.app (EB.functor.obj N) =
      left.inv.app (U.obj N) ≫ EB.functor.map (a.counit.app N)) →
    ∀ (M : A) (N : B) (q : L.obj M ⟶ N),
    left.inv.app M ≫ EB.functor.map q =
      (a'.homEquiv (EA.functor.obj M) (EB.functor.obj N)).symm
        (EA.functor.map (a.homEquiv M N q) ≫ right.hom.app N)

variable {C X : Type c} [Category.{v} C] [Category.{v} X]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} X]
  {J : GrothendieckTopology C} {K : GrothendieckTopology X}
  {uInv : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
  {uPush : Sheaf K (Type r) ⥤ Sheaf J (Type r)} {adj : uInv ⊣ uPush}
  (g : Geometry uInv uPush adj)
  {pY : Scalars.{c, v, r} J} {pX : Scalars.{c, v, r} K}
  (nY : SheafOfModules.SuccessiveDerivedQuotient.Normalization
    (J := J) pY)
  (nX : SheafOfModules.SuccessiveDerivedQuotient.Normalization
    (J := K) pX)
  (e : Comparisons g nY nX)

/-- The canonical comparison G_A Res_X to Res_Y G_R, obtained by taking the
right-adjoint conjugate of the normalized inverse-image/scalar comparison.
Source: Stacks 07A6, 0D6D, 0D6E and 0FPI
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def theta {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R) :
    nX.right (g.rings.map a) ⋙ g.right A ≅ g.right R ⋙ nY.right a :=
  (conjugateIsoEquiv ((nY.adjunction a).comp (g.adjunction R))
    ((g.adjunction A).comp (nX.adjunction (g.rings.map a))) (e.derived a).symm).symm

/-- The specified projection beta is the scalar-adjunction transpose of G_A of
its scalar unit, followed by the canonical comparison with exact restriction.
The functor-category adjunction makes naturality part of this construction.
Source: Stacks 07A6 and 0FPI
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def beta {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R) :
    g.right A ⋙ (pY a).derived ⟶ (pX (g.rings.map a)).derived ⋙ g.right R :=
  (((nY.adjunction a).whiskerRight (D K (g.rings.obj A))).homEquiv
    (g.right A) ((pX (g.rings.map a)).derived ⋙ g.right R)).symm
      ((leftUnitor (g.right A)).inv ≫
        whiskerRight (nX.adjunction (g.rings.map a)).unit (g.right A) ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft (pX (g.rings.map a)).derived (theta g nY nX e a).hom ≫
        (Functor.associator _ _ _).inv)

/-- The coefficient arrow gamma on Y, using the normalized scalar unit and associator.
Source: Stacks 07A6 and 0D6D
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def gamma {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S) :
    (pY a).derived ⟶ (pY (a ≫ c)).derived ⋙ nY.right c :=
  unitArrow (pY a).derived (nY.adjunction c) (nY.derived a c)

/-- The same scalar-unit arrow m on X, retaining the inverse-image ring-map equality.
Source: Stacks 07A6 and 0D6D
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def m {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S) :
    (pX (g.rings.map a)).derived ⟶
      (pX (g.rings.map (a ≫ c))).derived ⋙ nX.right (g.rings.map c) :=
  unitArrow (pX (g.rings.map a)).derived (nX.adjunction (g.rings.map c))
    (targetAssociator g nX a c)

/-- G_R(m) followed by the specified comparison with restriction.
Source: Stacks 0D6E and 0FPI
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
def kappa {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S) :
    (pX (g.rings.map a)).derived ⋙ g.right R ⟶
      ((pX (g.rings.map (a ≫ c))).derived ⋙ g.right S) ⋙ nY.right c :=
  whiskerRight (m g nX a c) (g.right R) ≫ (Functor.associator _ _ _).hom ≫
    whiskerLeft (pX (g.rings.map (a ≫ c))).derived (theta g nY nX e c).hom ≫
    (Functor.associator _ _ _).inv

/-- Simultaneous canonical shift witnesses, fixed by the universal computation
counits, the localization factors of restriction, and the scalar adjunctions.
Source: Stacks 07A6, 0FPI and shifted K-injective computation, Tags 0B56 and 0DV0
(blueprint: lem-sfb-geometric-coefficient-square-transport). -/
structure Shifts where
  [scalarY : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R), (pY a).derived.CommShift ℤ]
  [scalarX : ∀ {A R : Sheaf K CommRingCat.{r}} (a : A ⟶ R), (pX a).derived.CommShift ℤ]
  [restrictY : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R), (nY.right a).CommShift ℤ]
  [restrictX : ∀ {A R : Sheaf K CommRingCat.{r}} (a : A ⟶ R), (nX.right a).CommShift ℤ]
  canonicalY : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R),
    NatTrans.CommShift (pY a).counit ℤ
  canonicalX : ∀ {A R : Sheaf K CommRingCat.{r}} (a : A ⟶ R),
    NatTrans.CommShift (pX a).counit ℤ
  restrictionY : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R),
    NatTrans.CommShift (nY.right_factors a).hom ℤ
  restrictionX : ∀ {A R : Sheaf K CommRingCat.{r}} (a : A ⟶ R),
    NatTrans.CommShift (nX.right_factors a).hom ℤ
  adjunctionY : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R),
    (nY.adjunction a).CommShift ℤ
  adjunctionX : ∀ {A R : Sheaf K CommRingCat.{r}} (a : A ⟶ R),
    (nX.adjunction a).CommShift ℤ
  theta : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R),
    NatTrans.CommShift (GeometricSquare.theta g nY nX e a).hom ℤ
  beta : ∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R),
    NatTrans.CommShift (GeometricSquare.beta g nY nX e a) ℤ
  gamma : ∀ {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S),
    NatTrans.CommShift (GeometricSquare.gamma nY a c) ℤ
  m : ∀ {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S),
    NatTrans.CommShift (GeometricSquare.m g nX a c) ℤ
  kappa : ∀ {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S),
    NatTrans.CommShift (GeometricSquare.kappa g nY nX e a c) ℤ

/-- The canonical scalar-unit square in D(R), naturally in the unbounded input,
with all integer shifts, restriction to A and conjugation by exact equivalences.
The last formula writes each transported arrow as e_source inverse, E(arrow),
e_target; compatibility with the units, counits and restriction comparisons means
precisely that these are the specified arrows in the equivalent presentation.

Source: current blueprint direct-images proof paragraph (3), scalar-unit refinement;
Stacks 07A6, 0D6D, 0D6E, 0FPI, 0B56 and 0DV0
(blueprint: lem-sfb-geometric-coefficient-square-transport).

Proof:
1. Exact restriction is the derived direct image of the identity-topos coefficient
morphism (lem-pur-sheaf-ring-derived-coefficient-adjunction). The normalized
composition and monoidal comparison theorems identify theta with its right mate;
the triple comparison satisfies the cocycle by taking mates of tensor reassociation.
2. On a common flat-term K-flat representative gamma and m send r tensor x to
c(r) tensor x. Precomposing with the a-unit gives the ca-unit since c(1)=1
(lem-pur-derived-change-of-rings and the normalized coefficient adjunction).
3. The a-adjunct of gamma followed by restriction of beta_S is the ca-adjunct
of beta_S, namely G_A of the ca-unit followed by theta_ca.
4. Naturality of theta_a, its cocycle and step 2 identify the a-adjunct of
beta_R followed by kappa with the same arrow. Injectivity of the scalar Hom
bijection gives equality in D(R); faithfulness of restriction is not used.
5. All constructions are natural transformations. Canonical derived adjunctions
commute with shifts (lem-weil-pbc-derived-adjunction-shift); K-injective shifts
compute the same normalized direct-image comparisons. On K-flat complexes the
scalar maps have degree zero and commute with the signed shift differentials.
Transposing the shift squares proves the beta squares.
6. Apply restriction to the equality. Under exact equivalences, transport each
arrow by the displayed endpoint isomorphisms. Functoriality and cancellation of
adjacent inverse isomorphisms preserve composites. Compatibility of the units,
counits and restriction comparisons identifies their mates with these transported
arrows by adjoint uniqueness, so these are the same specified maps. -/
theorem geometricCoefficientSquareTransport [PreservesFiniteLimits uInv] :
    Nonempty (Shifts g nY nX e) ∧
    (∀ {A R : Sheaf J CommRingCat.{r}} (a : A ⟶ R),
      AdjunctTransport (nY.adjunction a) ∧
      AdjunctTransport
        (nX.adjunction (g.rings.map a)) ∧
      AdjunctTransport (g.adjunction A)) ∧
    ∀ {A R S : Sheaf J CommRingCat.{r}} (a : A ⟶ R) (c : R ⟶ S)
      (V : D K (g.rings.obj A)),
      (gamma nY a c).app ((g.right A).obj V) ≫
          (nY.right c).map ((beta g nY nX e (a ≫ c)).app V) =
        (beta g nY nX e a).app V ≫ (kappa g nY nX e a c).app V ∧
      (nY.right a).map ((gamma nY a c).app ((g.right A).obj V) ≫
          (nY.right c).map ((beta g nY nX e (a ≫ c)).app V)) =
        (nY.right a).map
          ((beta g nY nX e a).app V ≫ (kappa g nY nX e a c).app V) ∧
      ∀ (T : Type t) [Category.{h} T] [HasShift T ℤ] [Preadditive T] [HasZeroObject T]
        [∀ n : ℤ, (shiftFunctor T n).Additive]
        [Pretriangulated T] (E : D J R ≌ T) [E.functor.CommShift ℤ]
        [E.functor.IsTriangulated]
        (W₀ W₁ W₂ W₃ : T)
        (i₀ : E.functor.obj ((pY a).derived.obj ((g.right A).obj V)) ≅ W₀)
        (i₁ : E.functor.obj
          ((nY.right c).obj ((pY (a ≫ c)).derived.obj ((g.right A).obj V))) ≅ W₁)
        (i₂ : E.functor.obj ((g.right R).obj ((pX (g.rings.map a)).derived.obj V)) ≅ W₂)
        (i₃ : E.functor.obj ((nY.right c).obj
          ((g.right S).obj ((pX (g.rings.map (a ≫ c))).derived.obj V))) ≅ W₃),
        (i₀.inv ≫ E.functor.map ((gamma nY a c).app ((g.right A).obj V)) ≫ i₁.hom) ≫
            (i₁.inv ≫ E.functor.map
              ((nY.right c).map ((beta g nY nX e (a ≫ c)).app V)) ≫ i₃.hom) =
          (i₀.inv ≫ E.functor.map ((beta g nY nX e a).app V) ≫ i₂.hom) ≫
            (i₂.inv ≫ E.functor.map ((kappa g nY nX e a c).app V) ≫ i₃.hom) := by
  sorry

end SheafOfModules.RingedCoefficientProjection.GeometricSquare
