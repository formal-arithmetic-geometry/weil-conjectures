/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.OpenTensorNormalizationData

/-! # Finite operation comparisons for prescribed realizations

Source: Stacks 03D7, 0F6Z, 06YU and 0GL1.
(blueprint: lem-sf-finite-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace SheafOfModules.OpenTensorNormalization

/-- The direct-image part of a finite pullback pin, before taking its mate.
It is an isomorphism fixed by the underlying section identifications.
Source: Stacks 03D7 (blueprint: lem-sf-finite-operation-comparisons). -/
def FiniteDirectPin {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S) : Type _ :=
  { right : ProEtale.lowerStar (ModuleCat.{u + 1} A) f ⋙ eR.equivalence.functor ≅
      eS.equivalence.functor ⋙ direct .ordinary f R S c //
    ∀ (M : FiniteModules A X) (W : Y.ProEtᵒᵖ)
        (x : (eR.equivalence.functor.obj
          ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).val.obj W),
      (eS.underlying.hom.app M).hom.app ((baseChange .ordinary f).op.obj W)
        ((right.hom.app M).val.app W x) =
      (eR.underlying.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj M)).hom.app W x }

/-- The proved ordinary part of a finite pullback comparison: its right square,
left-adjoint comparison, and the defining mate equation.
Source: Stacks 03D7 (blueprint: lem-sf-finite-operation-comparisons). -/
structure FiniteOrdinaryPullPin {A : Type (u + 1)} [CommRing A] {X Y : Scheme.{u}}
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    {k : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ S.obj}
    (eR : FiniteRealization A Y R i) (eS : FiniteRealization A X S k)
    (f : X ⟶ Y) (c : R ⟶ ((baseChange .ordinary f).sheafPushforwardContinuous
      CommRingCat.{u + 1} (topology .ordinary Y) (topology .ordinary X)).obj S)
    (p : Pullback R S (direct .ordinary f R S c)) where
  right : FiniteDirectPin eR eS f c
  ordinary : ProEtale.upperStar (ModuleCat.{u + 1} A) f ⋙ eS.equivalence.functor ≅
    eR.equivalence.functor ⋙ p.ordinary
  mate : ∀ M : FiniteModules A Y,
    eR.equivalence.functor.map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app M) ≫
      right.val.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj M) =
    p.adjunction.unit.app (eR.equivalence.functor.obj M) ≫
      (direct .ordinary f R S c).map (ordinary.inv.app M)
  limits : PreservesFiniteLimits p.ordinary
  colimits : PreservesFiniteColimits p.ordinary
  derivedExact : IsIso p.epsilon

/-- Prescribed realizations and ordinary pullback pins extend to the derived
pullback, open extension and tensor comparisons.

Proof: use the two supplied ordinary pullback comparisons and their mate equations. Fixed
coefficient inverse image is exact. Hence its conjugate through the realization
equivalences is exact, so the ordinary ringed pullback is exact as well.
The universal property of the left derived functor then gives its derived
comparison, and uniqueness on the localization gives the equation on every
complex required by finitePullModel. Apply this argument to g and gU.

For each open, the underlying restriction functors identify by the published
upperStarIsoOpenImmersionRestriction. Lift this sectionwise identification to
module sheaves using scalar compatibility. Its mate under the two extension
by zero adjunctions gives the shriek comparison and the stated unit equation.
Both operations are exact; localizing their termwise comparisons gives the two
FiniteExactPin equations and therefore the open pins.

The module tensor universal property gives the comparison of ordinary tensor
products sending x tensor y to x tensor y under the underlying identifications.
It is invertible because the realizations and their inverses preserve these
bilinear universal properties. Apply it in each bidegree and commute the exact
realization equivalence with the direct sums of the signed total complex.
Naturality in both variables makes the resulting map commute with both parts
of the differential and its sign. This gives the total comparison and its
pure-summand equation. Equivalences of these module categories preserve flat
objects and flat K-flat complexes by the same tensor comparison and exactness.
The two tensor localization factorizations consequently descend the total
comparison to the tensor functor comparison; uniqueness of descent proves the
representative equation in finiteTensorModel. Carry this out on X and U.
Assemble the four original realizations and these eight comparisons, retaining
all six pins. No base-change or projection-arrow equality is used in this
construction; those are conclusions of the separate transport lemma.
Source: Stacks 03D7 (module adjunction), 0F6Z (open restriction), 015F (exact
localization), 06YU and 0GL1 (derived tensor and its open projection map).
(blueprint: lem-sf-finite-operation-comparisons) -/
theorem finite_operation_comparisons_exists (A : Type (u + 1)) [CommRing A]
    [Finite A] {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (rX : FiniteRealization A X
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
    (rX' : FiniteRealization A X'
      ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))
      (toSheafify (ProEt.topology X') ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A))))
    (rU : FiniteRealization A U
      (restrictRing .ordinary j
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)))
      (Functor.whiskerLeft (openInclusion .ordinary j).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)))))
    (rU' : FiniteRealization A U'
      (restrictRing .ordinary j'
        ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A)))
      (Functor.whiskerLeft (openInclusion .ordinary j').op
        (toSheafify (ProEt.topology X')
          ((Functor.const X'.ProEtᵒᵖ).obj (CommRingCat.of A)))))
    (pull : FiniteOrdinaryPullPin rX rX' g
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)) o.gPull)
    (pullU : FiniteOrdinaryPullPin rU rU' gU (cornerCoefficient t) o.gUPull) :
    ∃ e : FiniteComparisons A o, e.realizeX = rX ∧ e.realizeX' = rX' ∧
      e.realizeU = rU ∧ e.realizeU' = rU' := by
  sorry

end SheafOfModules.OpenTensorNormalization
