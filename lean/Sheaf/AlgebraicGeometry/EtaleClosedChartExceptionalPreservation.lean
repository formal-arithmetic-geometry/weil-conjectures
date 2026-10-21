/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.Compactification.Affine
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement
import Sheaf.AlgebraicGeometry.OpenSourceComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleStalkTorTest
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.FlatConstructibleTensor
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk
import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionAbelianDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude

/-! # Exceptional inverse image on a closed affine-space chart

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality and Charts; closed-chart supplement
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The literal ordinary etale functor pi^*(-)(r)[2r]. Its Tate sheaf is the recorded
finite etale twist, and tensor and shift act on the entire derived category.
Source: main-20261015, exceptional-reduction Locality and Charts, closed-chart supplement
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def closedChartTwistedPullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (V : Scheme.{u}) (r : ℕ) :
    DerivedCategoryModule A V ⥤
      DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin r)) V) :=
  (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V)).mapDerivedCategory ⋙
    derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin r)) V)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin r)) V) N A hA r)) ⋙
    shiftFunctor _ (2 * (r : ℤ))

/-- The specified compact-support comparison Fu_! -> v_! H i_*: compose, use the
chart equality, decompose, and use the canonical proper and open normalizations.
Source: main-20261015, exceptional-reduction Locality and Charts, proof steps 2--4
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def closedChartCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f]
    [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory :=
  Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion A u).symm _ ≪≫
    unboundedEtaleLowerShriekCompIso A u f ≪≫
    unboundedEtaleLowerShriekCongr A h ≪≫
    (unboundedEtaleLowerShriekCompIso A
      (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) v).symm ≪≫
    Functor.isoWhiskerRight
      (unboundedEtaleLowerShriekCompIso A i
        (AffineSpace (ULift.{u} (Fin r)) V ↘ V)).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) i) _) _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIsoOfIsOpenImmersion A v)

/-- The assertion after installing only consequences of the geometric and coefficient
hypotheses. The purity adjunction is quantified universally: in particular the assertion
applies to the adjunction normalized by the integration counit of vector-bundle purity.
Existence is included, so no purity or boundedness assumption is imposed on an input.
The counit equation determines the natural isomorphism uniquely for that specified
adjunction, and is invariant under changing the chosen ambient right adjoint.
Source: main-20261015, exceptional-reduction Locality and Charts, proof steps 1--8
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def ClosedChartExceptionalAssertion
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    {X Y U V : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ Y) (v : V ⟶ Y) (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V)
    [IsOpenImmersion u] [IsOpenImmersion v] [IsClosedImmersion i]
    [QuasiCompact u] [QuasiCompact v] [QuasiCompact f] [QuasiCompact (u ≫ f)]
    [HasCompactification u] [HasCompactification v] [HasCompactification f]
    [HasCompactification (u ≫ f)]
    [HasCompactification (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V))]
    [HasCompactification ((i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v)]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop :=
  Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r) ∧
  (∀ (F : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ F)
    (adjπ : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin r)) V ↘ V) ⊣ closedChartTwistedPullback A N hA V r),
    ∃! e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
          closedChartTwistedPullback A N hA V r) ⋙
          (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint,
      ∀ L : DerivedCategoryModule A Y,
        (closedChartCompactSupportComparison A u f v r i h).hom.app
            ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj L)) ≫
          ((R(lowerStar (ModuleCat.{u + 1} A) i) ⋙
            rightDerivedLowerShriek (ModuleCat.{u + 1} A)
              (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ⋙
            (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory).map
              (e.hom.app L) ≫
          (((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).comp adjπ).comp
            (derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} A) v)).counit.app L =
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u).comp adjF).counit.app L) ∧
  ∀ L : DerivedCategoryModule A Y,
    DerivedCategory.isBoundedConstructible A Y L →
    (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) →
    DerivedCategory.isBoundedConstructible A U
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L))) ∧
    ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A U a b
      ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        ((closedChartTwistedPullback A N hA V r).obj
          ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj L)))

/-- Install the Noetherian, compactification and finite-coefficient instances that follow
from the stated field, finite-type and affine-open hypotheses; then assert the closed-chart
comparison and preservation. None of these consequences is an extra input.
Source: main-20261015, exceptional-reduction closed-chart supplement, proof step 1
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation). -/
def ClosedChartExceptionalPreservation
    (ell : ℕ) [Fact ell.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] {X Y U V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsAffine U] [IsAffine V] (u : U ⟶ X) (v : V ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V) [IsClosedImmersion i]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) : Prop :=
  letI : Finite (Padic.coefficientExtensionRing ell E n) :=
    Padic.finite_coefficientExtensionRing ell E n hn
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsNoetherian X := {}
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  letI : IsNoetherian Y := {}
  letI : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion u
  letI : IsNoetherian U := {}
  letI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  letI : IsNoetherian V := {}
  letI : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  letI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  letI : IsSeparated (f ≫ (Y ↘ Spec (.of k))) :=
    (comp_over f (Spec (.of k))).symm ▸ inferInstance
  letI : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  ∃ hA : ((ell ^ n : ℕ) : Padic.coefficientExtensionRing ell E n) = 0,
    ClosedChartExceptionalAssertion (Padic.coefficientExtensionRing ell E n)
      (ell ^ n) hA u f v r i h

/-- Exceptional inverse image on a closed affine-space chart, before any boundedness
restriction, and bounded constructible finite-Tor preservation of its displayed right side.
The normalized vector-bundle purity adjunction is one of the adjunctions quantified in
`ClosedChartExceptionalAssertion`; its explicit counit equation gives the canonical iso.

Source: main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Locality and Charts, closed-chart supplement
(blueprint: lem-pur-etale-closed-chart-exceptional-preservation).

Proof:
1. The coefficient ring is finite. In its DVR, ell lies in the uniformizer ideal, so
   ell^n kills A; ell != p makes this exponent invertible on all the schemes. Finite
   type over a field gives Noetherian X,Y. Their affine opens are Noetherian, as are
   the affine space P and its open complement W. Nagata supplies compactifications.
2. Exact open extension has the ordinary derived adjunction u_! |- u^* and v_! |- v^*.
   Compose the unbounded compact-support comparisons using fu = v pi i; normalize
   the open factors by extension by zero, and the proper closed factor by i_*.
   This is exactly `closedChartCompactSupportComparison`.
3. Vector-bundle purity for the trivial rank-r bundle supplies H |- pi^*(-)(r)[2r]
   on all unbounded inputs. Compose it with i_* |- Ri! and v_! |- v^*. The natural
   Hom chain of proof step 3 identifies this composite right adjoint with u^* F.
4. Transpose the identity through that Hom chain. The resulting iso e is the unique
   one satisfying lambda ; J(e) ; epsilon^J = epsilon^(Fu). Expanding the composite
   counits gives the equation in `ClosedChartExceptionalAssertion`. This argument
   works for every choice of the two right-adjoint presentations, in particular for
   the vector-bundle integration normalization. No boundedness of F(L) is used.
5. For bounded constructible L with Tor interval [a,b], exact inverse image along v
   and pi preserves the cohomological bounds, constructibility and Tor interval,
   using constructible pullback and the geometric-stalk Tor test.
6. The ordinary Tate line A_P(r) is finite locally constant, flat and rank one.
   Flat constructible tensor and tensor/stalk comparison preserve the bounds.
   The shift [2r] changes the Tor interval to [a-2r,b-2r], including r=0.
7. Bound the dimensions of all field base changes of W by d. The arbitrary-field
   torsion direct-image dimension theorem and coefficient-forgetting comparison
   give R^q j_* M = 0 for every module sheaf M and q > c = 2d.
8. Finite-type direct-image constructibility supplies the other complement
   hypothesis. The closed-support Tor theorem then makes Ri! of this expression
   bounded constructible with interval [a-2r,b-2r+c+1]. This proves preservation
   independently of the unbounded comparison of steps 2--4. -/
theorem etaleClosedChartExceptionalPreservation
    (ell : ℕ) [Fact ell.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) (hn : 1 ≤ n)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hell : ell ≠ p)
    {X Y U V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsAffine U] [IsAffine V] (u : U ⟶ X) (v : V ⟶ Y)
    [IsOpenImmersion u] [IsOpenImmersion v] (r : ℕ)
    (i : U ⟶ AffineSpace (ULift.{u} (Fin r)) V) [IsClosedImmersion i]
    (h : u ≫ f = (i ≫ (AffineSpace (ULift.{u} (Fin r)) V ↘ V)) ≫ v) :
    ClosedChartExceptionalPreservation ell E n hn k f u v r i h := by
  sorry

end AlgebraicGeometry.Etale
