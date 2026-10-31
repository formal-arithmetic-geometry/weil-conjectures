/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SecSmoothPurity.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
public import WeilConjectures.SecSmoothPurity.CondensedOpenProperDefinitions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.IntegralArbitraryPullbackReduction
import WeilConjectures.AlgebraicGeometry.NoetherianProperFiniteness
import WeilConjectures.SixFunctors.RationalIntegralGenerators
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.AlgebraicGeometry.PullbackConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.ProperIntegralRationalScalarComparison
import WeilConjectures.AlgebraicGeometry.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.RingedDerivedSliceLocalization
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients

/-!
# Compact-support base change

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
`sk-prop-sp-purity-bc/det-prop-sf-cbc.md`
(blueprint: det-prop-sf-cbc).

The declarations below state the finite étale, finite pro-étale-origin, and condensed
compact-support exchanges. The condensed exchange is the existing proper/open composite,
with its canonical open comparison built from the arbitrary-base open comparison.

## Main definitions

* `compactSupportCondensedFormalism` organizes the existing ordinary derived functors.
* `compactSupportOpenBaseChangeIso` constructs the canonical open comparison.

## Main statements

* `finite_compactSupportBaseChange` and its pro-étale-origin version state clause (a).
* `condensed_compactSupportBaseChange` states clause (b).
* The three following coherence theorems state identity and both pasting laws.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CondensedOpenProper

attribute [local instance 30000]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local instance 30000]
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
attribute [local instance 40000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]


/-- The existing ordinary condensed-module functors, organized in the existing exchange formalism.
Pullback is total left derivation, direct image is total right derivation, and open extension is
exact termwise descent. The adjunctions and every pullback compositor are the published ones;
only the existing exact/total comparison transports the right side of the open adjunction.
Source: `det-prop-sf-cbc`, exchange definition and proof steps 9--10
(blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportCondensedFormalism : CompactSupportFormalism := by
  letI (X : Scheme.{u}) :
      ((Scheme.ProEt.topology X).W (A := Ab.{u + 1})).IsMonoidal :=
    CategoryTheory.GrothendieckTopology.W.monoidal
  exact
  { obj := fun X ↦ D Λ X
    pb := fun f ↦ detSfDerivedPullback Λ f
    pbId := fun T ↦ leftDerivedUpperStarId Λ T
    pbComp := fun f g ↦ leftDerivedUpperStarComp Λ f g
    pbComp_assoc := fun f g h K ↦ leftDerivedUpperStarComp_assoc_app Λ f g h K
    pbId_comp := fun f K ↦ leftDerivedUpperStarComp_id_left_app Λ f K
    pbComp_id := fun f K ↦ leftDerivedUpperStarComp_id_right_app Λ f K
    pf := fun f ↦ (lowerStar Λ f).rightDerivedFunctor
    adj := fun f ↦ derivedUpperStarLowerStarAdjunction Λ f
    sh := fun j _ ↦ by
      haveI : IsOpenImmersion j := Fact.out
      exact J Λ j
    shAdj := fun j _ ↦ by
      haveI : IsOpenImmersion j := Fact.out
      exact (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm }

/-- Canonical change from an arbitrary Cartesian open square to its literal pullback.
The isomorphism `sq.isoPullback` supplies an equivalence of the exact derived pullback functors.
Insert the inverse counit for its open adjunction, then use the published open and pullback
compositors. This constructs the transport without a choice of an unspecified comparison.
Source: `det-prop-sf-cbc`, canonical open comparison in proof step 8
(blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportOpenPullbackTransport
    {U' U Z' Z : Scheme.{u}} {t : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback t j' j b) :
    P Λ t ⋙ J Λ j' ≅ P Λ (pullback.fst j b) ⋙ J Λ (pullback.snd j b) := by
  let e := sq.isoPullback
  letI : (P Λ e.hom).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (P Λ e.hom) (P Λ e.inv)
      ((pId Λ _).symm ≪≫ eqToIso (by rw [e.inv_hom_id]) ≪≫ pComp Λ e.inv e.hom)
      ((pComp Λ e.hom e.inv).symm ≪≫ eqToIso (by rw [e.hom_inv_id]) ≪≫ pId Λ _)
      ).isEquivalence_functor
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ e.hom
  letI : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
  let et : P Λ t ≅ P Λ (pullback.fst j b) ⋙ P Λ e.hom :=
    eqToIso (by rw [sq.isoPullback_hom_fst]) ≪≫ pComp Λ e.hom (pullback.fst j b)
  let ej : J Λ j' ≅ J Λ e.hom ⋙ J Λ (pullback.snd j b) :=
    jCongr Λ sq.isoPullback_hom_snd.symm ≪≫
      (jComp Λ e.hom (pullback.snd j b)).symm
  exact Functor.isoWhiskerRight et (J Λ j') ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (P Λ (pullback.fst j b))
      (Functor.isoWhiskerLeft (P Λ e.hom) ej ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso adj.counit) (J Λ (pullback.snd j b)) ≪≫
        Functor.leftUnitor _)

/-- The canonical beta of the supplied compactification square, constructed from
`condensedOpenBaseChangeDerivedIso`. Its middle factor is precisely that existing comparison;
the other factors change its literal pullback to the compactification pullback and identify
exact derived pullback with total left derivation. All data are explicitly constructed.
Source: `det-prop-sf-cbc`, displayed beta and proof step 8 (blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportOpenBaseChangeIso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (c : Compactification f) :
    D((c.i)_!open⟦Λ⟧) ⋙ detSfDerivedPullback Λ (pullback.fst c.g g) ≅
      detSfDerivedPullback Λ (pullback.fst f g) ⋙ D(((c.baseChange g).i)_!open⟦Λ⟧) :=
  Functor.isoWhiskerLeft D((c.i)_!open⟦Λ⟧)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst c.g g)) ≪≫
    condensedOpenBaseChangeDerivedIso (Mon.mk Λ) c.i (pullback.fst c.g g) ≪≫
    (compactSupportOpenPullbackTransport Λ
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f g))).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.fst f g)).symm
      D(((c.baseChange g).i)_!open⟦Λ⟧)

/-- The canonical open mate is invertible in the ordinary condensed-module formalism.
Proof steps: apply `condensedOpenBaseChangeDerivedIso` to a literal pullback; transport through
`sq.isoPullback` using `compactSupportOpenPullbackTransport` and the exact/total comparisons.
The open-adjunction normalization identifies its inverse with the unit--square--counit mate.
Thus the supplied inverse proves invertibility for every Cartesian open square.
Source: `det-prop-sf-cbc`, proof steps 8--9 (blueprint: det-prop-sf-cbc). -/
@[instance] theorem compactSupportCondensedFormalism_hasBaseChange :
    (compactSupportCondensedFormalism Λ).HasBaseChange := by
  sorry

open CategoryTheory.TwoSquare

/-- The formalism's exchange is the existing specified proper-then-open composite.
Proof steps: expand the generic compact-support exchange. Its proper factor is the mate of
the published pullback-square compositor, hence `detSfProperBaseChangeMap`. The inverse open
factor is beta: the arbitrary-base comparison is normalized by the same open unit and counit.
Cancel the exact/total comparison factors. Functor associators have identity components, so
the result is exactly `detSfCompactSupportBaseChangeComposite`, as natural transformations.
Source: `det-prop-sf-cbc`, exchange definition and proof steps 8--9
(blueprint: det-prop-sf-cbc). -/
theorem compactSupportCondensedFormalism_exchange {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (c : Compactification f) :
    ((compactSupportCondensedFormalism Λ).shriekBaseChange c (c.baseChange g) (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f g))
      (c.isPullback_g_ofIsPullback (IsPullback.of_hasPullback f g)).flip).natTrans =
    detSfCompactSupportBaseChangeComposite Λ f g c
      (compactSupportOpenBaseChangeIso Λ f g c) := by
  sorry

/-- Finite étale compact-support base change for an arbitrary Cartesian square.
Proof steps: apply `thm-cbc-finite-torsion` to the supplied compactification and its pullback;
the exchange is the canonical proper mate followed by open base change. Its finite-ring and
arbitrary-base hypotheses are exactly those of clause (a), with no constructibility restriction.
Source: `det-prop-sf-cbc`, finite étale clause (blueprint: det-prop-sf-cbc). -/
theorem finite_compactSupportBaseChange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (c : Compactification f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiCompact f'] [HasCompactification f'] :
    IsIso (AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
      Λ sq c) := by
  infer_instance

/-- Finite compact-support exchange after pullback to the pro-étale site.
Proof steps: retain the specified etale-origin witness `(L,alpha)` and apply the finite-level
pro-étale exchange theorem using the supplied compactification alternative. Comparison
isomorphisms transport the finite étale identity and both pasting laws, and the resulting
component is independent of the witness.
Source: `det-prop-sf-cbc`, finite pro-étale-origin clause (blueprint: det-prop-sf-cbc). -/
theorem finite_compactSupportBaseChange_proetaleOrigin
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (c : Compactification f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiCompact f'] [HasCompactification f']
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (wK : Scheme.FixedEtaleOriginWitness X Λ K) :
    IsIso ((AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} Λ) sq c).app K.obj) := by
  exact AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    Λ sq c K.obj ⟨wK.complex.obj, wK.complex.property, ⟨wK.iso⟩⟩

/-- Condensed compact-support base change for `O_E`, `E`, and `Q̄_ell`.
Proof steps (the finite stages are the preceding two theorems):
3. Exact open extension preserves boundedness. Extend each finite constructible stratification
by the complement to obtain bounded constructibility on the original Noetherian compactification.
Noetherian proper finiteness gives the proper image on Y, with finite constant scalar models.
Exact pullback preserves their global cohomological interval and pulls their strata back to Y'.
Slice localization identifies the proper mate on every affine open of the arbitrary target.
4. For O_E, the integral arbitrary-pullback reduction gives complete endpoints and identifies
the residue of the actual ordinary mate with finite etale-origin proper exchange. Finite
proper base change and derived Nakayama make the integral mate invertible, without completion
of the pullback and without restricting the new base.
5. The integral/rational proper scalar comparisons are invertible on both qcqs schemes above
each affine target open. The constant scalar models supply constructibility after pullback;
ctf=bc supplies the finite Tor amplitudes needed for these comparisons.
6. The algebraic-closure coefficient is the filtered colimit of its finite coefficient-field
extensions. The bounded-below continuity theorem commutes proper direct image with this
scalar diagram, giving the algebraic-closure scalar comparison too.
7. The scalar/geometric exchange rectangle identifies each rational proper mate with scalar
extension of the integral mate on the integral generators. Rational integral generation,
canonical shift compatibility, and triangle two-out-of-three extend invertibility to every
bounded constructible rational input, including the algebraic-closure case.
8. Apply the proper result to j_!K and compose with the canonical beta constructed above.
The global pulled-back stratification, with local finite presentation checked on affine opens,
gives bounded constructibility of the source; the exchange isomorphism gives it for the target.
The separate identity and two pasting theorems below state the coherence clauses (steps 9--10).
Source: `det-prop-sf-cbc`, clause (b) and coherence clauses (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupportBaseChange
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    (c : Compactification f) [IsNoetherian c.Z]
    [QuasiCompact (pullback.snd f g)] :
    ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ Y')
        ((detSfCompactSupport Λ c ⋙ detSfDerivedPullback Λ g).obj K) ∧
      boundedConstructible (condensedRingObj Λ Y')
        ((detSfDerivedPullback Λ (pullback.fst f g) ⋙
          detSfCompactSupport Λ (c.baseChange g)).obj K) ∧
      IsIso ((detSfCompactSupportBaseChangeComposite Λ f g c
        (compactSupportOpenBaseChangeIso Λ f g c)).app K) := by
  sorry


/-- Identity-square law for the actual condensed compact-support exchange.
Proof steps: proper mate normalization gives the proper identity square. The open mate has
the open identity normalization. Their composite cancels the intermediate identity comparison;
the surviving factors are exactly the two displayed pullback identity comparisons and unitors.
`compactSupportCondensedFormalism_exchange` identifies this exchange with the specified
proper/open composite for the literal pullback realization.
Source: `det-prop-sf-cbc`, identity clause and proof step 9 (blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupportBaseChange_id
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ((compactSupportCondensedFormalism Λ).shriekBaseChange c c (𝟙 c.Z)
      (IsPullback.of_id_fst) (IsPullback.of_id_fst)).natTrans =
      Functor.whiskerLeft ((compactSupportCondensedFormalism Λ).shriek c)
        ((compactSupportCondensedFormalism Λ).pbId Y).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight ((compactSupportCondensedFormalism Λ).pbId X).inv
          ((compactSupportCondensedFormalism Λ).shriek c) := by
  exact CompactSupportFormalism.shriekBaseChange_id
    (compactSupportCondensedFormalism Λ) c _ _

/-- Cartesian pasting for the actual condensed compact-support exchange.
Proof steps: expand each exchange as proper mate followed by inverse open mate. Proper
mate-pasting identifies the proper factors; normalized open pasting identifies the open
factors. Naturality interchanges the two middle factors. The surviving endpoint factors are
precisely the displayed pullback compositors. This is an equation of natural transformations
on all ordinary unbounded complexes, before any constructibility restriction.
Source: `det-prop-sf-cbc`, Cartesian-pasting clause and proof step 9
(blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupportBaseChange_paste_cartesian
    {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {a' : X'' ⟶ X'} {a : Y'' ⟶ Y'} {b' : X' ⟶ X} {b : Y' ⟶ Y}
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (h₁ : c''.Z ⟶ c'.Z) (h₂ : c'.Z ⟶ c.Z)
    (hi₁ : IsPullback a' c''.i c'.i h₁) (hp₁ : IsPullback h₁ c''.g c'.g a)
    (hi₂ : IsPullback b' c'.i c.i h₂) (hp₂ : IsPullback h₂ c'.g c.g b)
    (hi : IsPullback (a' ≫ b') c''.i c.i (h₁ ≫ h₂))
    (hp : IsPullback (h₁ ≫ h₂) c''.g c.g (a ≫ b)) :
    (compactSupportCondensedFormalism Λ).shriekBaseChange c c'' (h₁ ≫ h₂) hi hp =
      (((compactSupportCondensedFormalism Λ).shriekBaseChange c c' h₂ hi₂ hp₂ ≫ᵥ
        (compactSupportCondensedFormalism Λ).shriekBaseChange c' c'' h₁ hi₁ hp₁).whiskerLeft
          ((compactSupportCondensedFormalism Λ).pbComp' a' b' (a' ≫ b') rfl).inv).whiskerRight
          ((compactSupportCondensedFormalism Λ).pbComp' a b (a ≫ b) rfl).hom := by
  exact CompactSupportFormalism.shriekBaseChange_paste_horiz
    (compactSupportCondensedFormalism Λ) c c' c'' h₁ h₂ hi₁ hp₁ hi₂ hp₂ hi hp

/-- The canonical forward Gamma_Q comparison for a compactification triangle. The square is the
triangle's normalized Cartesian square, and `CondensedOpenProper.gamma` is the published forward
comparison; only the specified `OpenUnits` datum is bound, with no proper-exchange invertibility.
Source: `det-prop-sf-cbc`, proof step 10 (blueprint: det-prop-sf-cbc). -/
noncomputable def compactSupportCanonicalGamma
    (units : CondensedOpenProper.OpenUnits Λ)
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (T : Compactification.Triangle f g) :
    (compactSupportCondensedFormalism Λ).shriek T.cf ⋙
        (compactSupportCondensedFormalism Λ).shriek T.cg ⟶
      (compactSupportCondensedFormalism Λ).shriek T.cfg := by
  let F : CompactSupportFormalism := compactSupportCondensedFormalism Λ
  let sq : CommSq T.q T.cf.g T.p T.cg.i := CommSq.mk T.isPullback.w.symm
  exact
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.sh T.cf.i)
        ((Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (CondensedOpenProper.gamma Λ units sq)
            (CondensedOpenProper.R Λ T.cg.g) ≫
          (Functor.associator _ _ _).hom) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (CondensedOpenProper.jComp Λ T.cf.i T.q).hom
        (CondensedOpenProper.R Λ T.p ⋙ CondensedOpenProper.R Λ T.cg.g) ≫
      Functor.whiskerRight (CondensedOpenProper.jCongr Λ T.i_q).hom
        (CondensedOpenProper.R Λ T.p ⋙ CondensedOpenProper.R Λ T.cg.g) ≫
      Functor.whiskerLeft (CondensedOpenProper.J Λ T.cfg.i)
        ((CondensedOpenProper.rComp Λ T.p T.cg.g).hom ≫
          eqToHom (by rw [T.p_g]; rfl))

/-- Pasting in the compact-support direction through supplied compatible triangles.
The theorem uses the canonical forward Gamma_Q comparisons built from the supplied normalized
`OpenUnits` datum; these are transformations, so no invertibility of proper exchange is asserted.
Proof steps: apply the arbitrary-base mixed proper/open cube of
`lem-zl-condensed-open-proper-pasting` to the triangles' middle squares. The equations `hq` and
`hp` identify the common cube and its outer square; proper mate-pasting, open compositor pasting,
and naturality give the displayed equation.
Source: `det-prop-sf-cbc`, compact-support-direction clause and proof step 10
(blueprint: det-prop-sf-cbc). -/
theorem condensed_compactSupportBaseChange_paste_compactSupport
    {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    {f' : X' ⟶ Y'} {g' : Y' ⟶ S'} {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S}
    (T : Compactification.Triangle f g) (T' : Compactification.Triangle f' g')
    (a : T'.cf.Z ⟶ T.cf.Z) (c : T'.cg.Z ⟶ T.cg.Z) (b : T'.cfg.Z ⟶ T.cfg.Z)
    (hfi : IsPullback gX T'.cf.i T.cf.i a) (hfp : IsPullback a T'.cf.g T.cf.g gY)
    (hgi : IsPullback gY T'.cg.i T.cg.i c) (hgp : IsPullback c T'.cg.g T.cg.g gS)
    (hfgi : IsPullback gX T'.cfg.i T.cfg.i b) (hfgp : IsPullback b T'.cfg.g T.cfg.g gS)
    (hq : IsPullback a T'.q T.q b) (hp : b ≫ T.p = T'.p ≫ c)
    (units : CondensedOpenProper.OpenUnits Λ) :
    Functor.whiskerRight (compactSupportCanonicalGamma Λ units T)
        ((compactSupportCondensedFormalism Λ).pb gS) ≫
        ((compactSupportCondensedFormalism Λ).shriekBaseChange T.cfg T'.cfg b hfgi hfgp).natTrans =
      ((compactSupportCondensedFormalism Λ).shriekBaseChange T.cf T'.cf a hfi hfp ≫ₕ
        (compactSupportCondensedFormalism Λ).shriekBaseChange T.cg T'.cg c hgi hgp).natTrans ≫
        Functor.whiskerLeft ((compactSupportCondensedFormalism Λ).pb gX)
          (compactSupportCanonicalGamma Λ units T') := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
