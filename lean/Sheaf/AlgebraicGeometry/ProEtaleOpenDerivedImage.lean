/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Open direct image and its unit on K-injective pro-etale complexes

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization, proof of
lem-exc-proetale-support-triangle; Stacks Project, Tags 03CE, 04IX, 08FI, 070I,
070K, 070Y, 08BJ and 09T5 (blueprint: lem-exc-proetale-open-derived-image).

The coefficients are the published sheafified continuous-function ring sheaves, including
noncommutative finite rings. The direct image is Mathlib's pushforward along their actual
coefficient map. Its unit is normalized by the published small-model Kan adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The open direct image, with the action through the canonical coefficient map.
On V its underlying group is G(V times_T U); no commutativity is needed.
This only specializes Mathlib's pushforward to the recorded ring map.
Source: Stacks Project, Tags 03CE and 04IX
(blueprint: lem-exc-proetale-open-derived-image). -/
noncomputable abbrev finiteCoefficientOpenDirectImage {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    FiniteCoefficientModules U A ⥤ FiniteCoefficientModules T A :=
  SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange j)
    (J := Scheme.ProEt.topology T) (K := Scheme.ProEt.topology U)
    (finiteCoefficientDirectImageMap j A)

/-- The specified Kan-adjunction unit on sections, before the coefficient action is
transported along c inverse. That transport changes no underlying section or map.
The model transports retain the underlying objects, so the result already has the
section type of the actual direct image of the published transported pullback.
Source: Stacks Project, Tags 00YV and 03D2
(blueprint: lem-exc-proetale-open-derived-image). -/
noncomputable def finiteCoefficientOpenUnitSection {U T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)) :
    ((finiteCoefficientOpenDirectImage j A).obj
      ((finiteCoefficientModulePullback j A).obj N)).val.obj (op V) :=
  (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
    (finiteCoefficientModelRingUnit j A)).unit.app
      ((Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf T A)).obj N)).val.app
        (AsSmall.up.op.obj (op V))) m

/-- Restriction identifies the actual open module inverse image, its action and its
specified adjunction unit; it preserves K-injectives and computes the derived open unit.
The natural ring comparison is fixed on constant sections. The first unit equation fixes
`adj` to the small-model inverse-image adjunction, preventing a rescaled adjunction.
The second unit equation identifies it with restriction. The derived comparison `alpha`
is the termwise factorization through Q, and `beta` is the total right-derived comparison.
Its invertibility on the restricted K-injective is precisely the claimed representation.
The final equation says that, after these two comparisons, the derived unit is Q of the
ordinary complex unit, whose degreewise sections are the restrictions just specified.

Source: Weil blueprint, proof of lem-exc-proetale-support-triangle; Stacks Project,
Tags 03CE, 04IX, 08FI, 070I, 070K, 070Y, 08BJ and 09T5
(blueprint: lem-exc-proetale-open-derived-image).

Proof:
1. Identify the open site with the slice by lem-weil-proetale-weakly-etale-localization.
   The initial inverse-image indexing pair at W/U identifies inverse image with evaluation
   on W/T (lem-sfb-proetale-object-inverse-image-restriction, its ring-independent clause).
2. Restrict the continuous-function coefficient presheaf. It is the identical presheaf
   on U; lem-cbc-sieve-slice-sheafification carries its sheafification unit to the slice.
   Thus the ring comparison fixes constants and is the canonical coefficient comparison
   of prop-weil-pbc-proetale-constant-ring-map. Transported actions are those in
   prop-weil-pbc-proetale-constant-exact, without permuting any noncommuting factors.
3. The Hom transpose sends phi:N|U -> G to phi at V times_T U after restriction from V.
   Conversely evaluate a map N -> j_*G on W/U and identify W times_T U with W.
   Naturality proves these are inverse and linear. The original Kan adjunction unit is
   the coprojection indexed by (V,id); under the initial-pair comparison it is exactly
   restriction along the first projection. This gives both displayed unit normalizations.
4. Apply lem-pur-kinjective-restrict-localized to A_T. Transport over the site and ring
   identifications to obtain K-injectivity of the actual pullback. Exactness from
   prop-weil-pbc-proetale-constant-exact gives its termwise descent through Q.
5. The ring-sheaf Grothendieck theorem lem-weil-pbc-ring-sheaves-grothendieck and
   lem-sfb-grothendieck-k-injective give resolutions for every complex. Termwise j_* is
   additive and preserves the shift and cone matrices. Apply
   lem-weil-pbc-kinjective-total-derived to its homotopy functor followed by Q_T.
   Precomposing with the homotopy quotient gives the displayed right-derived comparison
   on complexes and its universal property. It is invertible on the restricted I.
6. Exact left adjoint j^* makes j_* preserve K-injectives by
   lem-weil-pbc-right-adjoint-preserves-kinjective. The sheaf Hom adjunction descends to
   chain maps and homotopies, since its component formulas commute with differentials
   and addition. Apply lem-weil-pbc-kinjective-hom-derived on both sides, then beta, to
   obtain the derived adjunction from the specified ordinary adjunction.
7. For J = j^*I, the identity transposes to the ordinary unit. Consequently its derived
   transpose is Q_T(eta_I) followed by beta_J. The factor alpha identifies Q_U(j^*I)
   with j^*(Q_TI). This is the final equation and gives exactly the asserted unit. -/
theorem finiteCoefficientOpenDerivedImage {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (A : Type (u + 1))
    [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A] :
    ∃ d : (finiteCoefficientRingSheaf U A).obj ≅
        (Scheme.proEtaleOpenComposition j).op ⋙ (finiteCoefficientRingSheaf T A).obj,
      (∀ (W : U.ProEt) (a : A),
        (d.hom.app (op W)) ((finiteCoefficientScalarMap U A).app (op W) a) =
          (finiteCoefficientScalarMap T A).app
            (op ((Scheme.proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (N : FiniteCoefficientModules T A) (W : U.ProEt),
          ((finiteCoefficientModulePullback j A).obj N).val.obj (op W) ≃+
            N.val.obj (op ((Scheme.proEtaleOpenComposition j).obj W)),
        (∀ (N : FiniteCoefficientModules T A) (W : U.ProEt)
          (r : (finiteCoefficientRingSheaf U A).obj.obj (op W))
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W (r • m) = (d.hom.app (op W) r) • rho N W m) ∧
        (∀ (N : FiniteCoefficientModules T A) (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W' (((finiteCoefficientModulePullback j A).obj N).val.map b.op m) =
            N.val.map ((Scheme.proEtaleOpenComposition j).map b).op (rho N W m)) ∧
        (∀ (N N' : FiniteCoefficientModules T A) (h : N ⟶ N') (W : U.ProEt)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N' W (((finiteCoefficientModulePullback j A).map h).val.app (op W) m) =
            h.val.app (op ((Scheme.proEtaleOpenComposition j).obj W)) (rho N W m)) ∧
        ∃ (_ : (finiteCoefficientOpenDirectImage j A).Additive)
          (adj : finiteCoefficientModulePullback j A ⊣ finiteCoefficientOpenDirectImage j A),
          (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
            (adj.unit.app N).val.app (op V) m = finiteCoefficientOpenUnitSection j A N V m) ∧
          (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
            rho N ((Scheme.proEtaleBaseChange j).obj V)
                ((adj.unit.app N).val.app (op V) m) =
              N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m) ∧
          ∃ (L : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory U A)
            (alpha : DerivedCategory.Q ⋙ L ≅
              (finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ) ⋙
                DerivedCategory.Q)
            (R : FiniteCoefficientDerivedCategory U A ⥤ FiniteCoefficientDerivedCategory T A)
            (beta : (finiteCoefficientOpenDirectImage j A).mapHomologicalComplex (.up ℤ) ⋙
                DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R),
            R.IsRightDerivedFunctor beta
                (HomologicalComplex.quasiIso (FiniteCoefficientModules U A) (.up ℤ)) ∧
            ∃ derivedAdj : L ⊣ R,
              ∀ (I : CochainComplex (FiniteCoefficientModules T A) ℤ) [I.IsKInjective],
                CochainComplex.IsKInjective
                    (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj
                      I) ∧
                IsIso (beta.app
                  (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj
                    I)) ∧
                derivedAdj.unit.app (DerivedCategory.Q.obj I) ≫ R.map (alpha.hom.app I) =
                  DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
                    beta.app
                      (((finiteCoefficientModulePullback j A).mapHomologicalComplex (.up ℤ)).obj
                        I) := by
  sorry

end AlgebraicGeometry.ProEtale
