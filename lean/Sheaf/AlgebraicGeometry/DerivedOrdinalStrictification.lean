/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.SetTheory.Ordinal.Basic
public import Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion
import Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized

/-! # Strict chain representatives for ordinal derived descent data

Source: literature/stacks-project/cohomology.tex, Tag 0D6B
(cohomology-lemma-glueing-increasing-union)
(blueprint: lem-trf-derived-ordinal-strictification).

The localized open-site module category is canonically equivalent to modules on the open
subscheme by `Scheme.Modules.overEquiv`. The comparison maps below are the shared
sectionwise identity comparisons, at the complex and derived levels. In particular the
composition equation is an equality of chain maps, rather than a homotopy relation.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- Strictly composable quasi-isomorphic chain representatives for a continuous ordinal
family of compatible derived objects.
Source: Stacks Project, Cohomology, Tag 0D6B
(blueprint: lem-trf-derived-ordinal-strictification).

Proof:
1. Set a_beta_alpha to e_beta followed by inverse r_beta_alpha and inverse restricted
   e_alpha. The cocycle for r gives the composition law for a. Recurse on alpha,
   keeping all earlier choices. Restriction preserves K-injectivity by
   `lem-pur-kinjective-restrict-localized`. The localization of
   `def-weil-abstract-derived-category` reflects quasi-isomorphisms, since every
   cohomology functor factors through it.
2. At a successor alpha = delta + 1, `lem-weil-pbc-kinjective-hom-derived` lifts
   a_delta_alpha to a chain map into the restricted I_alpha. Define the earlier
   new maps by restriction and composition. The old strict equations and the
   cocycle give strict composition and the prescribed derived classes.
3. At a nonzero limit alpha, continuity covers W_alpha by the earlier opens.
   Apply `lem-trf-derived-strict-open-colimit` to obtain C and strictly compatible
   quasi-isomorphisms s_beta : I_beta to C restricted to W_beta.
4. The derived maps a_beta_alpha composed with inverse Q(s_beta) are compatible.
   Repeated opens give the same map by the cocycle. The distinct earlier opens
   cover W_alpha and refine intersections, which are the smaller member. Both
   QC and QI_alpha are locally identified with K_beta, so the negative cross
   Hom groups, in both directions and for the two endomorphism pairs, vanish.
5. Apply `lem-trf-derived-basis-local-hom-glue` to this family and its inverses.
   The injective part for both endomorphism pairs shows the glued maps are
   inverse. Thus obtain an isomorphism u : QC to QI_alpha with the required
   restrictions; no finite subcover is needed (Stacks 0D68).
6. Use `lem-weil-pbc-kinjective-hom-derived` to represent u by t : C to I_alpha.
   Put f_beta_alpha = s_beta followed by restricted t. The strict equations for
   s_beta give strict composition, and Q(t) = u gives the required derived class
   and hence quasi-isomorphy. This corrects the reversed comparison in 0D6B.
7. Set-sized transfinite recursion supplies all maps without changing the fixed
   I_alpha or e_alpha. For lambda zero or one there are no pairs. Empty and
   repeated opens satisfy the same equations. Only individual limit opens need
   covering families, so there is no covering hypothesis on the ambient X.
-/
theorem derived_ordinal_strictification
    (X : Scheme.{u}) (lambda : Ordinal.{v})
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (W : lambda.ToType → X.Opens) (hincreasing : Monotone W)
    (hcontinuous : ∀ alpha : lambda.ToType, Order.IsSuccPrelimit alpha →
      W alpha = ⨆ beta : {beta : lambda.ToType // beta < alpha}, W beta.val)
    (K : ∀ alpha : lambda.ToType,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W alpha))))
    (hnegative : ∀ (alpha : lambda.ToType) (i : ℤ), i < 0 →
      Subsingleton (K alpha ⟶ (K alpha)⟦i⟧))
    (I : ∀ alpha : lambda.ToType,
      CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W alpha))) ℤ)
    (hI : ∀ alpha : lambda.ToType, (I alpha).IsKInjective)
    (e : ∀ alpha : lambda.ToType,
      DerivedCategory.Q.obj (I alpha) ≅ K alpha)
    (r : ∀ (beta alpha : lambda.ToType) (h : beta < alpha),
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hincreasing h.le))).mapDerivedCategory.obj (K alpha) ≅ K beta)
    (hcocycle : ∀ (gamma beta alpha : lambda.ToType)
        (hgb : gamma < beta) (hba : beta < alpha),
      (derivedModuleOpenMapCompIso X
        (homOfLE (hincreasing hgb.le)) (homOfLE (hincreasing hba.le))).inv.app (K alpha) ≫
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE (hincreasing hgb.le))).mapDerivedCategory.map
        (r beta alpha hba).hom ≫
        (r gamma beta hgb).hom =
      (r gamma alpha (hgb.trans hba)).hom) :
    ∃ (f : ∀ (beta alpha : lambda.ToType) (h : beta < alpha),
        I beta ⟶
          ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (hincreasing h.le))).mapHomologicalComplex (.up ℤ)).obj (I alpha)),
      (∀ (beta alpha : lambda.ToType) (h : beta < alpha), QuasiIso (f beta alpha h)) ∧
      (∀ (gamma beta alpha : lambda.ToType) (hgb : gamma < beta) (hba : beta < alpha),
        f gamma beta hgb ≫
          ((SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (hincreasing hgb.le))).mapHomologicalComplex (.up ℤ)).map
            (f beta alpha hba) ≫
          (Functor.mapHomologicalComplexCompIso
            (moduleOpenMapCompIso X
              (homOfLE (hincreasing hgb.le)) (homOfLE (hincreasing hba.le)))
            (.up ℤ)).hom.app (I alpha) = f gamma alpha (hgb.trans hba)) ∧
      (∀ (beta alpha : lambda.ToType) (h : beta < alpha),
        DerivedCategory.Q.map (f beta alpha h) =
          (e beta).hom ≫ (r beta alpha h).inv ≫
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (hincreasing h.le))).mapDerivedCategory.map (e alpha).inv ≫
          (Functor.mapDerivedCategoryFactors
            (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE (hincreasing h.le)))).hom.app (I alpha)) := by
  sorry

end AlgebraicGeometry
