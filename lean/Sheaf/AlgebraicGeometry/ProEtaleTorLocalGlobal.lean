/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.SiteTorIntervalRestriction
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Local and global finite Tor dimension on a quasi-compact pro-etale site

Source: Stacks Project, Tags 08FZ and 09C2, the uniform Tor interval in the proof of
`lemma-describe-constructible-complexes`
(blueprint: lem-sfb-proetale-tor-local-global).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The recorded exact derived slice restriction at the standard localizations used by
`HasCoefficientModelTorAmplitude`. Both rings are the actual sectionwise restrictions.
Source: Stacks Tags 03DH and 08JB (blueprint: lem-sfb-proetale-tor-local-global). -/
def coefficientModelSliceRestriction {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) (V : C) :
    ConstantCompletion.D R ⥤ ConstantCompletion.D (R.over V) :=
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (SheafOfModules.{w} ((siteModuleRings R).over V))
  ringedDerivedRestrictionSized (siteModuleRings R) V

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Global finite Tor dimension is equivalent to finite Tor dimension locally on every
object of the small pro-etale site. A covering is expressed by a presieve whose generated
sieve belongs to the topology; each of its arrows has its own ordered Tor interval.
The coefficient-sized small model retains all objects and coverings of the recorded site.
Source: Stacks Tags 08FZ and 09C2 (blueprint: lem-sfb-proetale-tor-local-global).

Proof:
1. Exact module restriction (`lem-pur-site-restriction-module-adjunction-exact`) commutes
   with cohomology (`lem-weil-pbc-exact-functor-complex-cohomology`). The localization case
   of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` identifies restricted derived
   tensor with derived tensor of restrictions, for arbitrary unbounded complexes.
2. A global interval remains an interval against every slice module by
   `lem-sf-site-tor-interval-restriction`. Use the identity covering of each object.
   The two recorded restrictions both send Q(C) to Q(C|U). The tensor models agree by
   `lem-weil-pbc-site-derived-tensor-descent`, since flat-term K-flat resolutions are K-flat.
3. Conversely, quasi-compactness gives a finite affine open covering of X. Apply the local
   hypothesis to each member. The affine-target finite refinement in `sk-def-pe-site`
   refines each resulting covering to a finite affine covering. Compose these coverings,
   using `def-weil-pbc-sites-and-cohomology`, to obtain a finite covering of X.
4. Restrict the selected intervals further along the refinement, again using
   `lem-sf-site-tor-interval-restriction`. Relocalization identifies the iterated restriction
   with restriction to the refined object (`def-pur-localized-ringed-site`). Take the minimum
   of the finitely many lower bounds and 0, and the maximum of the upper bounds and 0.
   This gives an ordered common interval and includes the empty-scheme case.
5. For every global module N and q outside this interval, step 1 identifies the restriction
   of H^q(M tensor N) with the corresponding local cohomology. Step 4 makes each zero.
6. Base change the finite cover to any test object T. Sectionwise slice restriction and
   the sheaf equalizer axiom make sections over T inject into the product of zero groups.
   Thus the global cohomology sheaf is zero. The empty cover has the same conclusion.
-/
theorem hasFiniteCoefficientProEtaleTorAmplitude_iff_locally
    (X : Scheme.{u}) [CompactSpace X]
    (A : Type (max v (u + 1))) [CommRing A]
    (M : ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A)) :
    HasFiniteCoefficientProEtaleTorAmplitude X A M ↔
      ∀ U : coefficientProEtaleSiteModel.{u, v} X,
        ∃ S : Presieve U,
          Sieve.generate S ∈ coefficientProEtaleModelTopology.{u, v} X U ∧
            ∀ (V : coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
              ∃ a b : ℤ,
                HasCoefficientModelTorAmplitude
                  ((ConstantCompletion.constant
                    (coefficientProEtaleModelTopology.{u, v} X) A).over V)
                  ((coefficientModelSliceRestriction
                    (ConstantCompletion.constant
                      (coefficientProEtaleModelTopology.{u, v} X) A) V).obj M) a b := by
  sorry

end AlgebraicGeometry.Scheme
