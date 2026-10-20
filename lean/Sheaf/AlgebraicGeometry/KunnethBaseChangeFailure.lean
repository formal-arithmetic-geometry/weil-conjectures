/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
import Sheaf.AlgebraicGeometry.KunnethUnboundedBridges
import Sheaf.AlgebraicGeometry.KunnethFunctionFieldDescent

/-!
# Failure of base change over an algebraically closed function field

Source: Stacks Project, Lemma 59.90.3, Tag 0F1D; blueprint sec-smooth-purity,
sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0f1d).

The generic field is the function field itself. The second Cartesian square therefore
uses the canonical generic-point morphism, without choosing a further field extension.
Higher direct image is computed on abelian sheaves, using a sheaf in degree zero and
the bounded-below right derived direct image. The coefficient lift only implements the
small-site universe convention.
-/

@[expose] public section

universe u

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Failure in the first positive degree of cumulative universal base change is witnessed
on the generic fibre over an affine integral normal base with algebraically closed
function field, by a nonzero cyclic abelian higher direct image.
Source: Stacks Project, Lemma 59.90.3, Tag 0F1D; blueprint sec-smooth-purity,
sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0f1d).

Proof:
1. The cumulative hypothesis gives universal base change in every nonnegative degree
   below `q`. If the degree-`q` universal predicate also held, all integer degrees at
   most `q` would satisfy the cumulative condition: lower degrees come from the
   hypothesis, including negative degrees. Thus degree `q` fails universally
   (`def-kun-bc-property`, `sbc-def-base-change-property`).
2. Apply `sbc-lem-bc-universal-test` to obtain the two Cartesian squares over an affine
   integral normal base `S'`, with algebraically closed function field `L`, an
   algebraically closed extension `Ω/L`, and nonzero degree-`q` higher direct image of
   a constant cyclic sheaf of order `d` dividing `n`. Since `n` is positive, `d` is
   nonzero; replace an integer divisor by its absolute value without changing its
   cyclic group. Form the fibre `Y_L` over `L`. Fibre-product universality identifies
   the old fibre with `Y_L ×_L Ω` (`def-pc-fibre-product`). Invertibility of `n`
   implies invertibility, hence nonvanishing, of `d` in `L`.
3. On an etale object `V` over the new total space, form the cohomology presheaves of
   `V ×_{S'} Spec L` and `V ×_{S'} Spec Ω` with constant `ZMod d` coefficients.
   `lem-weil-pbc-higher-direct-image-sheafified-presheaf` identifies their
   sheafifications with the two higher direct images. The exact coefficient and site
   identifications use `lem-weil-pbc-cohomology-over-object-localization`,
   `lem-weil-pbc-etale-composition-cancellation`,
   `lem-weil-pbc-etale-inverse-image-restriction`, and
   `lemma-constructible-pullback-constant`.
4. Cohomological pullback forms a morphism between these presheaves by
   `lem-weil-pbc-cohomology-pullback-functorial` and
   `lem-weil-pbc-constant-pullback-composition-coherence`. For affine `V`, the schemes
   `V` and `S'` are qcqs (`lem-weil-pbc-affine-scheme-qcqs`), as are `V → S'` and its
   base change to `L` (`lem-weil-pbc-qcqs-morphism-permanence`). Hence the comparison
   is bijective by `lem-sc-qcqs-algclosed-extension-invariance`.
5. Cover every etale object by affine opens (`lem-weil-pbc-affine-opens-basis`,
   `lem-weil-pbc-etale-composition-cancellation`, `def-weil-pbc-etale-site`). The
   comparison is locally injective and locally surjective. By
   `lem-weil-pbc-site-sheafification-iso-locally-bijective` its sheafification is an
   isomorphism. The higher direct image over `L` is consequently nonzero since the
   one over `Ω` is nonzero. Keep the first square and take the second square to be
   the fibre over `L` itself, with its canonical generic-point map.
Normality is integral closedness of all stalks; integrality already makes them domains. -/
theorem exists_kunnethBaseChangeFailure_functionField
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(S, ⊤))) (q : ℕ) (hq : 1 ≤ q)
    (hprev : UnboundedCumulativeUniversalBaseChangeProperty f n hn (q - 1))
    (hfail : ¬ UnboundedCumulativeUniversalBaseChangeProperty f n hn q) :
    ∃ (S' X' : Scheme.{u}) (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S')
      (_ : ChosenCartesianSquare b f' f a) (_ : IsAffine S') (_ : IsIntegral S')
      (_ : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
      (_ : IsAlgClosed S'.functionField) (Y : Scheme.{u})
      (e : Y ⟶ Spec S'.functionField) (h : Y ⟶ X')
      (_ : ChosenCartesianSquare h e f' (S'.fromSpecStalk (genericPoint S'))) (d : ℕ),
      d ∣ n ∧ ¬ IsZero
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))) := by
  obtain ⟨hprev', hfail'⟩ := cumulative_and_not_universal_of_unbounded f n hn hinv q hprev hfail
  obtain ⟨S', X', a, b, f', hsquare, hAff, hInt, hNorm, hAlg, K, hKField,
      hKAlg, i, Y, e, h, hcart, d, hd, hne⟩ :=
    exists_universalBaseChangeFailure_cyclic_datum f n hn hinv q hq hprev' hfail'
  letI : Field K := hKField
  letI : IsAlgClosed K := hKAlg
  obtain ⟨Y₀, e₀, h₀, hcart₀, hne₀⟩ :=
    exists_functionField_descent_of_algClosedWitness (f' := f') hAff hInt hNorm hAlg i e h hcart
      q n d hn hd hne
  exact ⟨S', X', a, b, f', hsquare, hAff, hInt, hNorm, hAlg, Y₀, e₀, h₀, hcart₀, d,
    hd, hne₀⟩

end AlgebraicGeometry.Etale
