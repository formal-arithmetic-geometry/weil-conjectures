/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian

/-!
# Proper direct image with finite coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-finite.md
(blueprint: det-thm-sfb-proper-base-change-finite).

All three clauses use the recorded internal-module Dctf and ordinary uncompleted
unbounded derived operations. The exchange is the mate of the composition comparison;
the projection is the right-adjoint projection map of the canonical derived tensor comparison.

## Main definitions

* `finiteProperCoefficientRing`: the sheafified constant coefficient ring.
* `finiteProperAmbientExchange`: the canonical ambient exchange mate.

## Main statements

* `finiteProperBaseChange`: preservation of Dctf, base change, and the projection formula.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The sheafified constant commutative coefficient ring on the profinite point.
This bundles the existing `Sheaf.sheafifyRingPresheaf` construction, so the finite ring
may have the same arbitrary universe as the schemes, with no topology parameters.
Source: blueprint sk-thm-sfb-proper-base-change-finite, finite discrete coefficients,
and Bhatt--Scholze Section 5.3 (blueprint: det-thm-sfb-proper-base-change-finite). -/
noncomputable def finiteProperCoefficientRing (A : Type u) [CommRing A] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  letI : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
  let P : Profinite.{u}ᵒᵖ ⥤ RingCat.{u + 1} :=
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A))
  letI := P.isCommMonObj_compForget₂
    (fun _ a b ↦ @mul_comm (ULift.{u + 1, u} A) _ a b)
  exact
    { X := Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
        (coherentTopology Profinite.{u}) P }

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option maxHeartbeats 800000 in
-- Elaborating the two composed derived pullbacks unfolds their module scalar transports.
/-- The canonical ambient exchange for internal condensed-coefficient modules.
Source: blueprint sk-thm-sfb-proper-base-change-finite, clause (2), and the
unit/square/counit construction in sk-def-sfb-base-change-morphism
(blueprint: det-thm-sfb-proper-base-change-finite). -/
noncomputable def finiteProperAmbientExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (((leftDerivedUpperStarComp Λ p' g).symm ≪≫
      eqToIso (congrArg (fun f ↦ (upperStar Λ f).leftDerivedFunctor) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ g' p).hom)

/-- Proper direct image preserves Dctf, and its canonical exchange and projection arrows
are invertible, in the ordinary unbounded derived category of internal modules.
Source: blueprint main-20261015, sk-thm-sfb-proper-base-change-finite, clauses (1)--(3)
(blueprint: det-thm-sfb-proper-base-change-finite).

Proof:
1. The coefficients are the sheafified constant ring on the profinite point. For a
finite discrete ring this is its continuous-function condensed ring by the finite-discrete
condensed-ring identification; the scheme-ring identification gives constant coefficients
after pullback. Finite rings in any universe admit finite small representatives, so the
same identification applies up to ring isomorphism, without a universe restriction. A is
Noetherian because every ideal is finite and generated by its elements. The finite-Tor
comparison for Noetherian coefficients gives bounded constructible etale antecedents K0,
M0 with the same Tor intervals. Constructible pro-etale cohomology sheaves are classical
by sk-thm-pe-constructible-comparison, and their abelian sheaves are killed by the
annihilating power of ell.
2. The standing schemes are qcqs. The finite-type fibre-dimension bound gives e bounding
all scheme-theoretic fibres. Properness is stable under base change, and dimension is
unchanged by a field extension (lem-kun-dimension-extension), so e also bounds every
geometric fibre, including empty fibres.
3. A separably closed point has torsion cohomological dimension zero. The finite-type
cohomological-dimension theorem gives the uniform geometric-fibre bound c = 2e. Empty
fibres have zero cohomology, so the same nonnegative bound works there.
4. Enlarge the annihilating exponent to be positive, also for the zero ring. For an
ordered Tor interval [a,b] of K0, det-ctf-finite-proper-tor applies over the same field:
its ordinary constant coefficients, proper k-morphism and sectionwise ell-power-torsion
geometric-fibre vanishing hypotheses are exactly those just checked. It gives bounded
constructibility and Tor interval [a,b+c] for the etale direct image. The qcqs direct-image
comparison and finite-Tor comparison transfer these conclusions to the pro-etale site.
5. The bounded-below classical torsion proper-base-change theorem applies to K and any
cartesian square. Its canonical exchange is precisely the mate of the pullback-square
comparison, giving clause (2) without properness, smoothness or flatness of g.
6. Choose bounded flat models P,Q in ordered Tor intervals for K0,M0 by
lem-sf-etale-flat-model. They are K-flat by lem-pc-bounded-above-flat-kflat-site. Constant
coefficient pullback is exact and preserves flat K-flat models, by the ringed-topoi tensor
pullback theorem. The total tensor P tensor p*Q is zero outside the sum interval, so the
input K0 tensor^L p*M0 for the next comparison is bounded below.
7. The torsion-ring etale projection formula (Stacks 0F0G, lem-kun-0f0g) makes the canonical
counit-mate projection arrow invertible, without a regularity assumption on A.
8. Exact monoidal etale-to-pro-etale comparison and qcqs direct-image comparison transport
this arrow. Transpose it under pullback/direct-image adjunction. Compatibility of the
comparison with units and counits identifies its transpose with the canonical tensor
comparison followed by counit tensor identity. On flat representatives the tensor
comparisons have the same balanced pure-tensor formula, hence the same signed total map.
The adjunction bijection therefore identifies the transported arrow with the published
right-adjoint projection map. Functors preserve inverse arrows, proving clause (3).
-/
theorem finiteProperBaseChange
    (A : Type u) [CommRing A] [Finite A]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hA : ∃ r : ℕ, (ℓ ^ r : ℕ) • (1 : A) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : X ⟶ Y) [IsProper p.left] :
    (∀ K : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X X.left,
      (constantModelBoundedConstructible (finiteProperCoefficientRing A).X Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
          ((lowerStar (finiteProperCoefficientRing A).X p.left).rightDerivedFunctor.obj K.obj)) ∧
    (∀ (X' Y' : Scheme.{u}) (g : Y' ⟶ Y.left) (p' : X' ⟶ Y') (g' : X' ⟶ X.left)
      (sq : ChosenCartesianSquare g' p' p.left g)
      (K : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X X.left),
      IsIso ((finiteProperAmbientExchange (finiteProperCoefficientRing A).X
        sq.toCommSq).app K.obj)) ∧
    (∀ (K : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X X.left)
      (M : ConstantModelConstructibleFiniteTor (finiteProperCoefficientRing A).X Y.left),
      IsIso ((((derivedUpperStarLowerStarAdjunction (finiteProperCoefficientRing A).X
        p.left).rightAdjointProjectionMap
          (leftDerivedUpperStarTensor (finiteProperCoefficientRing A).X p.left)).app K.obj).app
            M.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
