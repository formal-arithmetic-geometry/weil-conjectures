/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Topology.Connected.Separation
import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Separable
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Compactification.OnePoint.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement

/-!
# Finite coefficient comparison for smooth exceptional inverse image

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md, det-sp-reduction-exceptional;
proof: sk-lem-sp-reduction-exceptional.proof.md, Existence, uniqueness, naturality;
Locality; Charts (blueprint: det-sp-reduction-exceptional).

This statement retains the canonical compact-support mate and its normalized chart formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Exceptional inverse image of a smooth morphism commutes with extension of finite coefficients.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/`
`sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/`
`sk-lem-sp-reduction-exceptional.md`, det-sp-reduction-exceptional; standing
finite-or-algebraically-closed field convention (blueprint: det-sp-reduction-exceptional).

Proof (deferred to stage 3; the node's six steps, from
`sk-lem-sp-reduction-exceptional.proof.md`):

1. (Existence, uniqueness, naturality.) Put $T=(-)_B$, $F_R=Rf_{!,R}$, $G_R=f_R^!$. Scalar
preservation and the restricted adjunction make $\tau_K=T(\epsilon_{A,K})b(G_AK)^{-1}$ well
typed. Define $c_K$ as its unique $B$-transpose. This is the required counit equation.
Naturality of $b,\epsilon_A$ gives $T(u)\tau_K=\tau_LF_BTG_A(u)$; injectivity and naturality of
transposition prove naturality of $c$.
Uses: det-sp-scalar-extension-functor, sk-prop-sf-rf-shriek-preservation,
det-sp-reduction-direct-image, def-weil-pbc-adjunction-mate.

2. (Locality and Charts.) Take the admissible affine coordinate cover $j:U\hookrightarrow X$,
$g=fj=p_de$. Its schemes and maps meet the finite-ring chart hypotheses. The chart-domain
theorem supplies etale origins, finite-Tor site equivalences and preservation by compact
support, pullback, Tate tensor, shifts and scalar extension.
Uses: lem-sp-smooth-admissible-coordinate-cover, lem-sp-etale-ctf-chart-domain.

3. (Charts: Kummer, diagonal, splitting and iterated integration.) The projective-line
splitting theorem preserves the unit, Kummer and diagonal classes and trace. The actual
projective-line counit has its scalar equation; the ordered affine-space counit theorem gives
$\epsilon_{d,B}F_{d,B}(a_d)\beta_d=T\epsilon_{d,A}$, including $d=0$, for the specified
compactification.
Uses: lem-sp-finite-p1-coefficient-splitting, lem-sp-p1-counit-scalar,
lem-sp-affine-counit-scalar.

4. (Charts: summation and composition with affine integration.) The etale-sum theorem gives the
counit scalar equation and graph-normalized coefficient square for $e$. Paste its inverse
coefficient square with that of $p_d$ using mate-pasting (2) and the composite counit.
Compact-support scalar composition and refinement identify the left square with $\beta_g$;
the ordered right normal form identifies its mate with canonical $a_g$. Thus
$\epsilon_{g,B}F_{g,B}(a_g)\beta_g=T\epsilon_{g,A}$.
Uses: lem-sp-finite-etale-sum-coefficient-counit, lem-weil-pbc-mate-pasting,
def-weil-pbc-composite-adjunction, lem-pur-etale-compact-scalar-coherence,
lem-amb-etale-compact-comparisons, lem-sp-finite-affine-right-scalar-normal-form.

5. (Charts: counit transport and canonical reassociation.) Transfer the chart adjunction
counit-preservingly through $\nu^*$: its counit is $\nu^*(\epsilon^{et})c_R^{-1}$. Substitute
the finite site/coefficient square in Step 4. It gives
$\epsilon_{g,B}F_{g,B}(\rho_K)=T(\epsilon_{g,A})b_g^{-1}$. The right-normal-form site equation
and chart reassociation identify the transported $a_g$ with $\rho_K$. Uniqueness of the
transpose gives $c_g(K)=\rho_K$.
Uses: det-sp-et-proet-adjunction-transfer, lem-sp-finite-ctf-site-coefficient-square,
lem-sp-finite-affine-right-scalar-normal-form,
lem-sp-reduction-exceptional-chart-scalar-reassociation, def-weil-pbc-adjunction-mate.

6. (Locality and Charts conclusion.) Open locality gives $c_g=j_B^*c_f\circ a_j$ under the
counit-preserving chart identification. Step 5 therefore gives exactly the asserted canonical
chart map for every restriction of $c_f$. It is invertible, so covering-family conservativity
makes $c_f$ invertible. This includes the empty scheme and its empty cover.
Uses: lem-sp-finite-exceptional-coefficient-open-locality, lem-cbc-proetale-stalk-conservative.
-/
theorem reductionExceptional_coefficient_extension
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (hchar : ringChar k ≠ ℓ)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B) :
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
        spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
      (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
        spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
      (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
        spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj)),
      ∃ (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
        (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
        (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
        (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB),
        ∃ (RA : ReductionExceptionalRealization A j p hFA GA adjA)
          (RB : ReductionExceptionalRealization B j p hFB GB adjB),
        ∃ hb : ∀ K : spFiniteConstructibleTorCategory Y A,
          IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj),
        ∃! c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB,
          (∀ K : spFiniteConstructibleTorCategory Y A,
            (reductionCompactSupport B j p).map (c.app K).hom ≫
                (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
              @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
                  (hb K) ≫
                (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) ∧
          (∀ K : spFiniteConstructibleTorCategory Y A, IsIso (c.app K)) ∧
          ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB
            RA RB c := by
  sorry

end AlgebraicGeometry.ProEtale
