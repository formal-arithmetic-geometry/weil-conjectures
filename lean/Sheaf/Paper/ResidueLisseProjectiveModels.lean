/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.IntegralDerivedReduction
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Cover.Open

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.Paper.CompleteResidueCohomologyBounds
import Sheaf.Paper.DerivedNakayamaFirstReduction
import Sheaf.SixFunctors.ProEtale.DerivedCompletion

/-!
# Projective models from lisse residue cohomology

Source: Stacks Project, proetale.tex, Tag 09C3 (blueprint:
lem-fix-residue-lisse-projective-models).

The conclusion records a finite disjoint open cover and, on every member, a bounded
complex whose terms split off finite sums of the completed coefficient sheaf.  The
differentials are unrestricted sheaf-linear maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/- The finite family is indexed by `Fin n`; `n = 0` therefore covers the empty
scheme, while the pairwise disjointness condition retains the stated clopen case. -/
/-- A complete integral complex with bounded finite locally constant residue cohomology
and finite residue Tor amplitude has bounded finite-projective sheaf models on a finite
clopen partition. Differentials are arbitrary maps over the completed ring sheaf.

Source: Stacks Project, proetale.tex, Tag 09C3, with Lambda = O_E and I = (varpi);
algebraization.tex, Tag 099I identifies the complete coefficient categories
(blueprint: lem-fix-residue-lisse-projective-models).

Proof plan, following the eight steps of the node:
1. The extension-integers DVR theorem makes O_E Noetherian. Use
   lem-weil-pbc-completed-constant-sheaf-reduction and
   lem-weil-pbc-constant-module-section-properties to obtain the free two-term
   quotient resolutions. They are K-flat by lem-pc-bounded-above-flat-kflat-site.
   The quotient tower is its derived limit by
   lem-weil-proetale-surjective-tower-derived-limit. Thus finite free sheaves and
   their shifts are complete. Use det-prop-integral-criterion-constant-coefficients
   and sk-def-pe-derived-completion to identify the completeness convention, and
   det-pe-derived-nakayama-first-reduction for cones and residue detection.
2. Trivialize the finitely many residue cohomology sheaves on a common pro-etale
   cover, using det-pe-topos-functoriality-site. By def-weil-pbc-proetale-covering,
   take finitely many affine covering members and their scheme coproduct using
   lem-weil-pbc-scheme-coproduct-family. Weak etaleness follows from
   sk-lem-pe-weakly-etale-stability, lem-weil-pbc-open-immersion-etale and
   det-pe-morphisms-etale-comparison. By lem-weil-pbc-proetale-subcanonical this
   cover gives an epimorphism of representables. Weak contractibility splits it.
   Pull back the coproduct components along the section to get a finite clopen
   partition on which every residue cohomology sheaf is constant finite-dimensional.
3. By lem-weil-proetale-weakly-etale-localization, restriction to a clopen member
   is site localization. The disjoint-complement product description of sheaves
   preserves limits, reductions and their Roos triangles. It preserves completeness
   and identifies the restricted completion with B_U. Extending by the terminal
   sheaf on the complement proves weak contractibility on U. Evaluation is exact,
   so Hom(B_U,F) = F(U) makes finite free B_U-sheaves projective.
4. Induct on the residue interval length. Use lem-sf-complete-residue-cohomology-bounds
   for integral cohomological bounds. Lift residue bases to cycles by exact
   evaluation, obtaining a zero-differential finite free residue model.
   By lem-pc-ring-derived-map-representative, bounded projective complexes compute
   derived maps; in particular maps from shifted free sheaves are cohomology sections.
5. The quotient resolution from step 1, computed using lem-pc-kflat-resolution and
   lem-pc-bounded-above-flat-kflat-site, gives the uniformizer triangle. By
   lem-sf-derived-homology-long-exact and the top bound, lift the top residue basis
   to integral cohomology and then cycles, giving a map B_U^r[-b] to K. Its reduction
   is the inclusion of the top summand in the split residue model of step 4.
6. Its cone L is complete by det-pe-derived-nakayama-first-reduction. Reduction is
   triangulated by lem-pur-derived-change-of-rings. The residue cone is the lower
   degree split model plus a contractible identity complex, so its amplitude drops
   to [a,b-1], using lem-pc-bounded-above-flat-kflat-site for the tensor computation.
   If a=b, derived Nakayama makes L zero; the one-term free model suffices.
7. Otherwise induction gives a bounded free model Q of L. Represent its connecting
   map to B_U^r[-b+1] by lem-pc-ring-derived-map-representative. Its shifted cone
   has terms Q below b and B_U^r in degree b, with the sheaf-linear last differential
   satisfying the chain equation. Cone triangles in def-weil-abstract-derived-category
   identify it with K on this member.
8. Apply this construction on every partition member. The finite free terms split
   off themselves, so give the asserted direct summands. Nothing makes the sheaf
   differentials constant. For the empty scheme use the empty partition; for zero
   residue use derived Nakayama and the zero complex. -/
theorem residue_lisse_projective_models
    (S : Scheme.{u}) (hS : IsAffine S)
    (hweak : (Scheme.ProEt.topology S).IsWeaklyContractible.{u + 1}
      (Scheme.ProEt.mk (𝟙 S)))
    (K : DerivedCategory (integralTowerModules.{u, u} l E S))
    (hcomplete : IsDerivedCompleteUnrestricted l E S K)
    (hresidue : intrinsicFiniteTorsionConstructible l E 1 (by omega) S
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K))
    (hlisse : ∀ q : ℤ, IsLocallyConstantProEtaleModuleSheaf S
      (Padic.coefficientExtensionRing l E 1)
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S
          (Padic.coefficientExtensionRing l E 1))) q).obj
        ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)))
    (hTor : HasFiniteProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing l E 1)
      ((scalarReductionDerivedExtension.{u, u} l E S 0).obj K)) :
    ∃ (n : ℕ) (U : Fin n → S.Opens),
      (⨆ i, U i) = ⊤ ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      ∀ i : Fin n,
        ∃ (P : CochainComplex (integralTowerModules.{u, u} l E (U i).toScheme) ℤ)
          (a b : ℤ),
          a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ r : ℤ, ∃ (N : ℕ)
            (ι : P.X r ⟶ ∏ᶜ fun _ : Fin N ↦
              SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
            (ρ : (∏ᶜ fun _ : Fin N ↦
              SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (U i).toScheme))
              ⟶ P.X r),
            ι ≫ ρ = 𝟙 _) ∧
          Nonempty
            ((integralDerivedPullback l E (U i).ι).obj K ≅
              DerivedCategory.Q.obj P) := by
  sorry

end WeilConjectures
