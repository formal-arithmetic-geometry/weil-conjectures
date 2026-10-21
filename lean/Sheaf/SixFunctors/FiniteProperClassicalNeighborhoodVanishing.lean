/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap
import Sheaf.AlgebraicGeometry.ProperHeartContinuitySections
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties

/-!
# Classical cohomology on proper weakly contractible neighborhoods

Source: blueprint main-20261015, sec-six-functors-basics,
`sk-prop-ctf-finite-proper-localizing.proof.md`, "Etale statements" and "Transfer";
Stacks Project, Tag 095U
(blueprint: lem-sfb-finite-proper-classical-neighborhood-vanishing).

We use the existing fixed-coefficient module-sheaf presentation of ordinary modules over
constant coefficients. The exact realization `finiteCoefficientRealization` identifies it
with the coefficient-ring-sheaf category of `def-weil-pbc-proetale-modules`.
Both derived functors below are total unbounded K-injective right derived functors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Every classical module sheaf on the proper neighborhood itself has zero higher
proper direct image and derived global sections in degrees greater than `2 * e`.
Classicality is the essential-image condition for the recorded comparison inverse image.

Source: blueprint main-20261015, `sk-prop-ctf-finite-proper-localizing.proof.md`,
"Etale statements" and "Transfer"; Stacks Project, Tags 095U, 03FD and 0946
(blueprint: lem-sfb-finite-proper-classical-neighborhood-vanishing).

Proof plan:
1. Base change preserves properness (lem-pc-proper-base-change). Apply the universal
   fibre bound to `V.hom`. Properness gives finite type, quasi-compactness and separatedness,
   hence quasi-separatedness (lem-pc-separated-quasi-separated).
2. The finite-discrete coefficient identifications
   lem-weil-pbc-finite-discrete-condensed-ring-constant and
   lem-weil-pbc-finite-discrete-scheme-ring-constant identify the coefficient rings with
   constant rings. Use det-pe-classical-sheaves-modules to choose an etale sheaf `F` on
   `X ×_Y V` whose comparison pullback is `H`. The additive order of `1` in the finite
   ring annihilates all its sections. Thus the underlying abelian sheaf is torsion;
   for the zero ring use the annihilator `1`. No descent from `X` is used.
3. Apply lem-kun-proper-torsion-cd-bound to this underlying torsion sheaf. The comparison
   lem-sbc-higher-direct-image-forget-comparison and faithful coefficient forgetting
   give the same etale module bound. Bounded-below injective resolutions compute total
   K-injective derivation on `F[0]` (lem-sp-kinjective-computes).
4. The canonical mate of def-sfb-unbounded-direct-image-mate is invertible on `F[0]`
   by lem-sfb-unbounded-direct-image-bounded-below. Exact comparison inverse image
   commutes with cohomology, giving the asserted proper direct-image vanishing.
5. A bounded-below injective resolution of `H` computes both total functors. Termwise
   sections of its direct image on `V` equal its global sections on `X ×_Y V`
   (def-weil-pbc-proetale-operations). The localization
   lem-weil-proetale-weakly-etale-localization identifies `V_proet` with `Y_proet/V`.
   To transfer weak contractibility, for an epimorphism `F -> G` on that slice and a
   section `s` over its final object, form the sheaf of pairs `(a : U -> V, t in F(a))`
   with `t` lifting the restriction of `s`. Maps `a` glue by subcanonicity
   (det-pe-topos-functoriality-site), and their lifts glue by the sheaf axioms. This
   sheaf maps epimorphically onto `h_V`; weak contractibility splits it. Evaluation
   of a splitting at `id_V` lifts `s`. Hence the final object of `V_proet` is weakly
   contractible. Its module sections are exact by det-proper-heart-continuity-sections,
   so they commute with cohomology. Apply them to the vanishing from step 4. -/
theorem finiteProper_classical_neighborhood_vanishing
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞))
    (V : Y.ProEt) [IsAffine V.left]
    (_hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)
    (H : Sheaf (Scheme.ProEt.topology (pullback f V.hom)) (ModuleCat.{u + 1} A))
    (_hH : ∃ F : Sheaf (pullback f V.hom).smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f V.hom)).obj F ≅ H))
    (q : ℤ) (_hq : 2 * (e : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd f V.hom)).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) ∧
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj
      ((globalSectionsFunctor (ModuleCat.{u + 1} A) (pullback f V.hom)).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj H))) := by
  sorry

end AlgebraicGeometry.ProEtale
