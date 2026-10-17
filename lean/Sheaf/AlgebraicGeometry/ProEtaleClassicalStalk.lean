/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

/-!
# Classical pro-etale stalks

Source: Stacks Project, Tags 0991 and 0993
(blueprint: lem-cbc-proetale-classical-stalk).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The strict localization is a pro-etale neighbourhood; its canonical colimit
coprojection is an isomorphism naturally in set-valued and abelian sheaves.
The abelian stalk functor preserves finite limits and finite colimits.
Source: Stacks Project, Tags 0991 and 0993
(blueprint: lem-cbc-proetale-classical-stalk).

Proof: (1) The strict-localization map factors through any affine etale chart.
The chart ring map is ind-etale, hence weakly etale, and composition gives the
site object, using strict-henselization functoriality, the affine-chart ind-etale
lemma and ind-etale stability. (2) Pull a pointed weakly etale neighbourhood back
to the strict localization. Localize an affine chart at its marked prime.
Olivier's theorem identifies this local ring with the strictly henselian base,
giving a pointed section. (3) The section is unique: both sections factor through
the affine chart since it contains the closed point of a local spectrum, and
localization forces their ring maps to be the inverse of the same isomorphism.
Thus the strict localization is initial among pointed neighbourhoods.
(4) Its opposite is terminal, so the canonical colimit leg is an isomorphism;
restriction naturality makes this an isomorphism of functors of sheaves.
(5) Every pro-etale cover of the strict localization has a split member, by the
same local-ring argument. Local surjectivity of sheaf epimorphisms then shows
that evaluation preserves epimorphisms; sheaf limits are sectionwise.
(6) Evaluation is additive and preserves kernels and epimorphisms, hence cokernels
by image factorization, and finite colimits by finite sums and cokernels.
The natural isomorphism transfers both preservation properties to the stalk.
Dependencies: steps (1)-(3) use `lem-weil-pbc-strict-henselization-functoriality`,
`def-weil-pbc-strict-henselization-limit`,
`def-weil-pbc-strict-henselization-structural-map`,
`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`,
`lem-weil-pbc-ind-etale-stability`, `def-weil-pbc-ind-etale-algebra`,
`def-weil-pbc-proetale-site`, `def-weil-open-immersion`,
`lem-weil-pbc-open-immersion-etale`, `def-weil-pbc-site-comparison-morphism`,
`lem-weil-pbc-weakly-etale-source-locality`,
`lem-weil-pbc-localization-ring-weakly-etale`,
`thm-weil-pbc-weak-etale-strict-local`, `def-pc-fibre-product`,
and `def-weil-affine-spectrum`. Step (4) uses `def-weil-proetale-geometric-stalk`.
Step (5) also uses `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
and `lem-weil-pbc-sheafification-exact`.
Step (6) uses `def-weil-pbc-sites-and-cohomology`. -/
theorem proEtale_classical_stalk
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    ∃ (h : WeaklyEtale (strictHenselizationStructuralMap t))
      (l : Spec (.of Ω) ⟶ strictHenselizationScheme t)
      (hl : l ≫ strictHenselizationStructuralMap t = t),
      IsIso (Functor.whiskerLeft (sheafToPresheaf (ProEt.topology T) (Type (u + 1)))
        (Functor.whiskerLeft
          ((Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            (Type (u + 1))).obj (proEtaleGeometricNeighbourhoodForget t).op)
          (colim.ι (op (StructuredArrow.mk
            (Y := @ProEt.mk T _ (strictHenselizationStructuralMap t) h)
                  (Over.homMk l hl)))))) ∧
      IsIso (Functor.whiskerLeft (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1})
        (Functor.whiskerLeft
          ((Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op)
          (colim.ι (op (StructuredArrow.mk
            (Y := @ProEt.mk T _ (strictHenselizationStructuralMap t) h)
                  (Over.homMk l hl)))))) ∧
      PreservesFiniteLimits
        (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
          (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim) ∧
      PreservesFiniteColimits
        (sheafToPresheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
          (Functor.whiskeringLeft (ProEtaleGeometricNeighbourhood t)ᵒᵖ T.ProEtᵒᵖ
            AddCommGrpCat.{u + 1}).obj (proEtaleGeometricNeighbourhoodForget t).op ⋙ colim) := by
  sorry

end AlgebraicGeometry.Scheme
