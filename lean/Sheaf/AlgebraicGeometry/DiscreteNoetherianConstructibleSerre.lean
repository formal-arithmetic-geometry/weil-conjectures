/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import Sheaf.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.Paper.LocalizeRingedSiteMorphism
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteMorphismComposition
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral

/-!
# Constructible sheaves over discrete Noetherian rings form weak Serre subcategories

Source: Stacks Project, Tag 03RZ (3), etale-cohomology.tex, lemma-constructible-abelian;
Tag 09B5, proetale.tex, lemma-constructible-serre
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).

## Main statements

- `etale_discreteNoetherian_constructible_serre`: the etale closure clauses.
- `proEtale_discreteNoetherian_constructible_serre`: the pro-etale closure clauses.

The two statements spell out zero, kernel, cokernel and extension closure in the ambient
categories of modules over the constant ring sheaves. No finite-ring or invertibility
hypothesis occurs. The etale predicate uses finite generation of constant module values;
over a Noetherian ring this is equivalent to the finite-presentation convention of the node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- Constructible etale module sheaves contain zero and are closed under kernels, cokernels
and extensions. Source: Stacks Project, Tag 03RZ (3)
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).

Proof plan (the same six steps apply on either small site):
1. Finite presentation implies finite generation. Conversely, over the Noetherian ring,
`Module.finitePresentation_of_finite` gives finite presentation of each finite module.
2. The geometric inverse image preserves colimits and finite limits. A constant set sheaf
is a coproduct of terminal sheaves, so inverse image preserves constant sheaves naturally
in their values; applying this to the ring and module operations preserves constants as
ring and module sheaves, with no finiteness condition on their underlying sets.
3. The induced action agrees with module inverse image: both constant coefficient maps
are adjoint to the constant-section map. Abelian inverse image is exact, and module
kernels and cokernels have the corresponding underlying abelian kernels and cokernels.
Thus restriction to any stratum preserves kernels, cokernels and short exact sequences.
4. On every affine open, intersect the two finite stratifications by fibre products.
Pull back and refine the trivializing covers; localization exchange and inverse-image
composition identify the restrictions with the same constant modules on the common strata.
5. On each common stratum apply Tag 093U (3), the recorded locally constant finite-type
weak-Serre theorem, to the restricted map or exact sequence. Convert its finite-type
values back to finitely presented values by step 1. The common partition is a witness.
6. The zero module is finitely presented; on every affine open the identity stratum
trivializes the zero sheaf. The empty open also admits the empty partition.

The DAG inputs for these steps are:
- step 1: `def-sc-finitely-presented-module` and
  `lem-sc-noetherian-finite-module-finite-presentation`;
- step 2: `lem-weil-pbc-etale-inverse-image-algebraic-structures`,
  `def-weil-proetale-inverse-image`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`,
  and `def-weil-pbc-constant-sheaf`;
- step 3: `lem-weil-pbc-site-pullback-abelian-exact` and
  `def-weil-sheaf-of-modules-category`;
- step 4: `lem-weil-pbc-constructible-stratification-intersection`,
  `lem-weil-pbc-site-morphism-composition`, `lem-weil-pbc-etale-covering-base-change`,
  and `lem-weil-pbc-localize-ringed-site-morphism`;
- step 5: `lem-weil-pbc-locally-constant-derived-serre`, the Noetherian finite-presentation
  lemma of step 1, `def-weil-pbc-proetale-site`, and `def-weil-pbc-etale-site`;
- step 6: the constant zero module and the identity stratum. -/
theorem etale_discreteNoetherian_constructible_serre
    (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R] :
    Etale.constructibleNoetherianModules X R (0 : ringedSiteModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R))) ∧
    (∀ (F G : ringedSiteModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R)))
        (f : F ⟶ G),
      Etale.constructibleNoetherianModules X R F →
        Etale.constructibleNoetherianModules X R G →
          Etale.constructibleNoetherianModules X R (kernel f) ∧
          Etale.constructibleNoetherianModules X R (cokernel f)) ∧
    (∀ S : ShortComplex (ringedSiteModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of R))),
      S.ShortExact → Etale.constructibleNoetherianModules X R S.X₁ →
        Etale.constructibleNoetherianModules X R S.X₃ →
          Etale.constructibleNoetherianModules X R S.X₂) := by
  sorry

/-- Constructible pro-etale module sheaves contain zero and are closed under kernels,
cokernels and extensions. Source: Stacks Project, Tag 09B5, with the direct common-partition
proof of Tags 03RZ (3) and 093U (3)
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).

Proof plan:
1. Finite presentation implies finite generation, and Noetherianity gives the converse.
2. The covering-preserving base-change functor defines a geometric inverse image. It
preserves finite limits and colimits, hence constant sheaves as coproducts of terminals,
naturally in their values and therefore compatibly with ring and module operations.
3. The canonical coefficient structure map is this constant-ring identification: both
maps are adjoint to the constant-section family. Thus the tensor-defined module pullback
is the induced module inverse image. Abelian inverse image is exact; underlying abelian
kernels and cokernels compute those of module sheaves, so all stratum restrictions are exact.
4. For every affine open take the fibre-product common refinement of the two finite
constructible locally closed partitions. Pull back the two trivializing covers, using
cover preservation. Localization exchange identifies the pulled-back constant local
models on the localized sites, and inverse-image composition identifies restrictions.
5. Apply the arbitrary-site weak-Serre theorem, Tag 093U (3), on each common stratum.
Take small skeletons in the module universe; no points or finite underlying coefficient
sets are needed. Step 1 makes the resulting constant module values finitely presented.
6. The identity stratum and the constant zero module prove zero constructible on each
affine open; the empty partition is also allowed on the empty open. The preceding steps
prove the displayed kernel, cokernel and extension clauses affine-locally.

The DAG inputs for these steps are:
- step 1: `def-sc-finitely-presented-module` and
  `lem-sc-noetherian-finite-module-finite-presentation`;
- step 2: `lem-weil-pbc-etale-inverse-image-algebraic-structures`,
  `def-weil-proetale-inverse-image`, `lem-weil-pbc-left-exact-site-inverse-image-tensor`,
  and `def-weil-pbc-constant-sheaf`;
- step 3: `lem-weil-pbc-site-pullback-abelian-exact` and
  `def-weil-sheaf-of-modules-category`;
- step 4: `lem-weil-pbc-constructible-stratification-intersection`,
  `lem-weil-pbc-site-morphism-composition`, `lem-weil-pbc-etale-covering-base-change`,
  and `lem-weil-pbc-localize-ringed-site-morphism`;
- step 5: `lem-weil-pbc-locally-constant-derived-serre`, the Noetherian finite-presentation
  lemma of step 1, `def-weil-pbc-proetale-site`, and `def-weil-pbc-etale-site`;
- step 6: the constant zero module and the identity stratum. -/
theorem proEtale_discreteNoetherian_constructible_serre
    (X : Scheme.{u}) (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R
      (0 : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R)) ∧
    (∀ (F G : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R))
        (f : F ⟶ G),
      Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R F →
        Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R G →
          Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R (kernel f) ∧
          Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R (cokernel f)) ∧
    (∀ S : ShortComplex (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R)),
      S.ShortExact → Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₁ →
        Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₃ →
          Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R S.X₂) := by
  sorry

end AlgebraicGeometry
