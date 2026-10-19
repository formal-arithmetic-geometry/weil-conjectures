/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.FiniteEtaleModuleTraceDegree
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne
import Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition
import Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris
import Sheaf.AlgebraicGeometry.LisseFiniteEtaleFiltration
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleModuleTraceDegree
import WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.Paper.EtaleLisseFiltrationDevissage
import Sheaf.Paper.ProjectionCompactification

/-!
# Constructibility for lisse coefficients on an open relative affine line

Source: Stacks Project, Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`, specialized to
finite coefficient rings and affine finite-type integer bases
(blueprint: lem-weil-pbc-etale-lisse-open-relative-line-constructibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Lisse sheaves with finite module values on an open relative affine line over a
finite-type integer base have constructible compactly supported cohomology sheaves.
Source: Stacks Project, Tag 0GKY, `lemma-loc-constant-shriek-rel-dim-1`
(blueprint: lem-weil-pbc-etale-lisse-open-relative-line-constructibility).

Proof plan:
1. Finite type over the Noetherian ring of integers makes the base and relative line
   Noetherian. Cover the open by finitely many principal affine opens; intersections
   remain principal and the restricted projections are smooth of relative dimension one
   (`lem-weil-pbc-finite-type-over-noetherian`, `lem-sc-affine-noetherian-underlying-space`,
   `sbc-lem-affine-space-smooth`, `lem-sbc-smooth-relative-dimension-permanence`).
2. Split the finite coefficient ring into its primary factors using orthogonal idempotents.
   Additivity reduces to a sheaf killed by a power of one prime; the zero sheaf is immediate.
3. Use `lem-weil-pbc-etale-lisse-finite-etale-filtration` and the module trace-degree theorem
   `lem-weil-pbc-finite-etale-module-trace-degree` to split the sheaf off a finite direct image.
   Finite direct image is exact (`lemma-weil-pbc-finite-direct-image-exact`), finite morphisms
   are proper (`lem-weil-pbc-finite-proper`), and shriek composition and compactification
   independence identify its shriek image with the image of the pulled-back sheaf.
   Nagata compactification supplies the intermediate compactifications.
4. The chosen shriek is triangulated: extension by zero is exact and direct image has a
   triangulated right derived functor (using enough injectives). On each affine clopen
   component of the finite cover, apply `lem-weil-pbc-etale-constant-shriek-rel-dim-1` to
   the constant filtration factors. The short-exact triangles and long exact cohomology
   sequences, together with `thm-constructible-serre`, give constructibility by induction.
   Finite sums and the trace splitting descend constructibility to the original sheaf.
5. Induct on the size of the principal cover using
   `lem-weil-pbc-etale-shriek-relative-mayer-vietoris`. Intersections have smaller covers.
   Its long exact cohomology sequence and Serre closure give the result for the specified
   compactification, including the empty-open case. -/
theorem isConstructibleEtaleModuleSheaf_lisse_openRelativeLine_shriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (U : (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R))).Opens)
    (L : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((L.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (U.toScheme.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M))
    (c : Compactification
      (U.ι ≫ (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of R)) ↘ Spec (.of R))))
    (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.Plus.homologyFunctor
        (Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj
          ((_root_.DerivedCategory.Plus.singleFunctor
            (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L))) := by
  sorry

end AlgebraicGeometry.Etale
