/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison
import Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.Paper.PQFCohomology
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-!
# Naturality of the canonical Cech-to-cohomology comparison map

Source: Stacks Project, Cohomology of Sheaves, Lemma Tag 01EQ
(blueprint: lem-sc-cech-comparison-map-naturality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical Cech-to-cohomology comparison exists, is independent of the resolution,
and is natural in the coefficient module. Alpha is a quasi-isomorphism for every resolution.
The comparison is characterized by `IsModuleCechComparison`, whose equation is required
for every injective resolution; existence is asserted for each coefficient module and
naturality is asserted for every pair of such comparisons.
The shared bicomplex places resolution degree first; multiplying the (p,q) summand by
`(-1)^(p*q)` identifies it with the source's exchanged convention and fixes both axes.
Source: Stacks Project, Cohomology of Sheaves, Lemma Tag 01EQ; the comparison is obtained
from an injective resolution, the first-quadrant total Cech double complex, and the
quasi-isomorphism from global sections. (blueprint: lem-sc-cech-comparison-map-naturality)

Proof:
1. Choose an injective resolution by lem-weil-pbc-scheme-modules-enough-injectives
   and def-sp-injective-resolutions. Form the Cech double complex using
   def-weil-pbc-site-cech-complex and its total by def-sp-double-complex-total.
2. By lem-weil-pbc-module-injective-open-cover-cech-acyclic and sheaf gluing
   (def-sc-zariski-site), alpha is an isomorphism on row cohomology. The functorial
   spectral sequences of thm-sp-double-complex-spectral-sequences give an isomorphism
   on the finite filtration quotients, hence on cohomology by induction and the five
   lemma. The augmentation gives beta into the total complex.
3. Use the resolution identification of pqf-def-cohomology and
   lem-weil-pbc-derived-functor-map-via-lift to define c by H(beta) followed by the
   inverses of H(alpha) and the identification. By
   lem-weil-pbc-injective-resolution-lift-exists, lift the identity to any other
   resolution. The alpha and beta squares commute, so the derived-map formula makes
   c independent of the resolution. Invertibility of H(alpha) gives uniqueness.
4. By lem-weil-pbc-injective-resolution-lift-exists, lift a coefficient morphism.
   Cech functoriality induces a morphism of double complexes; the alpha
   and beta squares commute by restriction functoriality and the augmentation equation.
   Taking cohomology and applying lem-weil-pbc-derived-functor-map-via-lift gives the
   displayed naturality square.
-/
theorem cechComparisonMapNaturality (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (hcover : iSup U = ⊤) :
    (∀ (F : X.Modules) (I : InjectiveResolution F), QuasiIso (moduleCechAlpha U I)) ∧
    ∀ p : ℕ, (∀ F : X.Modules, ∃ c :
        ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj F,
        IsModuleCechComparison U F p c) ∧
      (∀ (F G : X.Modules) (φ : F ⟶ G)
        (cF : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
        (cG : ((CategoryTheory.cechComplexFunctor U).obj G.presheafModuleCat).homology p ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj G),
        IsModuleCechComparison U F p cF → IsModuleCechComparison U G p cG →
        HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map
            ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
              φ.val)) p ≫ cG =
          cF ≫ (RingedSpace.moduleCohomology X.toRingedSpace p).map φ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
