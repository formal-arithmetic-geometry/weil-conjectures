/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.Paper.ContinuousIntegralLocalization
public import Sheaf.CategoryTheory.HomColimitExtension
import Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness
import Sheaf.Paper.ContinuousIntegralComplexTelescope
import Sheaf.Paper.IntegralConstructibleSheafHom
import Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport
import Sheaf.Paper.ContinuousIntegralLocalizationModel
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Shifted Hom continuity for the integral localization unit telescope

Source: Bhatt--Scholze, Lemma 6.8.12 and the full-faithfulness argument in
Proposition 6.8.14(2); Hemo--Richarz--Scholbach, Lemma 5.3.
(blueprint: lem-sfb-integral-localization-hom-colimit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Shifted additive Hom from an integral bounded constructible object preserves the
canonical scalar-localization unit telescope, indexed by ℕ or by ULift ℕ.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), full faithfulness.
(blueprint: lem-sfb-integral-localization-hom-colimit)

Proof:
1. For any complex C strictly zero below a, use integralComplexLocalization_colimit
   (lem-weil-pbc-integral-complex-telescope). All stages have the same lower bound a.
   Good truncation at a is naturally isomorphic to this diagram, so transports its
   colimit to the indicated good-truncated telescope.
2. Reindex along AsSmall ℕ ≌ ℕ. The common lower bound and colimit property persist.
   Apply integralConstructible_sheaf_hom_colimit
   (lem-weil-pbc-integral-constructible-sheaf-hom) to every constructible module M:
   M in degree zero satisfies homColimitProperty for this derived cocone.
3. For this fixed cocone, homColimitProperty contains zero and is invariant under
   isomorphisms and shifts. Precomposition gives the isomorphism comparison; the
   shift identity Hom(T[m],D[q]) = Hom(T,D[q-m]) gives shift invariance.
4. Apply bounded_cohomology_cone_witness (lem-sfb-bounded-cohomology-cone-witness)
   to K. Its cohomology sheaves are constructible by integralConstructible. Induct
   on the finite witness. Shifted cohomology leaves satisfy the property by 2--3.
   Rotate each witness triangle F_i → F_j → F_r[n] to put the two known objects
   at its ends (def-weil-triangulated-category), then apply
   homColimitProperty_extensions (lem-weil-pbc-hom-colimit-extension). Shift back
   to F_r. This also covers zero and acyclic K.
5. B is bounded below. Use exists_integralLocalization_complex_model
   (lem-weil-pbc-integral-localization-complex-model), then apply
   localizationCocone_isColimit_of_model
   (lem-weil-pbc-integral-localization-colimit-transport) to each shifted additive
   Hom functor from K. Steps 1--4 supply its continuity premise for every strictly
   bounded-below complex telescope. Thus the lifted canonical Hom cocone is colimiting.
6. The model identifies every leg with the specified unit followed by the restricted
   inverse scalar power (def-weil-pbc-integral-localization-telescope). Hence the
   colimit comparison is precisely the canonical map in the statement. The order
   equivalence ULift ℕ ≌ ℕ transports this conclusion to the ordinary index as well.
   No colimit in the derived category is assumed. -/
theorem integralLocalization_hom_colimit (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (K B : integralConstructible ℓ E X) :
    (∀ q : ℤ, IsIso (colimit.desc _
      ((shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (op K.obj)).mapCocone
        (integralLocalizationCocone ℓ E X B.obj)))) ∧
    homColimitProperty (integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ B.obj)
      (integralLocalizationLiftedCocone.{u, u + 1} ℓ E X B.obj) K.obj := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
