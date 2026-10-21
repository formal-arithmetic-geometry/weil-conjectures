/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.CartesianCoefficients

/-!
# Internal-Hom continuity for finite constant local models

Source: Stacks Tags 08JH, 08JI and 08JB; Bhatt--Scholze, Proposition 6.8.11(3)
and Lemmas 6.3.14(1),(3), 6.8.12, with the node's local-to-global extraction
(blueprint: lem-sfb-finite-local-model-rhom-continuity).

Continuity is expressed on every cohomology sheaf of the image of the original
termwise-colimit cocone. Exact filtered sheaf colimits and the cohomology criterion
for derived isomorphisms identify this with invertibility of the evaluation-induced
comparison on functorial complex representatives. This avoids choosing an unrelated
representative at each vertex. The second conjunct records the sharp lower bound.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite constant local models have filtered derived internal-Hom continuity for
uniformly cohomologically bounded-below target diagrams, and preserve their lower bound.
The scheme is arbitrary, and the scalar modules may have torsion.

Source: Stacks 08JH, 08JI, 08JB; Bhatt--Scholze, Proposition 6.8.11(3) and
Lemmas 6.3.14(1),(3), 6.8.12
(blueprint: lem-sfb-finite-local-model-rhom-continuity).

Proof, following the nine DAG steps:
1. Use lem-sfb-module-object-ringed-site-derived-comparison to pass to sheaves
of modules over the section-ring sheaf, preserving evaluation, underlying sheaves,
cohomology and cocone maps. By lem-pur-ringed-site-grothendieck-abelian, filtered
colimits are exact. The kernel/image and image/cokernel sequences then show that
cohomology commutes with them, and they preserve objectwise quasi-isomorphisms.
2. On a chart W of the given pro-etale cover, identify its site with the slice
using lem-weil-proetale-weakly-etale-localization. The untwisted clause of
sk-prop-sfb-cartesian-coefficients identifies the restricted coefficient with B_W.
3. Restriction is exact by lem-pur-site-restriction-module-adjunction-exact.
It preserves module colimits by lem-weil-pbc-module-sheaves-colimits-forgetful
and lem-cbc-sieve-slice-sheafification, preserving the original cocone maps.
Use lem-weil-pbc-ringed-internal-hom-exact-restriction for derived Hom.
4. Apply lem-sfb-finite-constant-model-two-term-free-resolution on W. It gives
0 -> R^a -> R^b -> L_W -> 0, and a quasi-isomorphism Q -> L_W[0] with
Q = [R^a -> R^b] in degrees -1,0. In the field case a=0. Scalar torsion is allowed.
5. By lem-sfb-ringed-site-strict-perfect-hom and def-pur-derived-internal-hom,
Hom(Q,C) computes RHom(L_W[0],C), naturally in every target complex C.
Use lem-sc-finite-free-internal-hom-exact and def-pur-hom-complex to write
F_Q(C)^n = (C^n)^b + (C^(n-1))^a with differential
(f,g) |-> (d_C f, d_C g - (-1)^n f u). A target map acts on both coordinates.
6. These finite sums commute with colimits. The resulting degreewise isomorphisms
commute with the differential, since cocone maps commute with d_C, composition
with the fixed matrix u, and the integer sign. This gives an isomorphism of complexes.
7. Every vertex map is postcomposition with its original target cocone arrow.
Naturality of the Hom model and evaluation identify their induced comparison with
the specified evaluation-transpose map. Step 1 permits changes of representatives.
8. For a target N with cohomology zero below c, choose on the slice a representative
C with terms zero below c, using def-sbc-standard-tstructure-derived-category.
The formula in step 5 vanishes below c as well; thus RHom(L_W[0],N) is >= c.
No simultaneous nonfunctorial truncations of the diagram are needed for continuity.
9. Descend the cohomology isomorphisms of the comparison by
lem-sfb-sheaf-cover-local-isomorphism, then use
lem-weil-pbc-unbounded-derived-iso-cohomology. Descend the vanishing below c
in the same way, applying the local criterion to the map of each sheaf to zero.
This uses only the cover and the finite local resolutions, with no Noetherianity. -/
theorem finite_local_model_rhom_continuity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ : Λ = Mon.mk (FiniteConstantModel.integralCoefficients l E) ∨
      Λ = Mon.mk (FiniteConstantModel.rationalCoefficients l E))
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
    (_hL : HasFiniteConstantLocalModel Λ.X T L) (c : ℤ) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)) ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.obj i)).IsGE c) →
      ∀ n : ℤ, Nonempty (IsColimit
        ((DerivedCategory.Q ⋙ (CondensedRing.derivedHom Λ.X T).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj L)) ⋙
          DerivedCategory.homologyFunctor _ n).mapCocone (colimit.cocone N)))) ∧
    (∀ N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)),
      N.IsGE c →
      (((CondensedRing.derivedHom Λ.X T).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj N).IsGE c) := by
  sorry

end AlgebraicGeometry.ProEtale
