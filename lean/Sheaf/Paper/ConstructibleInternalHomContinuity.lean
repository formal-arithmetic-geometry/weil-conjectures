/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.FiniteModelStratumFiltration
import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Continuity of constructible-source derived internal Hom

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemmas 6.8.12,
6.3.14 and the local support argument of 6.7.13. The internal filtered-colimit
assertion is the additional local devissage claim of the DAG, rather than the
verbatim global direct-sum assertion of the paper
(blueprint: lem-sfb-constructible-internal-hom-continuity).

We use the equivalent formulation on every cohomology module sheaf. The cocone
is obtained by applying localization, the recorded closed derived internal Hom,
and cohomology to the actual termwise-colimit cocone. Thus its legs are the
canonical evaluation-induced maps, and no complex representative is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Constructible-source internal Hom commutes with uniformly bounded-below filtered
colimits in the ordinary, uncompleted module-object derived category. On cohomology,
the image of the original colimit cocone is a colimit cocone in every degree.

Source: Bhatt--Scholze, Lemmas 6.8.12, 6.3.14 and 6.7.13, with the internal
filtered-colimit devissage in the node
(blueprint: lem-sfb-constructible-internal-hom-continuity).

Proof, following the seven DAG steps:
1. Use lem-sfb-module-object-ringed-site-derived-comparison to identify the closed
module-object Hom with the ordinary ringed-site model, preserving evaluation.
Filtered sheaf colimits are exact (lem-pur-ringed-site-grothendieck-abelian), hence
commute with cohomology and preserve objectwise quasi-isomorphisms. The functorial
Hom model of def-pur-derived-internal-hom is therefore independent of resolutions.
A common cohomological bound c can be made termwise by replacing degree c with
coker(d^(c-1)) and killing lower terms; exactness makes this commute with colimits.
Strengthen continuity for a fixed source A by a uniform output bound c+d_A.
2. For a finite constant local model L, use
lem-sfb-finite-constant-model-two-term-free-resolution on each model chart.
The bounded-free Hom model (lem-weil-pbc-ringed-site-bounded-free-rhom-model)
uses finite sums of target terms, so commutes with filtered colimits and vanishes
below c, including integral torsion models. Exact slice restriction identifies
these with the canonical maps (lem-weil-pbc-ringed-internal-hom-exact-restriction).
The chart inverse images preserve colimits by def-sfb-module-upper-lower-adjunction,
lem-weil-pbc-left-adjoint-preserves-colimits and sk-prop-sfb-cartesian-coefficients.
Use lem-weil-proetale-weakly-etale-localization and
lem-sfb-sheaf-cover-local-isomorphism to descend the cohomology isomorphisms.
3. For a closed immersion with open complement j, use the support triangle of
lem-weil-pbc-condensed-open-closed-recollement. The topological Noetherian
hypothesis makes the immersions qcqs. Apply det-pe-bounded-continuity-direct-image
to Rj_* on the uniformly bounded-below targets. Exact filtered colimits of the
support triangles and lem-weil-pbc-five-lemma give continuity for Ri^!, with the
same common lower bound; apply exact i^* to remove i_*.
4. The closed formula of lem-sfb-open-closed-internal-hom-formulas identifies
RHom(i_*L,N) with i_*RHom(L,Ri^!N). Steps 2--3 and the exact filtered-colimit
preservation of lem-weil-pbc-proetale-ringed-open-closed give continuity and d=0.
5. The open formula identifies RHom(v_!A,N) with Rv_*RHom(A,v^*N).
The bound c+d_A permits the bounded-continuity theorem again; continuity and
that bound are preserved by open extension. This covers v_!t_*L.
6. Shifts and finite source triangles preserve continuity: internal Hom reverses
source triangles and shifts. Exact filtered colimits of their cohomology long
sequences (lem-sf-derived-homology-long-exact) and the five lemma identify the
remaining comparison. Chain-map cones use only finite sums, so colimits preserve
these triangles and their canonical comparison maps. Shifting A by n replaces
d_A by d_A+n; triangle rotations give a minimum of the two bounds, possibly minus one.
7. Apply lem-sfb-finite-model-stratum-filtration to each cohomology sheaf of K.
Its finite filtration has quotients v_!t_*L, and its short exact sequences give
triangles by lem-sf-derived-ses-triangle. Steps 4--6 yield continuity for each
cohomology sheaf. Consecutive standard truncations
(def-sbc-standard-tstructure-derived-category) reconstruct bounded K from their
finitely many shifts. Every map is induced by evaluation and the given cocone.
Exact colimits preserve the model-changing quasi-isomorphisms, so the assertion
is independent of all representative choices. The cohomology criterion
lem-weil-pbc-unbounded-derived-iso-cohomology identifies this formulation with
invertibility of the requested derived comparison. -/
theorem constructible_internalHom_continuity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (_hΛ : Λ = Mon.mk (FiniteConstantModel.integralCoefficients l E) ∨
      Λ = Mon.mk (FiniteConstantModel.rationalCoefficients l E))
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (_hK : constantModelBoundedConstructible Λ.X X K)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (M : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) ℤ)
    (c : ℤ) (_hM : ∀ (i : I) (r : ℤ), r < c → IsZero ((M.obj i).X r)) :
    ∀ n : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ (CondensedRing.derivedHom Λ.X X).obj (Opposite.op K) ⋙
        DerivedCategory.homologyFunctor _ n).mapCocone (colimit.cocone M))) := by
  sorry

end AlgebraicGeometry.ProEtale
