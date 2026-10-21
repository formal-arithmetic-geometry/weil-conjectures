/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Bounded-below continuity of closed support and open direct image

Source: Stacks Project, Tag 09BM; the support triangles in Hemo--Richarz--Scholbach,
(3.3)--(3.4), Lemma 3.4; bounded direct-image continuity in the blueprint
`det-pe-bounded-continuity-direct-image`
(blueprint: lem-sfb-closed-support-bounded-continuity).

The comparisons use termwise colimits of functorial K-injective models. They are the
localizations of `colimit.post` for the resolution followed by the underived functor.
Thus every leg is the image of a leg of the original complex colimit cocone. No
categorical colimit of a diagram in the triangulated derived category is substituted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxHeartbeats 100000 in
-- Colimits of these internal-module complexes need a larger typeclass search budget.
set_option synthInstance.maxSize 4096 in
/-- Closed support and open direct image commute with filtered colimits sharing a
cohomological lower bound, and preserve that lower bound.
Source: Stacks Project, Tag 09BM; Hemo--Richarz--Scholbach, (3.3)--(3.4), Lemma 3.4;
the blueprint bounded-continuity direct-image proof
(blueprint: lem-sfb-closed-support-bounded-continuity).

`closedSupport` is the recorded kernel construction, whose total right derivation is
the right adjoint of closed direct image. Each comparison below is formed in complexes
and then localized. Functorial K-injective resolution represents the total right derived
functor on every input and every cocone leg, including the colimit complex itself.
Exactness of filtered sheaf colimits makes this independent of representative choices.

Proof plan:
1. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to identify internal modules
with modules over the section-ring sheaf, including their ordinary derived localizations.
2. By lem-pc-module-filtered-colimits-tensor, filtered sheaf colimits are exact. Apply this
to the kernel/image sequences defining cohomology: cohomology commutes with filtered
colimits. Hence these colimits preserve quasi-isomorphisms and common lower bounds.
3. The noetherian topology makes every open quasi-compact, hence j is qcqs. The
recollement resolution models give left t-exactness of Rj_* and Ri^! at every integer c.
4. Apply good truncation at c functorially. Its projection is a quasi-isomorphism on
inputs with vanishing cohomology below c. Cokernels commute with colimits, so truncation
also commutes with the termwise colimit, retaining the comparisons of the original cocone.
5. Apply det-pe-bounded-continuity-direct-image to j and the truncated diagram. Compute
on the same source-module K-injective resolutions as the full module pushforward.
Restriction of scalars along B_T -> j_* B_U changes neither cohomology nor colimits;
lem-weil-pbc-module-sheaves-colimits-forgetful reflects the resulting isomorphisms.
6. Apply lem-sf-derived-homology-long-exact and exact i^* to the natural triangle
i_*Ri^!K -> K -> Rj_*j^*K ->. Using i^*i_* = id gives five consecutive terms
H^(q-1)(i^*K), H^(q-1)(i^*Rj_*j^*K), H^q(Ri^!K), H^q(i^*K), H^q(i^*Rj_*j^*K).
The connecting arrows are natural because they come from the natural fourth triangle map.
7. Compare the filtered colimit of these sequences for N_t with the sequence for colim N.
Both rows are exact. The four outer comparisons are invertible: exact colimit-preserving
i^*, j^* handle the ordinary terms, and step 5 handles Rj_*j^*N_t with the same bound c.
8. Apply lem-weil-pbc-five-lemma to obtain invertibility of the middle comparison in
every degree. The derived localization then makes the closed-support comparison an
isomorphism. All comparisons were induced by the original cocone. No upper bound,
constructibility, structure-sheaf noetherianity or cohomological dimension was used.
-/
theorem closedSupport_bounded_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {T Z U : Scheme.{u}} [TopologicalSpace.NoetherianSpace T]
    (i : Z ⟶ T) [IsClosedImmersion i] (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ) (c : ℤ) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex (supportModules Λ T) ℤ),
      (∀ t : I, (DerivedCategory.Q.obj (N.obj t)).IsGE c) →
      IsIso (DerivedCategory.Q.map (colimit.post N
        (CochainComplex.kInjectiveResolutionFunctor.{u + 1} (supportModules Λ T) ⋙
          (closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ))))) ∧
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (V : I ⥤ CochainComplex (supportModules Λ U) ℤ),
      (∀ t : I, (DerivedCategory.Q.obj (V.obj t)).IsGE c) →
      IsIso (DerivedCategory.Q.map (colimit.post V
        (CochainComplex.kInjectiveResolutionFunctor.{u + 1} (supportModules Λ U) ⋙
          (lowerStar Λ j).mapHomologicalComplex (ComplexShape.up ℤ))))) ∧
    (∀ K : DerivedCategory (supportModules Λ T), K.IsGE c →
      ((closedSupport Λ i j).rightDerivedFunctor.obj K).IsGE c) ∧
    (∀ K : DerivedCategory (supportModules Λ U), K.IsGE c →
      ((lowerStar Λ j).rightDerivedFunctor.obj K).IsGE c) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
