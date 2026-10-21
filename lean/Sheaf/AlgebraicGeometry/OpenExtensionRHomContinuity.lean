/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Topology.NoetherianSpace
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence

/-!
# Open extension preserves bounded-target internal-Hom continuity

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemmas 6.3.14(2), 6.8.12;
Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3 and its open-immersion argument
(blueprint: lem-sfb-rhom-continuity-open-extension).

Continuity is expressed on every cohomology sheaf. Exact filtered colimits identify
these maps with the cohomology of the evaluation-induced comparison formed by taking
termwise sheaf colimits of functorial complex representatives. In particular, no
ordinary categorical colimit of a diagram in the triangulated derived category is used.
The map `colimit.post` has components obtained by applying internal Hom and cohomology
to the original complex-colimit inclusions, fixing the comparison canonically.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Exact open extension preserves both bounded-target internal-Hom continuity and its
chosen uniform lower bound, without a constructibility hypothesis.

Source: Bhatt--Scholze, Lemmas 6.3.14(2), 6.8.12, refined using Hemo--Richarz--Scholbach,
Lemma 5.3(1) and the open case of its proof of (2)
(blueprint: lem-sfb-rhom-continuity-open-extension).

Proof plan:
1. Every subset of a Noetherian space is quasi-compact
   (`lem-sfb-noetherian-space-compact-subsets`). Thus the open immersion is quasi-compact;
   separated cancellation and separated implies quasi-separated
   (`lem-weil-pbc-separated-cancellation`, `lem-pc-separated-quasi-separated`) give qcqs.
   Choose a complementary closed subscheme using
   `lem-weil-pbc-closed-subset-closed-subscheme` solely to apply the open Hom formula.
2. Pro-etale abelian sheaves are Grothendieck (`lem-sfb-proetale-sheaves-grothendieck`);
   their closed additive tensor (`sk-def-sfb-sheaf-tensor`) makes internal modules
   Grothendieck (`lem-sfb-modobj-grothendieck`). Exact filtered colimits
   (`def-sp-grothendieck-abelian`, `src-weil-homology-preserves-exact-colimits`) preserve
   common lower bounds and objectwise quasi-isomorphisms of complex diagrams.
3. Coefficient-compatible inverse image is exact
   (`det-prop-sfb-module-pullback-exact-main`) and left adjoint
   (`def-sfb-module-upper-lower-adjunction`), hence preserves colimits
   (`lem-weil-pbc-left-adjoint-preserves-colimits`), their cocones and lower bounds.
4. Derived direct image preserves every lower bound: use enough injectives
   (`lem-sp-grothendieck-enough-injectives`), a bounded-below representative
   (`def-sbc-standard-tstructure-derived-category`), an injective resolution with the
   same lower support (`lem-weil-pbc-complex-injective-resolution-mono`) and its
   K-injectivity (`lem-weil-pbc-bounded-below-injectives-kinjective`). Termwise direct
   image computes the total functor (`sk-def-sfb-module-derived-pushpull`).
5. The evaluation-normalized open formula (`lem-sfb-open-closed-internal-hom-formulas`)
   identifies RHom(v_! A,N) with Rv_* RHom(A,v^* N). The section-action equivalence
   (`def-weil-pbc-internal-abelian-sheaf-module-equivalence`) identifies its direct image
   and colimits with those in `lem-weil-pbc-condensed-qcqs-pushforward-continuity`.
6. Apply the hypothesized bound after v^*, then the lower-bound preservation of Rv_*:
   the output has lower bound c+d, with exactly the original d.
7. For a diagram bounded below by c, the internal Homs after v^* share the bound c+d.
   Apply `lem-weil-pbc-condensed-qcqs-pushforward-continuity` to that diagram, then
   the continuity hypothesis and preservation of the original colimit by v^*.
8. Naturality of the evaluation-normalized open formula identifies each cocone component
   with RHom(v_! A,ι_i). The colimit universal property identifies the resulting map
   with the specified evaluation comparison. Exact colimits and detection of derived
   isomorphisms on all cohomology sheaves give precisely the displayed degreewise maps. -/
theorem openImmersionLowerShriek_rhom_continuity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {V T : Scheme.{u}} (v : V ⟶ T) [IsOpenImmersion v] [TopologicalSpace.NoetherianSpace T]
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) (condensedRingObj Λ.X V)))
    (d : ℤ)
    (hcontinuity : ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ.X V)) ℤ) (c : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.obj i)).IsGE c) → ∀ q : ℤ,
      IsIso (colimit.post N
        (DerivedCategory.Q ⋙ (derivedHom Λ.X V).obj (op A) ⋙
          DerivedCategory.homologyFunctor _ q)))
    (hbound : ∀ (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ.X V))) (c : ℤ),
      N.IsGE c → (((derivedHom Λ.X V).obj (op A)).obj N).IsGE (c + d)) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ.X T)) ℤ) (c : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.obj i)).IsGE c) → ∀ q : ℤ,
      IsIso (colimit.post N
        (DerivedCategory.Q ⋙
          (derivedHom Λ.X T).obj (op ((openImmersionLowerShriek Λ.X v).mapDerivedCategory.obj A))
          ⋙ DerivedCategory.homologyFunctor _ q))) ∧
    (∀ (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ.X T))) (c : ℤ),
      N.IsGE c →
        (((derivedHom Λ.X T).obj
          (op ((openImmersionLowerShriek Λ.X v).mapDerivedCategory.obj A))).obj N).IsGE (c + d)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
