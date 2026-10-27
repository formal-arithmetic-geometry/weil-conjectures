/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.StalkKFlatTensorHomology
import WeilConjectures.Topology.RingedModuleSkyscraper
import WeilConjectures.Topology.SkyscraperComplexStalk

/-! # Tor amplitude on a ringed space, stalks and uniform bounds

Source: Stacks Project, Tag 09U9, `lemma-tor-amplitude-stalk`; Tag 06YB,
`lemma-check-K-flat-stalks`, and the finite-subcover consequence of the stalk criterion.
(blueprint: lem-trf-ringed-tor-amplitude-stalk-test).

Open restriction is written on the localized site of opens using `overFunctor`.
This is the ordinary restriction to the open subspace, with its restricted ring sheaf.
No scheme, locally ringed, quasi-coherent or boundedness condition is imposed.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- A fixed Tor-amplitude interval is detected by all modules over every stalk ring.
Source: Stacks Project, Tag 09U9, `lemma-tor-amplitude-stalk`, and Tag 06YB.
(blueprint: lem-trf-ringed-tor-amplitude-stalk-test).

Proof, Steps 1--3 of the accepted split:
1. Choose a K-flat resolution P of K by lem-pc-kflat-resolution. The exact stalk
functor (lem-weil-pbc-module-stalk-exact) makes P_z to K_z a quasi-isomorphism.
The localization Q inverts it (def-weil-abstract-derived-category). Applying
lem-pc-stalk-kflat-tensor-homology with the identity stalk-ring isomorphism identifies
stalks of tensor cohomology with the cohomology of the derived stalk tensor.
2. Given global vanishing, test against the skyscraper of an arbitrary stalk module L
(def-pc-ringed-module-skyscraper). Its stalk is L by
lem-pc-skyscraper-complex-stalk-recovery. Step 1 gives the required vanishing for L.
This argument works for nonclosed points as well.
3. Conversely, choose one K-flat resolution P. For every test sheaf F, Step 1 and
stalkwise vanishing make all stalks of the tensor cohomology sheaf zero.
Clause (5) of lem-weil-pbc-module-stalk-exact, applied to zero to H to zero,
then makes that sheaf zero. This resolution witnesses the existential predicate
of def-trf-ringed-complex-derived-tensor-vanishing. -/
theorem torAmplitude_iff_stalks
    (Z : RingedSpace.{u})
    [∀ z : Z, HasDerivedCategory.{v} (ModuleCat.{u} (Z.presheaf.stalk z))]
    (K : CochainComplex (Modules Z) ℤ) (a b : ℤ) (hab : a ≤ b) :
    (∀ (F : Modules Z) (i : ℤ), i < a ∨ b < i →
      CochainComplex.sheafDerivedTensorVanishes Z.sheaf K F i) ↔
    ∀ (z : Z) (L : ModuleCat.{u} (Z.presheaf.stalk z)) (i : ℤ),
      i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Z.presheaf.stalk z)) i).obj
        (DerivedCategory.Q.obj
          (((moduleStalkFunctor Z z).mapHomologicalComplex (.up ℤ)).obj K) ⊗
            (DerivedCategory.singleFunctor (ModuleCat.{u} (Z.presheaf.stalk z)) 0).obj L)) := by
  sorry

/-- Local finite Tor bounds admit one uniform finite interval on a quasi-compact ringed space.
Source: Stacks Project, Tag 09U9, `lemma-tor-amplitude-stalk`, finite-subcover consequence.
(blueprint: lem-trf-ringed-tor-amplitude-stalk-test).

Proof, Steps 4--6 of the accepted split:
4. For z in an open W, identify the restricted stalk with the original stalk by
sending each representative on V contained in W to the same representative on Z.
The inverse restricts a representative on U to U intersect W; both composites are
the identity on germs (def-pc-module-stalk-functor). These identifications preserve
the scalar action and differentials, so Steps 1--3 give the same Tor tests on W.
5. For nonempty Z, take a finite subcover of the Tor-bounded neighbourhoods.
Take the minimum of their lower bounds and the maximum of their upper bounds.
At a point choose a member of the cover. A degree outside the resulting interval
is outside that member's interval, so Step 4 gives vanishing at this stalk.
Steps 1--3 give global vanishing. Only neighbourhood bounds, not merely finite
bounds at individual points, are used.
6. Global bounds give local bounds by taking the whole space at each point.
For the empty space the stalk condition is vacuous and Steps 1--3 give [0,0]. -/
theorem locallyFiniteTorAmplitude_iff_uniform
    (Z : RingedSpace.{u}) [CompactSpace Z]
    (K : CochainComplex (Modules Z) ℤ) :
    (∀ z : Z, ∃ W : Opens Z, z ∈ W ∧ ∃ a b : ℤ, a ≤ b ∧
      ∀ (F : SheafOfModules.{u} ((moduleRings Z).over W)) (i : ℤ),
        i < a ∨ b < i →
        CochainComplex.sheafDerivedTensorVanishes (Z.sheaf.over W)
          (((SheafOfModules.overFunctor (moduleRings Z) W).mapHomologicalComplex
            (.up ℤ)).obj K) F i) ↔
    ∃ a b : ℤ, a ≤ b ∧ ∀ (F : Modules Z) (i : ℤ), i < a ∨ b < i →
      CochainComplex.sheafDerivedTensorVanishes Z.sheaf K F i := by
  sorry

/-- On the empty ringed space the interval [0,0] is a global Tor-amplitude interval.
Source: Stacks Project, Tag 09U9, `lemma-tor-amplitude-stalk`, empty-space consequence.
(blueprint: lem-trf-ringed-tor-amplitude-stalk-test).

Proof, Step 6: the condition on all stalk modules is vacuous since there are no
points. Steps 1--3 (the exact-stalk and K-flat-resolution argument of
lem-pc-kflat-resolution, lem-pc-stalk-kflat-tensor-homology and
lem-weil-pbc-module-stalk-exact) give global tensor vanishing in every degree,
in particular outside [0,0]. -/
theorem torAmplitude_zero_zero_of_isEmpty
    (Z : RingedSpace.{u}) [IsEmpty Z] (K : CochainComplex (Modules Z) ℤ) :
    ∀ (F : Modules Z) (i : ℤ), i < 0 ∨ 0 < i →
      CochainComplex.sheafDerivedTensorVanishes Z.sheaf K F i := by
  sorry

end AlgebraicGeometry.RingedSpace
