/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Continuous sections with finite discrete quotient

Source: blueprint `sk-lem-pe-derived-nakayama-resolution.proof.md`, On the point and Triangles.
(blueprint: lem-pe-profinite-sections-finite-quotient)

The condensed coefficient sheaves use the existing universe-general continuous coefficient
construction. The scalar map is the recorded continuous-map postcomposition, and the restricted
regular module specifies the pointwise module structures. Both conclusions characterize their
arrows by postcomposition on sections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

/-- Continuous T-valued sections as internal modules over the continuous A-valued ring:
restrict the regular module along the given continuous scalar homomorphism. The scalar map
is the recorded postcomposition `continuousMapRingSheafMapOfUniverse` of
def-sfb-continuous-map-condensed-ring-map; `continuousCoefficientRingSheaf` is definitionally
that node's `continuousMapRingSheafOfUniverse.{u, u}`.
Source: blueprint derived Nakayama resolution, On the point, pointwise scalar action.
(blueprint: lem-pe-profinite-sections-finite-quotient) -/
noncomputable def continuousSectionsModule
    (A T : Type u) [CommRing A] [CommRing T]
    [TopologicalSpace A] [TopologicalSpace T]
    [IsTopologicalRing A] [IsTopologicalRing T]
    [Algebra A T] [ContinuousSMul A T] :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (continuousCoefficientRingObj A) :=
  (Mod.comap ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A T) (continuous_algebraMap A T) :
        continuousCoefficientRingSheaf A ⟶ continuousCoefficientRingSheaf T))).obj
    (Mod.regular (continuousCoefficientRingObj T))

/-- Continuous sections preserve this short exact topological module sequence, both on each
profinite set and as condensed internal modules. The section formulas uniquely specify the
postcomposition arrows, rather than allowing arbitrary arrows witnessing short exactness.

Source: blueprint derived Nakayama resolution, On the point and Triangles.
(blueprint: lem-pe-profinite-sections-finite-quotient)

Proof plan:
1. Pointwise addition and scalar multiplication make C(S,T_i) into C(S,A)-modules;
   composition with the continuous A-linear maps is C(S,A)-linear.
2. Injectivity is checked at each point; range f = ker g gives the zero composite.
3. A section killed by g lands continuously in its subspace kernel. The inverse of the
   prescribed homeomorphism onto this kernel gives its continuous preimage under f.
4. Choose a preimage in T_1 for each value in the finite discrete T_2. Composing this
   continuous map from a discrete space with a section lifts that section.
5. The continuous-function sheaves of sk-def-sfb-condensed-ring carry the pointwise actions,
   compatible with precomposition restrictions. The module objects are those of
   sk-def-sfb-module-objects. The sheaf tensor and sheaf-tensor-closed nodes supply the
   monoidal setting; def-weil-pbc-internal-abelian-sheaf-module-equivalence identifies these
   with sectionwise modules without changing sections or restrictions.
6. By def-weil-sheaf-of-modules-category, kernels are sectionwise and cokernels are
   sheafifications of sectionwise cokernels. Steps 2--4 give a kernel and zero cokernel.
   The equivalence in step 5 transports this short exactness to internal module objects. -/
theorem continuousSections_finiteDiscrete_shortExact
    (A T₀ T₁ T₂ : Type u) [CommRing A] [CommRing T₀] [CommRing T₁] [CommRing T₂]
    [TopologicalSpace A] [TopologicalSpace T₀] [TopologicalSpace T₁] [TopologicalSpace T₂]
    [IsTopologicalRing A] [IsTopologicalRing T₀]
    [IsTopologicalRing T₁] [IsTopologicalRing T₂]
    [Algebra A T₀] [Algebra A T₁] [Algebra A T₂]
    [ContinuousSMul A T₀] [ContinuousSMul A T₁] [ContinuousSMul A T₂]
    (f : T₀ →L[A] T₁) (g : T₁ →L[A] T₂)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap)
    [Finite T₂] [DiscreteTopology T₂]
    (hker : ∃ e : T₀ ≃ₜ LinearMap.ker g.toLinearMap,
      ∀ t : T₀, (e t).val = f t) :
    (∀ S : Profinite.{u},
      ∃ (F : C(S, T₀) →ₗ[C(S, A)] C(S, T₁))
        (G : C(S, T₁) →ₗ[C(S, A)] C(S, T₂)),
        (∀ a : C(S, T₀), ∀ s : S, F a s = f (a s)) ∧
        (∀ a : C(S, T₁), ∀ s : S, G a s = g (a s)) ∧
        Function.Injective F ∧ Function.Exact F G ∧ Function.Surjective G) ∧
    (∃ (F : continuousSectionsModule A T₀ ⟶ continuousSectionsModule A T₁)
       (G : continuousSectionsModule A T₁ ⟶ continuousSectionsModule A T₂)
       (h : F ≫ G = 0),
       (∀ (S : Profinite.{u}) (a : ULift.{u + 1} C(S, T₀)) (s : S),
         ((F.hom.hom.app (op S)) a).down s = f (a.down s)) ∧
       (∀ (S : Profinite.{u}) (a : ULift.{u + 1} C(S, T₁)) (s : S),
         ((G.hom.hom.app (op S)) a).down s = g (a.down s)) ∧
       (ShortComplex.mk F G h).ShortExact) := by
  sorry

end Profinite
