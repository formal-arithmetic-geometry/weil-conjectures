/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType
import WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk

/-! # Injectivity near independent germs of a finite free epimorphism

Source: Stacks Project, Modules, Tag 0B8J, last two sentences of the proof of
`lemma-finite-presentation-stalk-free`.
(blueprint: lem-trf-finite-free-epi-independent-germs)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- A finite free epimorphism onto a finitely presented module becomes injective on
sections near a point if the germs of its generator images are linearly independent.
This asserts only injectivity of the given epimorphism on smaller open sets; it
neither chooses sections representing germs nor asserts a free trivialization.

Source: Stacks Project, Modules, Tag 0B8J, proof of
`lemma-finite-presentation-stalk-free`, kernel and final shrinking; Tags 01BP(1)
and 01B8 for finite type of the kernel and vanishing near its zero stalk.
(blueprint: lem-trf-finite-free-epi-independent-germs)

Proof: Restrict the finite presentation of F to U and apply 01BP(1) to p. Its
kernel K is of finite type. A section of K is a tuple of ring sections whose
linear combination of the displayed generator images is zero. Taking germs at
x, linear independence makes each coordinate germ zero. Equality of germs and
finiteness of the tuple give one smaller neighbourhood on which the tuple is
zero. Thus K_x is zero. Apply 01B8 to the zero map into K on the ringed open U.
It gives a neighbourhood V of x on which every kernel section is locally zero;
sheaf uniqueness makes each such section zero. Kernels are computed sectionwise,
so p is injective on every W contained in V. Slice-site restriction and the
ringed open have the same sections and restriction maps. The empty tuple already
vanishes, so the argument includes r = 0 and the zero ring. -/
theorem exists_injective_neighbourhood_of_independent_free_epi
    (X : RingedSpace.{u}) (F : ringedSiteModules (moduleRings X))
    [F.IsFinitePresentation] (U : Opens X) (x : X) (hxU : x ∈ U) (r : ℕ)
    (p : SheafOfModules.free (R := (moduleRings X).over U)
      (ULift.{u} (Fin r)) ⟶ F.over U) [Epi p]
    (h : LinearIndependent (X.presheaf.stalk x) (fun j : Fin r ↦
      TopCat.Presheaf.germ F.val.presheaf U x hxU
        (((F.over U).freeHomEquiv p (ULift.up j)).val (op (Over.mk (𝟙 U)))))) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : Opens X) (hWV : W ≤ V),
        Function.Injective
          (p.val.app (op (Over.mk (homOfLE (hWV.trans hVU))))) := by
  sorry

end AlgebraicGeometry.RingedSpace
