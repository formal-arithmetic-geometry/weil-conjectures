/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Kernel finiteness from a chosen local generating family

Source: Stacks Project, Modules, Lemma 01BY (2), proof, second paragraph;
Lemma 01B7 (1) and Definition 01B5.
(blueprint: lem-weil-pbc-finite-type-kernel-local-generators).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- If the kernels of the composites with a chosen local free epimorphism are
finite type, then the original kernel is finite type. No coherence assumption
or finiteness assumption on the chosen generating families is needed.
Source: Stacks Project, Modules, Lemma 01BY (2), proof, second paragraph;
Lemma 01B7 (1) and Definition 01B5.
(blueprint: lem-weil-pbc-finite-type-kernel-local-generators).

Proof: On the cover q.X, put p = (q.generators i).π and L = kernel (p ≫ φ.over _).
The morphism kernel.ι (p ≫ φ.over _) ≫ p factors through kernel (φ.over _).
This factor is epi: a section killed by φ locally lifts through the epi p;
each lift is killed by the composite and therefore lies in L. As L is finite
type, its quotient kernel (φ.over _) is finite type by pushing forward local
finite generators. Restriction computes kernels sectionwise, so this is the
restriction of kernel φ. Refine the cover q.X by the finite generating covers
of these local kernels. Cover transitivity makes this a cover of U, and
forgetting the intermediate slice identifies its finite families with local
finite generators of kernel φ. Thus kernel φ is finite type. Empty covers of
an empty open and zero generating families satisfy the same argument. -/
theorem finiteType_kernel_local_generators (X : RingedSpace.{u})
    (U : Opens X) {F H : SheafOfModules.{u} ((moduleRings X).over U)}
    (φ : F ⟶ H) (q : SheafOfModules.LocalGeneratorsData.{u, u, u, u} F)
    (h : ∀ i : q.I, (kernel ((q.generators i).π ≫ φ.over (q.X i))).IsFiniteType) :
    (kernel φ).IsFiniteType := by sorry

end AlgebraicGeometry.RingedSpace
