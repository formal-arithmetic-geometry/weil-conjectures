/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Finprod

/-! # Well-definedness of the Euler characteristic

Source: Stacks Project, Varieties, Definition 0BEJ and the following paragraph
(blueprint: lem-pc-euler-characteristic-well-defined).

Cohomology is the right derived functor of module-valued global sections. Scalars are
restricted along the structure map `k → Γ(X, ⊤)`. The final clause expresses the integer
Euler sum as a finite sum, in addition to finite dimensionality and finite nonzero support.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace AlgebraicGeometry.Scheme

/-- Coherent cohomology on a proper scheme over a field is finite dimensional and nonzero
in only finitely many degrees; its alternating dimension sum is a finite sum of integers.
Source: Stacks Project, Varieties, Definition 0BEJ and the following paragraph
(blueprint: lem-pc-euler-characteristic-well-defined).

Proof:
1. The structure morphism to `Spec k` is proper, hence separated and of finite type
(def-weil-proper-morphism, def-weil-finite-type-morphism). The affine spectrum of a field
is quasi-compact and locally Noetherian (def-weil-affine-spectrum, pqf-def-locnoeth).
2. Thus X is locally Noetherian by pqf-lem-locnoeth-lft. Coherence implies quasi-coherence
by pqf-lem-coherent-ft-locnoeth (Stacks 01XZ and 01T6).
3. Apply lem-pc-coherent-hi over the Noetherian affine base Spec k (Stacks 02O6): every
cohomology group is finite over k, with scalars through the displayed structure map.
A finite generating family contains a basis, giving finite dimension
(def-weil-vector-space-dimension).
4. The same proper-cohomology result gives an integer bound on higher direct images
(Stacks 01XJ). By lem-pc-cohomology-sections-affine-base (Stacks 01XK), cohomology is
sections of these higher direct images, so it vanishes above that bound. Its nonzero
support is contained in a finite initial segment of the natural numbers.
5. Zero spaces have dimension zero. Therefore the alternating integer dimension terms
vanish outside that segment, and their finsum is the displayed finite sum, independent
of any larger truncation bound. This is the well-defined integer of Definition 0BEJ. -/
theorem eulerCharacteristic_wellDefined (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    (∀ i : ℕ, FiniteDimensional k
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F))) ∧
    Set.Finite {i : ℕ | ¬ IsZero ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F)} ∧
    ∃ n : ℕ,
      (∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F)) : ℤ)) =
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (Module.finrank k
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
          ((RingedSpace.moduleCohomology X.toRingedSpace i).obj F)) : ℤ) := by
  sorry

end AlgebraicGeometry.Scheme
