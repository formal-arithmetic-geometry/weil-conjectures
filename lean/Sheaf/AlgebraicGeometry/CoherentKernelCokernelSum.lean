/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeSubKernel
import Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension

/-! # Closure properties of coherent modules

Source: Stacks Project, Modules, Tag 01BY, parts (3) and (4)
(blueprint: lem-weil-pbc-coherent-modules-kernel-cokernel-sum).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits ZeroObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.RingedSpace

/-- Coherent modules are closed under kernels, cokernels, two out of three in short exact
sequences, finite direct sums (including the zero module), and isomorphisms.
Source: Stacks Project, Modules, Tag 01BY, parts (3) and (4)
(blueprint: lem-weil-pbc-coherent-modules-kernel-cokernel-sum).

Proof:
1. Isomorphisms transport finite generators and identify kernels of maps from finite free
modules. The zero module is coherent: its relations are finite free modules. Finite type
is local on open covers, and restriction to opens preserves kernels, epimorphisms and
exactness by `lem-weil-pbc-ringed-space-module-exactness-local-lifting` and
`lem-weil-pbc-module-restriction-open-immersion-colimits`.
2. For a map of coherent modules, its kernel is of finite type by
`lem-weil-pbc-coherent-finite-type-sub-kernel` (2), and is coherent as a finite type
submodule of its coherent source by part (1) of that lemma.
3. The cokernel and image are finite type by `lem-weil-pbc-module-finite-type-image-extension`.
The image is the kernel of the cokernel projection, giving its short exact sequence with
the target and cokernel (`lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`).
4. Locally lift any finite tuple of cokernel sections to the target and choose finitely many
image generators. The map from the sum of the two finite free modules to the target has
finite type kernel by coherence. Apply `lem-weil-pbc-snake-lemma-abelian` to the split free
sequence above the image-target-cokernel sequence. Its kernel surjects onto the relations
of the chosen cokernel sections (`lem-weil-pbc-abelian-exact-epi-cokernel`), so those
relations have finite type. Thus the cokernel is coherent.
5. When the middle term of a short exact sequence is coherent, the other coherent term
makes the remaining term a coherent kernel or cokernel, using
`lem-weil-pbc-abelian-short-exact-kernel` and `lem-weil-pbc-abelian-exact-epi-cokernel`.
6. If the end terms are coherent, the middle term is finite type by
`lem-weil-pbc-module-finite-type-image-extension`. For any finite tuple in the middle term,
apply the snake lemma to the sequence with top row zero, finite free, finite free and
identity, and bottom row the given short exact sequence restricted to its open. Its
relations are the kernel of a map from the relations in the last term to the first term.
The former is finite type and the latter coherent, by
`lem-weil-pbc-coherent-module-local-on-open-cover`; hence the kernel is finite type by
`lem-weil-pbc-coherent-finite-type-sub-kernel` (2). Exactness identifies this kernel with
the middle relations using `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift`.
7. Induct on the number of summands, starting with the coherent zero module. The split
short exact sequence for a binary biproduct and step 6 give the induction step.
Isomorphism invariance is step 1. -/
theorem coherent_kernel_cokernel_sum (X : RingedSpace.{u}) :
    (∀ (F G : SheafOfModules.{u} (moduleRings X)) (f : F ⟶ G),
      IsCoherent X F → IsCoherent X G →
        IsCoherent X (kernel f) ∧ IsCoherent X (cokernel f)) ∧
    (∀ (S : ShortComplex (SheafOfModules.{u} (moduleRings X))), S.ShortExact →
      (IsCoherent X S.X₁ → IsCoherent X S.X₂ → IsCoherent X S.X₃) ∧
      (IsCoherent X S.X₁ → IsCoherent X S.X₃ → IsCoherent X S.X₂) ∧
      (IsCoherent X S.X₂ → IsCoherent X S.X₃ → IsCoherent X S.X₁)) ∧
    (∀ (r : ℕ) (F : Fin r → SheafOfModules.{u} (moduleRings X)),
      (∀ i : Fin r, IsCoherent X (F i)) → IsCoherent X (⨁ F)) ∧
    IsCoherent X (0 : SheafOfModules.{u} (moduleRings X)) ∧
    (∀ (F G : SheafOfModules.{u} (moduleRings X)) (_e : F ≅ G),
      IsCoherent X F → IsCoherent X G) :=
  sorry

end AlgebraicGeometry.RingedSpace
