/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Affine sections of coherent formal modules form adic towers

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, affine reduction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Affine global sections carry a coherent formal system to a tower of finite
A-modules with the algebraic annihilation and transition-kernel conditions.
This statement concerns only finite-level sections, with no inverse limit.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, first paragraph;
Schemes, Tags 01I7 and 01IB.
(blueprint: lem-weil-pbc-coherent-formal-module-affine-sections-adic).

Proof: Spec A is locally Noetherian. Coherence is consequently equivalent to being
quasi-coherent and of finite type; affine sections of a quasi-coherent finite-type
module are finite over A. For each positive power of J, the affine sections formula
for ideal products identifies its product with a quasi-coherent module with
I^(n+1) times its sections. Apply this to the zero product in the formal-system
annihilation condition, obtaining the asserted zero submodule. The same affine
formula says that the quotient projection onto sections of F_(n+1)/J^(n+1)F_(n+1)
is surjective with kernel I^(n+1) times the source sections. The defining quotient
isomorphism of the formal system identifies this quotient with F_n and its quotient
projection with the successor transition. Apply the global-sections functor to this
isomorphism. Its invertible map preserves surjectivity and does not change the kernel.
Finally transport scalars along Γ(Spec A, O) = A; hJ identifies the ideal with I
under this transport, including all its powers. -/
theorem coherentFormalModule_affine_sections_adic (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) :
    let T := F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A)
    (∀ n : ℕ, Module.Finite A (T.obj (op n))) ∧
    (∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule A (T.obj (op n))) = ⊥) ∧
    (∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I ^ (n + 1) • (⊤ : Submodule A (T.obj (op (n + 1))))) := by sorry

end AlgebraicGeometry
