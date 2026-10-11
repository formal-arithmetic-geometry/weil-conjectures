/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The torsion subsheaf and its torsion-free quotient

Source: Stacks Project, Divisors, Tags 0AXR and 0AXT
(blueprint: lem-sc-torsion-subsheaf-quotient).

The generic skyscraper has sections `F_eta` on opens containing the generic point and zero
on the empty open. It therefore realizes `j_* F_eta` for `j : Spec k(X) → X`.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The sections with zero generic germ form a quasi-coherent submodule, whose stalks are
exactly the torsion submodules and whose quotient is torsion-free. The inclusion is a kernel
of the canonical generic-germ morphism to the generic skyscraper `j_* F_eta`.
Source: Stacks Project, Divisors, Tags 0AXR and 0AXT
(blueprint: lem-sc-torsion-subsheaf-quotient).

Proof:
1. On every open take the kernel of the generic-germ map. The equivalences of
`lem-sc-torsion-sections-generic` identify these sections with torsion sections. The map to
`j_* F_eta` is `toSkyscraper` of the identity of the generic stalk. The generic-point morphism
is quasi-compact and quasi-separated, so `pqf-lem-pushforward-qcoh` gives quasi-coherence of
its pushforward. Then `lem-weil-pbc-quasi-coherent-module-kernel` gives quasi-coherence of T.
2. By `lem-weil-pbc-module-stalk-exact` the stalk inclusion is injective. A germ of T has a
representative with zero generic germ, hence is torsion by `lem-sc-torsion-sections-generic`.
Conversely a torsion germ has an annihilated representative after shrinking; the same lemma
makes its generic germ zero, so it belongs to T. This identifies the stalk image exactly.
3. The quotient is the cokernel of the inclusion and is quasi-coherent by
`lem-weil-pbc-quasi-coherent-module-cokernel-image`. Exactness of stalks from
`lem-weil-pbc-module-stalk-exact` identifies its stalk with F_x/T_x and gives local lifts.
A torsion quotient germ has a representative with zero generic germ by
`lem-sc-torsion-sections-generic`. Since T_eta = 0, a local lift to F also has zero generic
germ, hence lies in T, so its quotient germ is zero. Thus every quotient stalk is torsion-free.
-/
theorem torsion_subsheaf_quotient (X : Scheme.{u}) [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (T : X.Modules) (i : T ⟶ F),
      Mono i ∧ T.IsQuasicoherent ∧
      (∀ (U : X.Opens) (s : Γ(F, U)),
        (∃ t : Γ(T, U), i.app U t = s) ↔
          ∀ hη : genericPoint X ∈ U, F.presheaf.germ U (genericPoint X) hη s = 0) ∧
      (∀ (x : X) (s : F.presheaf.stalk x),
        s ∈ Set.range (i.stalkLinearMap x) ↔
          ∃ a : X.presheaf.stalk x, a ≠ 0 ∧ a • s = 0) ∧
      (∀ (x : X) (s : (cokernel i).presheaf.stalk x)
        (a : X.presheaf.stalk x), a ≠ 0 → a • s = 0 → s = 0) ∧
      ∃ h : i ≫ toSkyscraper
          (LinearMap.id : F.presheaf.stalk (genericPoint X) →ₗ[X.functionField]
            F.presheaf.stalk (genericPoint X)) = 0,
        Nonempty (IsLimit (KernelFork.ofι i h)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
