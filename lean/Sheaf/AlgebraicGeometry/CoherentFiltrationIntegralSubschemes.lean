/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Limits
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentGenericPointIdealInclusion
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentSupportPowerIdealKills
import Sheaf.AlgebraicGeometry.CoherentSupportUnionExactSequence
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# A coherent filtration supported on integral closed subschemes

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.3, Tag 01YF
(blueprint: lem-weil-pbc-coherent-filtration-integral-subschemes).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a Noetherian scheme has a finite filtration by coherent submodules
whose successive quotients are pushforwards of nonzero coherent ideals on integral closed
subschemes. A sheaf of ideals of `𝒪_Z` is a `Z.IdealSheafData`, viewed as an `𝒪_Z`-module by
`IdealSheafData.toModules`; it is nonzero (`≠ ⊥`) and its module is coherent.
Quotients are cokernels of the canonical subobject inclusions.

Source: Stacks Project, Cohomology of Schemes, Tag 01YF
(blueprint: lem-weil-pbc-coherent-filtration-integral-subschemes).

Proof:
1. Coherent modules are closed under kernels, cokernels and finite sums on a locally
Noetherian scheme, and have closed support (pqf-lem-coherent-ft-locnoeth,
lem-weil-pbc-coherent-kernel-cokernel-locnoeth,
lem-weil-pbc-finite-type-module-support-closed). Stalk exactness and detection of isomorphisms
are lem-weil-pbc-module-stalk-exact and lem-weil-pbc-module-iso-on-stalks.
2. Call a module good if it admits this filtration. The zero module is good. Pull back a
filtration of a quotient and concatenate with a filtration of the submodule to show goodness
is closed under extensions, using the stalk lemmas of step 1.
3. Choose a minimal closed support of a nongood coherent module by
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Its support is nonempty.
4. A reducible support is a union of two proper closed subsets. Apply
lem-weil-pbc-coherent-support-union-exact-sequence and minimality, contradicting step 2.
5. Give this irreducible support its reduced induced structure, an integral closed subscheme
(lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-scheme-sober). Its ideal J has
vanishing locus the support and generic stalk equal to the ambient maximal ideal, by
lem-weil-pbc-ideal-module-product-stalk and lem-weil-pbc-basic-open-function.
6. Some power of J kills the module (lem-weil-pbc-coherent-support-power-ideal-kills).
The J-adic filtration has coherent successive quotients annihilated by J, by
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and the stalk lemmas. If all these
quotients were good, step 2 would give a contradiction. Replace the module by a nongood
quotient; minimality ensures it has the same support.
7. Apply lem-weil-pbc-coherent-generic-point-ideal-inclusion to embed the pushforward of a
finite sum of a coherent ideal into this module, isomorphically near the generic point.
Closed pushforward preserves coherence (lem-weil-pbc-closed-immersion-coherent-equivalence;
local Noetherianity follows from lem-weil-pbc-immersion-base-change-lft and
pqf-lem-locnoeth-lft). Pushforward commutes with finite sums. The generic stalk is nonzero,
so the number of summands and the ideal are nonzero (lem-weil-pbc-closed-pushforward-stalks).
8. The partial sums filter the image with quotients the pushforward of that ideal. The
cokernel has strictly smaller support because its generic stalk vanishes. It is good by
minimality, and then step 2 makes the original module good, the final contradiction. -/
theorem exists_coherent_filtration_integral_subschemes
    (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      (∀ k : Fin (m + 1), RingedSpace.IsCoherent X.toRingedSpace (c k : X.Modules)) ∧
      ∀ j : Fin m, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ I : Z.IdealSheafData,
          I ≠ ⊥ ∧ RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
          Nonempty (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)) ≅ (pushforward i).obj I.toModules) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
