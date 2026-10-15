/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.ModificationExtensionZero
import Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Constructibility transfers across a proper modification

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lem-finrepair-modification-c.md`, statement and proof
(blueprint: lem-finrepair-modification-c).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Property `C` transfers from a proper modification and the reduced closed complement
of the open where it is an isomorphism. The reduced closed complement is represented by
any reduced closed immersion `i` with image the complement of `U`; its finite-type
structure over `k` and coefficient convention are inherited from `X`.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-finrepair-modification-c.md`,
statement and proof (blueprint: lem-finrepair-modification-c).

Proof plan:
1. Fix a constructible module sheaf `F` and put `G = F|U`, `H = i⁻¹F`.
   Constructible pullback (`prop-constructible-pullback`) and open-closed localization
   (`lem-weil-pbc-open-closed-short-exact`) give `0 → j_!G → F → i_*H → 0`.
2. Over `U`, the pullback of `π` is an isomorphism. Pull `G` back to that open of `Y`.
   Extension by zero is constructible (`lem-fin-extension-by-zero`). The canonical
   adjunction isomorphism and positive-degree acyclicity of
   `lem-finrepair-modification-extension-zero` identify its direct image with `j_!G`.
3. The composition spectral sequence (`lem-weil-pbc-grothendieck-spectral-sequence`)
   has only its bottom row, so `R^q f_* j_!G ≅ R^q(fπ)_* j'_!G'`. For each total
   degree the finite abutment filtration has just this nonzero graded piece.
   The hypothesis `C(fπ)` makes these sheaves `A_q` constructible.
4. Closed-immersion acyclicity (`lem-fin-closed-immersion`) and the same spectral
   sequence give `B_q = R^q f_* i_*H ≅ R^q(fi)_*H`, constructible by `C(fi)`.
5. Enough injectives (`lem-weil-pbc-module-sheaves-enough-injectives`), left exact
   direct image (`lem-weil-pbc-module-direct-image-left-exact`), and the full long
   exact sequence (`lem-weil-pbc-derived-functor-long-exact`) give
   `B_(q-1) → A_q → R^q f_*F → B_q → A_(q+1)` for `q > 0`.
   For `q = 0` this starts with `0 → A_0 → f_*F → B_0 → A_1`.
6. Factoring through images gives a short exact sequence with outer terms
   `coker(B_(q-1) → A_q)` and `ker(B_q → A_(q+1))`. In degree zero the first
   term is `A_0`, so no negative derived functor is needed.
7. Kernel, cokernel and extension closure (`thm-constructible-serre`) make
   `R^q f_*F` constructible for every `q : ℕ`. This is `C(f)` by
   `def-finrepair-property-c`, without any uniform bound or vanishing assertion. -/
theorem hasConstructibleHigherDirectImages_of_modification
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [S.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (hZ : IsSmoothBaseChangeCoefficients N Λ Z)
    (f : X ⟶ S) (π : Y ⟶ X) [IsProper f] [IsProper π]
    [f.IsOver (Spec (.of k))] [π.IsOver (Spec (.of k))]
    (U : X.Opens) [IsIso (pullback.snd π U.ι)]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z] [i.IsOver (Spec (.of k))]
    (_hi : Set.range i.base = (U : Set X)ᶜ)
    (hπ : HasConstructibleHigherDirectImages k N Λ hY hS (π ≫ f))
    (hi : HasConstructibleHigherDirectImages k N Λ hZ hS (i ≫ f)) :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  sorry

end AlgebraicGeometry.Etale
