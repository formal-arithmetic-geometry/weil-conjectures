/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
import Sheaf.RingTheory.ColimitEventuallyFlat
import Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings
import Sheaf.RingTheory.FlatModInjective
import WeilConjectures.RingTheory.LocalizedBaseChangeQuotientFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Closed-fibre injectivity over an essentially finitely presented local algebra

Source: Stacks Project, Algebra, Tag 046Y (`lemma-mod-injective-general`), statement and proof
(blueprint: lem-trf-valuation-general-mod-injective).
-/

@[expose] public section

set_option autoImplicit false

universe u v p w z

namespace Algebra

/-- A map of finitely presented modules over an essentially finitely presented local algebra,
with flat target and injective closed fibre, is injective with flat cokernel. The algebra `P`
and submonoid `W` witness essential finite presentation; `IsLocalization W S` expresses the
localization up to its canonical isomorphism, compatibly with the `R`-algebra structures.

Source: Stacks Project, Algebra, Tag 046Y (`lemma-mod-injective-general`)
(blueprint: lem-trf-valuation-general-mod-injective).

Proof:
1. Simultaneously approximate `R`, `S`, both modules and the map by Noetherian local stages
   [lem-trf-local-module-arrow-noetherian-descent]. Descend the two presentation matrices and
   the matrix of the map together with its relation witnesses. This supplies commuting local
   ring diagrams, additive colimits, and transition and limit localization/base-change maps.
2. Apply [lem-weil-pbc-colimit-eventually-flat] to the target diagram. All its Noetherianity,
   finiteness, localization and colimit hypotheses come from step 1. The flat limit target
   gives one flat stage. Use [lem-weil-pbc-localized-base-change-quotient-flat] at the zero
   ideal to propagate flatness to every later stage, and restrict to that cofinal tail.
3. Write `k` for the residue field of `R`, and `kᵢ` for that of a stage `Rᵢ`. Over the fixed
   field `k`, put `Dᵢ = Sᵢ ⊗[Rᵢ] k` and `Pᵢ = Mᵢ ⊗[Rᵢ] k`. Tensor-over-quotient identifies
   these with the scalar extensions of the closed fibres
   [lem-weil-pbc-tensor-over-quotient-ring]. By localization/tensor commutation, `Dᵢ` is a
   localization of a finite type `k`-algebra [lem-weil-pbc-localization-tensor-over-base],
   hence Noetherian [lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-localization-noetherian]. The generators of `Mᵢ` tensor `1` generate `Pᵢ`;
   its comparison kernel is finite [lem-weil-pbc-noetherian-submodule-finite].
4. Tensor the actual transition localizations with `k`. This identifies `Dⱼ` and `Pⱼ` as
   localizations of `Dᵢ` and `Pᵢ`; the maps on pure tensors are the original transition
   maps tensor the identity [lem-weil-pbc-localization-tensor-over-base]. The varying-ring
   tensor/colimit theorem identifies their additive colimit with `M ⊗[R] k` and its actual
   comparison maps [lem-weil-pbc-filtered-colimit-tensor-varying-rings]. Use one common
   containing universe for the small index and all rings and modules.
5. The finite kernel at one stage and the localization transitions give injective source
   comparisons at every sufficiently late stage
   [lem-trf-localization-system-kernel-stabilization]: kill finitely many kernel generators
   at a common stage; every later kernel element is a fraction of an element of that kernel.
6. The extension `kᵢ → k` is faithfully flat
   [lem-weil-pbc-field-extension-base-change-faithfully-flat]. Universal injectivity embeds
   `Mᵢ / mᵢ Mᵢ` in its extension to `k`
   [lem-weil-pbc-faithfully-flat-universally-injective]. Composing with step 5 embeds it in
   `M / m M`. In the commuting closed-fibre square, injectivity of the limit map therefore
   implies injectivity of the stage map. No target comparison is assumed injective.
7. Apply the Noetherian local criterion [lem-weil-pbc-flat-mod-injective] at each sufficiently
   late stage, with finite source, flat target and injective closed-fibre map. It gives
   injectivity and flat cokernel at that stage.
8. Represent a kernel element of the limit map at a late stage. Its image is eventually zero
   by [lem-weil-pbc-filtered-colimit-modules-elementwise] on underlying abelian groups, viewed
   as integer modules. Compatibility and stage injectivity kill its later representative,
   proving injectivity of the limit map; no stage is identified with its colimit.
9. For a fixed late stage, tensor right exactness identifies its cokernel after extension to
   `S` with `N / u(M)`, sending `[y] ⊗ s` to `s [νᵢ(y)]`
   [lem-weil-pbc-tensor-right-exact]. The actual limit localization and step 7 give flatness
   over `R` by [lem-weil-pbc-localized-base-change-quotient-flat] at the zero ideal.
-/
theorem local_essentially_finite_presentation_mod_injective
    {R : Type u} {S : Type v} {P : Type p} {M : Type w} {N : Type z}
    [CommRing R] [CommRing S] [CommRing P] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Algebra.FinitePresentation R P] (W : Submonoid P) [IsLocalization W S]
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    [Module R M] [Module R N] [IsScalarTower R S M] [IsScalarTower R S N]
    [Module.FinitePresentation S M] [Module.FinitePresentation S N]
    (u : M →ₗ[S] N) [Module.Flat R N]
    (h_fibre : Function.Injective
      (Submodule.mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R N))
        (u.restrictScalars R)
        (Submodule.smul_top_le_comap_smul_top
          (IsLocalRing.maximalIdeal R) (u.restrictScalars R)))) :
    Function.Injective u ∧ Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) := by
  sorry

end Algebra
