/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.EssentialFiniteness
import Sheaf.TraceFormula.ValuationFlatFiniteModulePresentation
import Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective
import Sheaf.SecTraceFormula.ValuationFiniteModuleFpReduction

/-! # Finite presentation and rigidity of a fibre-injective source

Source: Stacks Project, More on Morphisms, Tag 0GSG
(`lemma-mod-injective-valuation-ring`), second and third reduction paragraphs
(blueprint: lem-trf-valuation-fibre-injective-source-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v p n m e

namespace Algebra

/-- A finite source mapping injectively on the closed fibre into a finite, base-flat target
is finitely presented. Every finitely presented surjective approximation of the source
which induces an isomorphism on the closed fibre is itself an isomorphism.
The algebra `P` and submonoid `W` witness essential finite presentation of `S` over `A`.
Bijectivity of a linear map expresses that it is a linear isomorphism.

Source: Stacks Project, More on Morphisms, Tag 0GSG
(`lemma-mod-injective-valuation-ring`), second and third reduction paragraphs
(blueprint: lem-trf-valuation-fibre-injective-source-presentation).

Proof:
1. Finite presentation of `P` implies finite type, so its localization `S` is essentially
   of finite type, using def-weil-pbc-finitely-presented-algebra,
   def-weil-pbc-finite-type-algebra and def-weil-pbc-essentially-finite-type-algebra.
2. Apply lem-trf-valuation-flat-finite-module-presentation to the finite, `A`-flat module
   `M` over the local essentially finite type algebra `S`. Thus `M` is finitely presented.
3. For rigidity, let `E` and `v` satisfy the second conclusion's assumptions. The closed
   fibre of `u` composed with `v` is injective. Apply
   lem-trf-valuation-general-mod-injective to this composite: `E` and `M` are finitely
   presented and `M` is `A`-flat. Its injectivity implies injectivity of `v`. Together
   with surjectivity this makes `v` bijective; its inverse is linear by uniqueness of
   preimages. This argument does not assume finite presentation of `N`.
4. Apply lem-trf-valuation-finite-module-fp-reduction to `N`, obtaining a nonempty
   filtered system of finitely presented modules with surjective transitions, colimit
   `N`, and eventually isomorphic closed fibres. Each cocone map is surjective: represent
   an element of the colimit by finitely many stage elements, pass to a common receiving
   stage with the chosen stage, and lift their sum along the surjective transition.
   At a stage with unchanged closed fibre, Step 3 identifies that module with `N`.
5. Compose a finite free presentation of that stage with its linear isomorphism to `N`.
   Its surjectivity and kernel are preserved, so this is a finite presentation of `N`,
   in the sense of def-sc-finitely-presented-module.
-/
theorem valuation_fibre_injective_source_presentation
    {A : Type u} {S : Type v} {P : Type p} {N : Type n} {M : Type m}
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    [CommRing P] [Algebra A P] [Algebra P S] [IsScalarTower A P S]
    [Algebra.FinitePresentation A P] (W : Submonoid P) [IsLocalization W S]
    [AddCommGroup N] [AddCommGroup M] [Module S N] [Module S M]
    [Module A N] [Module A M] [IsScalarTower A S N] [IsScalarTower A S M]
    [Module.Finite S N] [Module.Finite S M] (u : N →ₗ[S] M) [Module.Flat A M]
    (h_fibre : Function.Injective
      (Submodule.mapQ
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))
        (u.restrictScalars A)
        (Submodule.smul_top_le_comap_smul_top
          (IsLocalRing.maximalIdeal A) (u.restrictScalars A)))) :
    Module.FinitePresentation S N ∧
      ∀ (E : Type e) [AddCommGroup E] [Module S E] [Module A E]
        [IsScalarTower A S E] [Module.FinitePresentation S E] (v : E →ₗ[S] N),
        Function.Surjective v →
        Function.Bijective
          (Submodule.mapQ
            (IsLocalRing.maximalIdeal A • (⊤ : Submodule A E))
            (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
            (v.restrictScalars A)
            (Submodule.smul_top_le_comap_smul_top
              (IsLocalRing.maximalIdeal A) (v.restrictScalars A))) →
        Function.Bijective v := by
  sorry

end Algebra
