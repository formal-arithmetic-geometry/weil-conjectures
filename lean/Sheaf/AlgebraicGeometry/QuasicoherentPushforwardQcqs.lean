/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize
import Sheaf.AlgebraicGeometry.Coherent

/-!
# Quasi-coherence of pushforward along a qcqs morphism

Source: Stacks Project, Schemes, Lemma 26.24.1, Tag 01LC
(blueprint: pqf-lem-pushforward-qcoh).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Pushforward along a quasi-compact, quasi-separated morphism preserves quasi-coherence.
Source: Stacks Project, Schemes, Lemma 26.24.1, Tag 01LC
(blueprint: pqf-lem-pushforward-qcoh).

Proof:
1. Work over an affine open `S₀ = Spec A` and set `X₀ = f⁻¹(S₀)`. Quasi-compactness
   (`def-weil-pbc-scheme-conventions`) supplies a finite affine cover `Uᵢ = Spec Bᵢ` of `X₀`.
   Quasi-coherence (`pqf-def-coherent`) identifies the restrictions with associated modules
   `Mᵢ`. Quasi-separatedness makes each overlap quasi-compact, by the relative diagonal,
   so choose finite covers of the overlaps by principal opens `Wᵢⱼₖ = D(gᵢⱼₖ)` in `Uᵢ`.
   Their section modules are the localizations `Nᵢⱼₖ = (Mᵢ)_{gᵢⱼₖ}`, using
   `pqf-lem-associated-sections-localize` and restriction of associated sheaves.
2. Sheaf gluing identifies sections on `X₀` with the kernel of the difference of
   restrictions from the finite product of the `Mᵢ` to the finite product of the `Nᵢⱼₖ`.
3. Pull these covers back to each principal open `D(a)` in `S₀`. The section-localization
   lemma (`pqf-lem-associated-sections-localize`) identifies the new two terms and map with
   localization over `A` of the old ones. Localization is exact and commutes with finite
   products, giving sections over `f⁻¹(D(a))` as sections over `X₀` localized at `a`.
4. These identifications commute with further localization because the maps are
   restrictions. Thus on the principal-open basis of `S₀` the pushforward is the sheaf
   associated to its module of sections on `X₀`, hence is quasi-coherent
   (`pqf-def-coherent`). Varying `S₀` proves the result. -/
theorem isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent := by
  sorry

end AlgebraicGeometry.Scheme.Modules
