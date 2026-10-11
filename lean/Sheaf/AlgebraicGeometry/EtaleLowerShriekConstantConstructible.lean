/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Constructibility of extension by zero of a finite constant module sheaf

Source: Stacks Project, Tag 03S8, Lemma 59.73.1(3)
(blueprint: lem-weil-pbc-etale-free-sheaf-constructible).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Extension by zero of a finite constant module sheaf along an etale morphism between
quasi-compact quasi-separated schemes is constructible. Sheaves valued in `ModuleCat Λ`
encode module sheaves over the constant ring sheaf `Λ_X`. The functor `etaleLowerShriek`
sheafifies the presheaf whose value on `V` is the direct sum over `Hom_X(V, U)` of the
constant module sheaf's sections on `V`; restriction reindexes by composition and restricts
sections. Thus its value here is the node's `j_! underline M_U`, including the free
rank-one case `M = Λ`.

Source: Stacks Project, Tag 03S8, Lemma 59.73.1(3)
(blueprint: lem-weil-pbc-etale-free-sheaf-constructible).

Proof:
1. Choose a finite partition of `X` into constructible locally closed subschemes such
   that the base change of `j` to each stratum is finite etale, by Tag 03S9
   (`lem-weil-pbc-etale-stratified-finite`).
2. Pull back the extension to each stratum. Tag 03S6 identifies this pullback with the
   extension of the constant module sheaf on the base-changed source
   (`lem-weil-pbc-etale-shriek-base-change-modules`).
3. For each finite etale base change, extension by zero agrees with direct image,
   by Tag 03S7 (`lem-weil-pbc-etale-shriek-star-finite-modules`).
4. This direct image is finite locally constant by Tag 095B
   (`lem-weil-pbc-etale-finite-pushforward-locally-constant`).
5. The partition therefore witnesses constructibility, as in
   `def-weil-pbc-etale-constructible-sheaf` and `def-weil-pbc-etale-sheaves` on the site
   `def-weil-pbc-etale-site`. Finiteness of `Λ` supplies the Noetherian coefficient
   hypothesis of Tag 03S8; finiteness of `M` supplies finite constant values.
-/
theorem isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
    {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (j : U ⟶ X) [Etale j] (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsConstructibleEtaleModuleSheaf
      ((Etale.etaleLowerShriek Λ j inferInstance).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := sorry

end AlgebraicGeometry.Scheme
