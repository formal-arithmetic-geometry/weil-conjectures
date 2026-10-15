/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.RingTheory.WeakEtaleRefinement
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso
import Sheaf.RingTheory.RetainedLocalizationProperties
import Sheaf.RingTheory.StrictWCoverProperties
import Sheaf.RingTheory.WeaklyEtaleField
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-! # Properties of the canonical weakly etale refinement

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1232;
Stacks Project, Tag 097Z (blueprint: thm-weil-pbc-weak-etale-refinement).
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.WeakEtaleRefinement

/-- For the specified refinement, `B → B'` is faithfully flat and ind-etale, and
`A → B'` is ind-etale. The latter map is the composite through `B`.
Source: blueprint order 1232; Stacks Project, Tag 097Z
(blueprint: thm-weil-pbc-weak-etale-refinement).

Proof:
1. Use `C`, `J`, and `D₀` from def-weil-pbc-weak-etale-refinement.
   By lem-weil-pbc-strict-w-cover, `C/A` is faithfully flat and ind-etale, its spectrum
   is w-local, and its maximal local rings are strictly henselian. Base-change stability
   in lem-weil-pbc-ind-etale-stability makes `D₀/C` weakly etale.
   Apply lem-weil-pbc-weak-etale-field to its fibres: their residue fields are algebraic
   over the base fields. Thus `T = V(JD₀)` consists of closed points of `D₀`.
   By lem-weil-pbc-retained-localization, `B'` is w-local, its closed points are `T`,
   its local rings there are unchanged, and `D₀ → B'` is ind-Zariski.
2. Every maximal ideal `n` of `B'` contracts to a maximal ideal `m` of `C`.
   By lem-weil-pbc-ind-etale-stability the composite `C → D₀ → B'` is weakly etale:
   its first map is a weakly etale base change, its second is ind-Zariski, hence
   ind-etale and weakly etale. The local map `C_m → B'_n` is therefore weakly etale
   and is an isomorphism by thm-weil-pbc-weak-etale-strict-local.
   Every prime lies below a maximal ideal; localizing this isomorphism again identifies
   all local rings of `C → B'`. Apply lem-weil-pbc-local-rings-ind-zariski, then compose
   with the ind-etale map `A → C`, to obtain ind-etaleness of `A → B'`.
3. Base change from `A → C` makes `B → D₀` ind-etale. Composition with `D₀ → B'`
   makes `B → B'` ind-etale and flat. The closed points `V(J)` surject onto `Spec A`
   by lem-weil-pbc-strict-w-cover. For a prime of `B`, choose a closed point of `C`
   over its contraction to `A`; the tensor product of their residue fields over the
   common residue field is nonzero, so it has a prime. This gives a point of `T`
   over the chosen prime of `B`. The base-change tool
   lem-weil-pbc-faithfully-flat-base-change also preserves the faithful flatness of
   `A → C` in `B → D₀`; the retained-point argument is needed after `D₀ → B'`.
   All these points are retained in `Spec B'`, so `Spec B' → Spec B` is surjective.
   Apply lem-weil-pbc-flat-surjective-spectrum-faithfully-flat to conclude faithful
   flatness of `B → B'`. -/
theorem properties (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hweak : Algebra.WeaklyEtale A B) :
    (algebraMap B (algebra A B hweak)).FaithfullyFlat ∧
    (algebraMap B (algebra A B hweak)).IndEtale ∧
    ((algebraMap B (algebra A B hweak)).comp (algebraMap A B)).IndEtale := by
  sorry

end PrincipalWLocalization.WeakEtaleRefinement
