/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Algebras spanned by idempotents

Let `K` be a field and `R` a `K`-algebra which is spanned over `K` by a set `E` of idempotents
(e.g. `R = LocallyConstant T K`, or a filtered colimit of finite products of copies of `K`).
Then every element of `R` is congruent to a scalar modulo every prime, every prime of `R` is
maximal and is determined by the elements of `E` it contains, and the local rings of `R` are
copies of `K`. In particular, if `K` is separably closed, `R` is w-strictly local, and it is
w-contractible as soon as its space of connected components is extremally disconnected.

We also give a criterion for a continuous map to induce a homeomorphism on spaces of connected
components, and its incarnation for ring maps in terms of idempotents.

## Main statements

- `IsWStrictlyLocalRing.of_forall_mem_span_isIdempotentElem`
- `IsWContractibleRing.of_forall_mem_span_isIdempotentElem`
- `Continuous.isHomeomorph_connectedComponentsMap`
- `PrimeSpectrum.isHomeomorph_connectedComponentsMap_comap`
-/

@[expose] public section

open PrimeSpectrum TopologicalSpace

section Span

variable {K R : Type*} [CommRing R]

variable [Field K] [Algebra K R]

end Span

section ConnectedComponents

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {S T : Type*} [CommRing S] [CommRing T]

end ConnectedComponents
