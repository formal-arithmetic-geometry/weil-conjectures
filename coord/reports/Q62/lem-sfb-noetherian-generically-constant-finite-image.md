## Worker report

The module `lean/Sheaf/RingTheory/NoetherianGenericallyConstantFiniteImage.lean`
introduces `WeilConjectures.finite_image_of_generically_constant` with a `sorry` proof.
It states the finite-image consequence for an arbitrary function
`f : PrimeSpectrum A → T`, where `A` has `[CommRing A] [IsNoetherianRing A]` and
`T` is an arbitrary type. The theorem conclusion is a conjunction: for every ideal
`J`, the image of `{p | J ≤ p.asIdeal}` under `f` is finite, and the full range of
`f` is finite.

The hypothesis is rendered by
`(∀ (I : Ideal A), I.IsPrime → ∃ b : A, b ∉ I ∧ ∃ t : T, ∀ p : PrimeSpectrum A,
I ≤ p.asIdeal → b ∉ p.asIdeal → f p = t)`. Thus `I.IsPrime` is exactly the
prime-ideal condition; `b ∉ I` is the required element of the complement; and the
last two implications say that `f` is equal to `t` on `V(I) ∩ D(b)`. The first
conclusion clause is rendered by
`∀ (J : Ideal A), (f '' {p : PrimeSpectrum A | J ≤ p.asIdeal}).Finite`, which is
exactly `{f(p) : p ∈ V(J)}` finite. The second clause is `(Set.range f).Finite`,
the stated “in particular” conclusion.

The statement dependencies are the existing Mathlib declarations recorded by their
nodes: `IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs` (node
`def-weil-pbc-noetherian-ring`) and the spectrum construction `AlgebraicGeometry.Spec`
from `Mathlib.AlgebraicGeometry.Scheme` (node `def-weil-affine-spectrum`). The Lean
signature uses the corresponding Mathlib `PrimeSpectrum A` type and its `asIdeal`
field. Proof dependencies in the node are the Mathlib Noetherian finite-module ACC
lemmas `isNoetherian_of_isNoetherianRing_of_finite` in
`Mathlib.RingTheory.Noetherian.Basic`, `set_has_maximal_iff_noetherian` and
`monotone_stabilizes_iff_noetherian` in `Mathlib.RingTheory.Noetherian.Defs`,
and `Module.Finite` in
`Mathlib.RingTheory.Finiteness.Defs`, imported as proof dependencies; no additional declarations are introduced by this
statement module.

Edge cases checked: `CommRing` permits the zero ring, whose prime spectrum is empty;
then every displayed image is empty and finite. `T` is an unconstrained `Type v`, so
an empty target is allowed whenever a function exists (necessarily with empty domain).
No nonemptiness, continuity, separatedness, or characteristic hypothesis was added.
The ideal `J` is arbitrary, including `⊥` and `⊤`; `J = ⊤` gives the empty closed
subset, while `J = ⊥` gives the full spectrum and the range clause.

Searches for an existing notion or theorem were made before writing:

- `msearch.py ... leanfinder "An arbitrary function on the prime spectrum of a Noetherian ring has finite image if it is constant on a principal dense open in every prime closed subset"`: returned `PrimeSpectrum.finite_setOf_isMin`, Noetherian-space instances, and minimal-prime finiteness, but no theorem about an arbitrary generically constant function.
- `msearch.py ... leansearch "A function on a Noetherian prime spectrum generically constant on each prime closed set has finite range"`: returned `IsLocallyConstant.range_finite`, `LocallyConstant.range_finite`, and finite-minimal-prime results; none has this hypothesis or conclusion.
- `msearch.py ... loogle "PrimeSpectrum, Set.Finite"`: returned finite minimal-prime, retrocompactness, and quasi-finite-spectrum declarations, none matching this statement.
- `msearch.py ... grep "(generically.*constant|finite.*range|range.*finite)" RingTheory/Spectrum`: found only unrelated finite-range and spectrum-topology lemmas.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for generically-constant finite-image names found no duplicate declaration; the only related hits concern different generic-finiteness statements.
- `grep` of the item id and `rg` of the Stacks labels found no existing Lean attachment and confirmed the source places Tag 0ASY, Tag 00IK, and Tag 00FR recorded in the node.

The file was compiled with `scompile.py` and produced no errors or warnings other than the
expected `sorry` declaration warning. No statement correction or `STATEMENT-DISPUTED`
flag is needed.

## Second reading by Q62

I performed a separate self-review pass with the node and module open; no other agent
was started, as required by the dispatcher brief. The ring hypothesis is exactly the pair
`[CommRing A] [IsNoetherianRing A]`; `T` remains arbitrary and `f` has the exact
prime-spectrum domain. The module quantifies over every prime ideal `I`, requires
`b ∉ I`, and requires constancy precisely on primes satisfying both `I ≤ p.asIdeal`
and `b ∉ p.asIdeal`. It quantifies over every ideal `J` and renders its closed-set
image as a finite `Set.image`, then includes the separate finite-range clause.
The zero-ring and empty-target cases remain represented because no `Nonempty` or
`Nontrivial` instance is present. I found no mismatch and made no changes.

Validation: the final module at the RingTheory path passed `scompile.py` cleanly.
The Lean record changes only the item’s `lean` field. The stage-2 independent
maintainer review is separate from the self-review above.
