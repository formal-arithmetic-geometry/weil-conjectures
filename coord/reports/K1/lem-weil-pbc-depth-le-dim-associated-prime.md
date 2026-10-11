## Worker report

The module `lean/Sheaf/RingTheory/DepthLeDimAssociatedPrime.lean` states
`IsLocalRing.depth_le_ringKrullDim_quotient_of_annihilator`. Its hypotheses are rendered as follows:
`{R : Type u} [CommRing R]` is a commutative ring, `[IsNoetherianRing R]` is the
Noetherian hypothesis, and `[IsLocalRing R]` is the local-ring hypothesis. The finite
module is `{M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]`.
The prime ideal is `(p : Ideal R)` with `(hp : p.IsPrime)`. The associated-prime
witness is `(z : M)` and its annihilator equality is
`(hAnn : {a : R | a • z = 0} = p)`. The conclusion
`(IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)` renders
`dim(R/p) ≥ depth(M)`, using Mathlib's `ringKrullDim` and the project's
`IsLocalRing.depth`.

Dependencies used: `Sheaf.RingTheory.Depth`, declarations
`IsLocalRing.depth`; `Mathlib.RingTheory.Noetherian.Defs`, declaration
`IsNoetherianRing`; and `Mathlib.RingTheory.KrullDimension.Basic`, declaration
`ringKrullDim`. The quotient `R ⧸ p` is the standard ideal quotient ring.

Edge cases checked: the witness condition implies the associated element need not
be separately assumed nonzero; `p.IsPrime` excludes `p = ⊤`, so the quotient is
nontrivial. The depth definition handles the zero module and the infinite-depth
case, while `WithBot ℕ∞` permits finite or infinite Krull dimension. Universes `u`
and `v` are explicit.

Searches for an existing statement/definition: `msearch.py leanfinder` for “depth of
a finite module over a Noetherian local ring bounded by dimension of quotient at an
associated prime” (no match); `msearch.py loogle` for `depth, ringKrullDim,
associatedPrimes` (no match); grep of Mathlib `associatedPrimes.*depth` and
`ringKrullDim.*depth` (no combined declaration); `rg` over `WeilConjectures/`
for the item and depth-associated-prime statements (no match); `rg` over
`lean/Sheaf` found only this node's downstream use and the separate
`AssociatedPrimeMinimalOfDepth` statement. Thus no existing declaration states this
lemma.

No statement dispute or node fault.

## Earlier second reading (a previous round; superseded)

The node's Noetherian local ring, finite module, prime ideal, annihilator witness,
and dimension/depth inequality each appear in the module signature. The module uses
`p.IsPrime` for “prime ideal”, `hAnn` for exactly the displayed annihilator set, and
casts depth to `WithBot ℕ∞` so it compares with `ringKrullDim (R ⧸ p)`. No hypothesis
or conclusion clause is omitted or strengthened.

## Second reading by K1

I independently read the node, its seven proof steps, the sandbox module, and
Stacks algebra.tex at 0BK4 (17985–18020), 00LA (15108–15115), and 00LI
(17766–17794), read over SSH from the project server because literature is absent
from this clone. The source has exactly local Noetherian R and finite M; its
associated-prime definition is an element with prime annihilator. No additional
standing hypothesis is needed.

Object/hypothesis/conclusion inventory and verdicts:

- Commutative ring R: `{R : Type u} [CommRing R]`; exact, no field assumption.
- Noetherian R: `[IsNoetherianRing R]`; exact. I opened the dependency node and
  Mathlib Noetherian/Defs.lean:196: this is `IsNoetherian R R`, all ideals FG.
- Local R with its unique maximal ideal: `[IsLocalRing R]`; exact. Mathlib
  LocalRing/Defs.lean:30 is the standard nontrivial local-ring predicate;
  `IsLocalRing.depth` uses its `maximalIdeal R`. No separate choice of maximal
  ideal is necessary.
- Finite R-module M: `{M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M]`; exact. I read def-weil-finitely-generated-module in
  sec-smooth-purity and Mathlib Finiteness/Defs.lean:117: `Module.Finite` means
  the top submodule is FG, not finiteness of the underlying set.
- Prime ideal p: `(p : Ideal R) (hp : p.IsPrime)`; exact, no maximality required.
- Associated witness z: `(z : M)`; exact. Universal quantification over witnesses
  is equivalent to the node's implication for every p having such a witness,
  because the conclusion is independent of z.
- Annihilator equality: `(hAnn : {a : R | a • z = 0} = p)`; exactly the node's
  displayed set. Ideal-to-set coercion denotes the same ideal, not a private
  definition of associated primes.
- Entire conclusion: `(IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤
  ringKrullDim (R ⧸ p)`; exactly dim(R/p) ≥ depth(M). I opened the recorded
  `Sheaf.RingTheory.Depth` module: `Ideal.depth` is infinity when I•top=top,
  otherwise the supremum of lengths of `RingTheory.Sequence.IsRegular` lists in
  I, and local depth uses the maximal ideal. This agrees with 00LI. The recorded
  dimension declaration, Mathlib KrullDimension/Basic.lean:30, is the supremum
  of strict prime-chain lengths. Casting into WithBot preserves order and
  infinity. The conclusion adds no assertion about finiteness.

Edge cases: p.IsPrime makes p proper, so hAnn forces z ≠ 0 and M ≠ 0;
therefore zero M and an empty set of associated primes are correctly vacuous,
with no extra Nontrivial M instance. A zero ring has no prime witness (and is
not local in the node's exactly-one-maximal-ideal sense). Depth zero and a
length-zero prime chain are included. No characteristic constraint or fixed
finite dimension is assumed. Independent universes u/v cover all rings and
modules. Scheme and index-set edge cases are not objects of this lemma.

Independent searches used different wording: msearch.py leanfinder query
`depth ringKrullDim quotient annihilator associated prime` found eight dimension
and support-dimension results, including
`Module.supportDim_eq_ringKrullDim_quotient_annihilator` and dimension-drop
lemmas; none bounds depth at every associated prime. Loogle query
`depth ringKrullDim associatedPrimes` found zero hits (unknown depth in its
index). LeanSearch query `The depth of a finitely generated module is bounded
by dimension of the quotient by a prime annihilator of an element` returned
service unavailable; this is not an absence verdict. The other search kinds
succeeded. Independent rg on pinned Mathlib and WeilConjectures for
`associatedPrimes.*depth|depth.*associatedPrimes|ringKrullDim.*depth` found no
combined declaration. rg on project lean/Sheaf for depth/associated-prime names
found the separate AssociatedPrimeMinimalOfDepth lemma and its use of the depth
bound, not an existing version of this item. The full new declaration name has
no collision. No missing notion, new node, dependency module, or statement
correction is needed.

Mismatch repaired: the original proof docstring only summarized induction and
omitted node steps (Nakayama, finite-depth justification, and construction of the
minimal prime). I replaced that paragraph with all seven natural-language proof
steps and their named DAG dependencies. The signature is unchanged; the node's
lean.statement now reproduces its signature verbatim, including line breaks.
Only the named theorem has sorry, no definition is hollow, and nothing is proved.
All universes and variables are bound and all imports serve the signature.
The required server single-file compile is clean; the delivery dry run is recorded
by deliver2.py below.

## Reviewer fix (R-dap0936, stage 2)

The associated-prime hypothesis `(hp : p.IsPrime) (z : M) (hAnn : {a : R | a • z = 0} = p)`
was an inline second rendering of the notion; the landed siblings
(`exists_mem_associatedPrimes_quotient_pow`, `mem_minimalPrimes_of_depth_ge`, the downstream
user of this lemma) state it as Mathlib's `p ∈ associatedPrimes R M`. Replaced by
`(hp : p ∈ associatedPrimes R M)` (import `Mathlib.RingTheory.Ideal.AssociatedPrime.Basic`),
declaration renamed `IsLocalRing.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`.
Over Noetherian R this is exactly the node's notion: checked in Lean that
`p ∈ associatedPrimes R M ↔ p.IsPrime ∧ ∃ z : M, {a : R | a • z = 0} = p`
(via `isAssociatedPrime_iff`, which drops Mathlib's radical under `IsNoetherianRing`).
Everything else unchanged.
