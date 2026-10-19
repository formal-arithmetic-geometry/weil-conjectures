## Worker report

The module `Sheaf.TraceFormula.ValuationHeightRank` states
`Ideal.valuationHeightLeRationalRank` with proof `sorry`. It uses Mathlib's
`ValuationSubring K` for the valuation ring, its canonical subgroup `A.unitGroup`
of `Kˣ`, the quotient group `Kˣ ⧸ A.unitGroup`, and `Additive` to view this
multiplicative quotient as an additive commutative group for the recorded
`AddCommGroup.rationalRank` definition.

The Lean binders render the node clause by clause. `K : Type u` with `[Field K]`
is the field. `A : ValuationSubring K` is exactly a subring of `K` satisfying the
valuation-ring alternative (for every element, it or its inverse is in the
subring). `n : ℕ` is the length of the prime chain. `p : Fin (n + 1) → Ideal A`
contains the ideals indexed by `0,...,n`; `hp : StrictMono p` says every later
ideal strictly contains every earlier one, hence gives the displayed strict
chain. `hprime : ∀ i, (p i).IsPrime` says every member is prime. The conclusion
casts `n` to `Cardinal.{u}` and bounds it by
`AddCommGroup.rationalRank (Additive (Kˣ ⧸ A.unitGroup))`, the cardinal-valued
Q-dimension of the value-group quotient, exactly the node's rational rank.

The statement dependencies used are:

- `def-weil-field`: Mathlib's `Field` class (the node is a Mathlib leaf).
- `def-trf-rational-rank`: `AddCommGroup.rationalRank` in
  `Sheaf.GroupTheory.RationalRank`, whose definition is
  `Module.rank ℚ (ℚ ⊗[ℤ] G)`.

The proof dependencies are named in the theorem docstring and are intentionally
not imported because neither has a Lean declaration yet:
`lem-trf-valuation-prime-convex-correspondence` supplies the strict chain of
convex subgroups, and `lem-trf-convex-chain-rational-rank` supplies the chain
bound.

Edge cases checked: `n = 0` gives a one-element prime list and the required
zero bound; `A = ⊤` is the field valuation ring and the quotient is trivial;
`A` may have a nontrivial or infinite-rank value group; `A.unitGroup` is the
canonical unit subgroup, so no arbitrary choice of units or value-group map is
introduced. The `Fin (n + 1)` index retains the endpoint and excludes no chain
length. The quotient is converted with `Additive` only to match the additive
abelian-group interface of rational rank, without changing its underlying
value-group elements.

Searches made before writing:

- `msearch.py Q142 lem-trf-valuation-height-rank leanfinder "strict chain of prime ideals in valuation subring bounded by rational rank"`: 8 hits, including Noetherian Krull-dimension bounds and `ValuationSubring.primeSpectrumOrderEquiv`; no theorem combining valuation prime chains with value-group rational rank.
- `msearch.py Q142 lem-trf-valuation-height-rank loogle "ValuationSubring unitGroup quotient rationalRank"`: 0 hits; the service reported unknown identifier `unitGroup`.
- `msearch.py Q142 lem-trf-valuation-height-rank grep "ValuationSubring.*unitGroup|rationalRank|StrictMono.*Ideal" Mathlib`: 19 hits, including `ValuationSubring.unitGroup`, `unitGroup_le_unitGroup`, and unrelated strict-monotonicity lemmas; no matching height/rational-rank theorem.
- Direct `rg` over `WeilConjectures/` and `lean/Sheaf/`, and grep for
  `lem-trf-valuation-height-rank` and `valuationHeightLeRationalRank`, found no
  existing project declaration. The full Mathlib `ValuationSubring` source was
  read; its `unitGroup` is the canonical subgroup used here.

The file compiled cleanly with `scompile.py`; the only expected diagnostic is the
theorem's use of `sorry`.

## Second reading by Q142

I reread the item node, both statement-dependency records, the full
`ValuationSubring` declaration containing `unitGroup`, and the delivered module.
The field, valuation-ring object, chain index, strictness, primality, quotient,
and cardinal rational-rank inequality all occur with the same objects and no
extra hypotheses. `StrictMono` on `Fin (n+1)` preserves every clause of the
strict chain, including `n=0`. The module imports the recorded rational-rank
definition and uses Mathlib's valuation-ring construction rather than a private
copy. No statement correction, new node, dependency repair, or
`STATEMENT-DISPUTED` finding is needed.


### Independent immutable-delivery review (2026-10-18)

Reviewed f1936108f935f7e0d85be29be8e8722de2ffca02 from the extracted snapshot.
The original Worker report and Second reading by Q142 sections above are retained.

Clause audit: `{K : Type u} [Field K]` supplies precisely a field; Mathlib Field
extends CommRing and DivisionRing, with nontriviality. `A : ValuationSubring K`
is a genuine subring with `mem_or_inv_mem'`. Its alternative at zero adds no
condition because zero belongs to a subring. `A.unitGroup` is the kernel of its
canonical valuation on K-units; `unitGroupMulEquiv : A.unitGroup ≃* Aˣ`
identifies it with exactly the units required by the node. The quotient is
therefore the specified value group; Additive changes only notation/structure.
`p : Fin (n + 1) → Ideal A` includes both endpoints, `StrictMono p` is equivalent
to the consecutive strict inclusions by transitivity, and `hprime` supplies
primality for every endpoint. The sole conclusion is the required bound on n.
The imported rationalRank is the real construction Module.rank over Q of
Q tensor_Z G; tensor symmetry gives the node's G tensor_Z Q. No finite-rank,
finite-generation, characteristic, Noetherian, or extra universe assumption occurs.
All type and universe variables are explicitly bound with autoImplicit false.

Edge cases: n=0 has one prime and zero strict inclusions; no empty chain is
required by this node. The field valuation A=top has trivial quotient and rank
zero, and no positive-length strict prime chain. Arbitrary positive characteristic
and infinite rank are included. The node writes all infinite dimensions as infinity;
for comparison with finite n this has exactly the same truth value as the cardinal
rank used here. No statement correction is necessary.

Source checked online: Temkin, Stable modification of relative curves, author v3,
section 2.1 pp.7-8, especially lines 375-437 and 479-503 in the PDF text extraction.
The source order uses a/b in A; the node uses the dual y/x convention. Convex
subgroups and their chain lengths are unchanged by this duality. The source gives
the units quotient, prime/overring/convex correspondence, rationalized dimension,
and the height consequence. The general finite-chain bound follows by choosing
one element from each strict convex-group increment: the last nonzero term of
an integer relation cannot lie in the preceding convex subgroup, since convex
subgroups of an ordered abelian group are pure. Thus those elements are rationally
independent. This is the node's cited convex-chain proof dependency, not a new
statement prerequisite. Neither proof dependency is needed to type this theorem;
their current nodes have no Lean declarations. They need not be formalized just
to state this item with sorry.

Independent rg searches in Mathlib's valuation, GroupTheory, and dimension trees,
and in WeilConjectures and the group's lean tree found no duplicate theorem.
The existing rationalRank is reused; no private definitions or arbitrary maps occur.
The current route-pivot dropped list has none of this item's statement or proof
dependencies, and no item repair note was present. No dropped machinery occurs.

Finding H8 repaired: the delivered docstring only named two proof ingredients and
omitted the quotient-order step. The complete replacement module now records all
three node steps, both dependency ids, finite chain reversal, and the tensor
identification. The signature and sorry proof are unchanged. This report adds the
clause-by-clause independent review to strengthen the terse original second reading.

Compiler evidence: scompile.py Q142 lem-trf-valuation-height-rank with the absolute
immutable module path returned exit 0: sandbox 5.7 seconds, library path 18.9 seconds,
with no diagnostics. The reviewer's fixed module is compiled separately through the
same wrapper, as recorded in review.md. No lake build, live Lean edits, delivery,
claim, merge, direct ssh, or Git mutation was performed.
