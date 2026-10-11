## Worker report

The module `Sheaf.RingTheory.SeparateImageClosedFromClosed` states
`PrimeSpectrum.exists_one_mod_mem_of_disjoint_closure_image_zeroLocus`, with `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  The independently bound universes allow arbitrary sizes for both rings.
- Ring homomorphism φ: `(φ : R →+* S)`.
- Ideals I of R and J of S: `(I : Ideal R) (J : Ideal S)`.
- V(J) in Spec S: `zeroLocus (J : Set S)`.
- Its image under Spec φ: `comap φ '' zeroLocus (J : Set S)`.
- Its closure in the Zariski topology of Spec R: `closure` of that image.
- Disjointness from V(I): `h : Disjoint (closure (...)) (zeroLocus (I : Set R))`.
- An element f of R exists: `∃ f : R`.
- Its image in R/I is one: `Ideal.Quotient.mk I f = 1`.
- Its image in S belongs to J: `φ f ∈ J`; both clauses are joined by `∧`.

There are no `stmt_deps` on the node. The statement uses Mathlib declarations
`PrimeSpectrum`, `PrimeSpectrum.comap`, `PrimeSpectrum.zeroLocus`, and its Zariski topology
from `Mathlib.RingTheory.Spectrum.Prime.Topology`, and `Ideal.Quotient.mk`
from `Mathlib.RingTheory.Ideal.Quotient.Defs` (available through that import).
The theorem docstring records all three proof steps and both proof-dependency node ids.

Source checked: https://stacks.math.columbia.edu/tag/07M3, Lemma 15.9.8 and its proof.
The local `literature/stacks-project/more-algebra.tex` is absent on this machine;
the authoritative tag was read online. Its statement agrees exactly with this node.
The proof uses the node's simplified choice I' = φ⁻¹(J).

Edge cases checked mathematically before writing:
- I = top: V(I) is empty and the quotient is the zero ring; f = 0 works for any J.
- J = top: V(J) is empty; f = 1 works for any I.
- R is the zero ring: its spectrum is empty, and a unital map out of R forces S to
  be the zero ring; f = 0 satisfies both clauses.
- S is the zero ring: J = top; f = 1 works.
- I = bottom: the hypothesis forces J.comap φ = top by the closure identity;
  hence φ(1) belongs to J, so f = 1 works. No injectivity or surjectivity is assumed.
- J = bottom and φ is the identity: the hypothesis forces I = top; f = 0 works.
No nontriviality, finiteness, or integrality hypotheses were added.
No statement disputes or node faults were found.

Searches for an existing full statement (2026-10-11):
- `msearch.py ... leanfinder`: “If the closure of the image of V(J) under Spec of a
  ring homomorphism is disjoint from V(I), there exists f mapping to 1 modulo I and
  into J”. Eight hits included `PrimeSpectrum.exists_image_comap_of_finite_of_free`,
  `Ideal.exists_le_prime_disjoint`, and zero-locus/basic-open identities; no exact match.
- `msearch.py ... loogle 'PrimeSpectrum.zeroLocus, closure, PrimeSpectrum.comap'`:
  returned `PrimeSpectrum.closure_range_comap` and
  `PrimeSpectrum.closure_image_comap_zeroLocus`; only proof ingredients.
- `msearch.py ... grep 'separate_image|07M3|closure_image_comap_zeroLocus' RingTheory`:
  two hits, the closure-image lemma and its use, both in Prime/Topology.lean.
- `rg -n 'separate_image|07M3|closure_image_comap_zeroLocus|lem-weil-pbc-separate-image-closed-from-closed'`
  on the source's `WeilConjectures/` and the project's `lean/Sheaf/`: no source hits;
  one project hit in LiftIdempotentUpstairs.lean, a proof-docstring citation only.
- Name collision search `rg -n 'exists_one_mod_mem_of_disjoint'` in Mathlib's prime-spectrum
  sources, WeilConjectures, and Sheaf: no existing declaration with the proposed name.
The relevant Mathlib signatures and docstrings for zeroLocus, the quotient map, and
closure_image_comap_zeroLocus were read. No private copy of any notion is introduced.

Validation: server single-file compile and delivery dry run are run by the worker;
the independent second reading is left to the assigned second reader.

## Second reading by E1

I read the node in `dag/nodes/sec-proper-base-change/lem-weil-pbc-separate-image-closed-from-closed.json`, the
Lean declaration, and Stacks Project More on Algebra, Lemma Tag 07M3.

The statement matches item by item:

- The rings are arbitrary `R : Type u` and `S : Type v`, with independent universes and
  `[CommRing R] [CommRing S]`.
- The ring homomorphism is `(φ : R →+* S)`.
- The ideals are `(I : Ideal R)` and `(J : Ideal S)`.
- `V(J)` is `zeroLocus (J : Set S)` and its image under `Spec φ` is
  `comap φ '' zeroLocus (J : Set S)`; `closure` is taken in `Spec R`.
- The sole hypothesis is exactly
  `h : Disjoint (closure (comap φ '' zeroLocus (J : Set S)))
  (zeroLocus (I : Set R))`.
- The conclusion is exactly `∃ f : R`, with both clauses
  `Ideal.Quotient.mk I f = 1` and `φ f ∈ J` joined by `∧`.

The declaration has no extra finiteness, Noetherian, integrality, injectivity, or
surjectivity hypotheses, and no conclusion is weakened or strengthened. Universes are
fully bound by `universe u v`; no variable is left implicit. The empty spectrum and zero
rings, `I = ⊤` or `⊥`, and `J = ⊤` or `⊥` are all covered by the same unrestricted
statement; no nontriviality or characteristic assumption is present.

I checked the source proof: taking `I' = φ⁻¹(J)` identifies the closure with `V(I')`,
disjoint zero loci imply `I + I' = R`, and writing `1 = g + f` yields the two stated
conclusion clauses. The Lean docstring records these steps and cites the two proof
nodes. No mismatch was found, so no source or statement repair was needed.

For the one-definition-per-notion check, I repeated the worker's searches: `msearch.py`
LeanFinder/LeanSearch queries for the full theorem, Loogle for
`PrimeSpectrum.zeroLocus`, `closure`, and `PrimeSpectrum.comap`, and `rg` over Mathlib,
`WeilConjectures/`, and `lean/Sheaf/` for `07M3`, `separate_image`, and
`exists_one_mod_mem_of_disjoint`. They found only ingredient lemmas such as
`PrimeSpectrum.closure_image_comap_zeroLocus`; no existing declaration states this
result. The module therefore correctly introduces the single theorem, with a `sorry`
proof and no private duplicate definitions.

Compilation with `scompile.py` succeeded without errors or warnings. The node's `lean.statement`
is verbatim the theorem signature in the module.
