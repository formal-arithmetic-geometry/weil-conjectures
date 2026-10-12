## What changed

Proved `Pi.isNormalRing_of_finite` in
`lean/Sheaf/RingTheory/FiniteProductNormal.lean`, with its statement unchanged.
Added the proof-only import `Mathlib.RingTheory.Spectrum.Prime.RingHom`.
The proof follows all three existing DAG steps: classify the prime using
`PrimeSpectrum.exists_comap_evalRingHom_eq`, identify its localization using
`RingEquiv.ofBijective` and `Localization.AtPrime.mapPiEvalRingHom_bijective`,
then transport the factor's domain and integral-closedness properties using
`MulEquiv.isDomain_iff` and `IsIntegrallyClosed.of_equiv`.

The local launcher compile passed without warnings. The empty index case is covered
by the classification theorem: a prime would produce an element of the empty index
set. No nonempty assumption or additional hypothesis was introduced. The selected
factor may itself have zero ring structure; a prime on that factor is required by
classification, so that case is likewise handled without extra assumptions.
The original proof route and dependencies remain accurate; no node change is needed.

## Proved and sorry left

Closed the sole hole: `Pi.isNormalRing_of_finite`
(node `lem-weil-pbc-finite-product-normal`).
No `sorry` remains in the module, and no holes or declarations were added elsewhere.
This is a proof entirely from proved Mathlib declarations, not a decomposition.

## No longer needed

None. All three original public imports supply the unchanged statement's notions;
the new non-public import supplies prime classification. All original DAG dependencies
are used, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The three Mathlib leaves in the DAG have exactly
the required signatures. LeanFinder, Loogle and launcher grep confirmed the matches;
searches of both library roots found no existing proof of this theorem.
The referenced Stacks source file is absent from this machine's literature directory;
the existing node and docstring record its source and complete proof, which this
Lean proof follows without alteration.

## Second reading by D3

1. PASS — Compared the complete delivered module against the repository with `diff -u`.
   The only differences are replacing the sole `sorry` with its proof and adding
   `import Mathlib.RingTheory.Spectrum.Prime.RingHom`. The existing declaration's
   signature and docstring are byte for byte unchanged. No definitions, target
   statements, or other modules are changed; no change record is needed.
2. PASS — Compiled the delivered file through `lcompile.py` without errors or warnings.
   Scanned for holes and forbidden declarations: none remain. Compiled a scratch copy
   ending in `#print axioms Pi.isNormalRing_of_finite`; its axioms are exactly
   `propext`, `Classical.choice`, and `Quot.sound`. The equivalence is constructed from
   a proved bijective homomorphism; no data is chosen from an unproved existence claim.
3. PASS — No statements or holes were split off, so no new docstrings or nodes are
   required. Read the Mathlib sources for prime classification, the localization map
   and its bijectivity, and both equivalence-transport lemmas. The empty index case
   has no primes; singleton products reduce to the given factor; zero ring factors
   contribute no primes. Independent LeanFinder search for local normality of direct
   products returned local-property results requiring a domain, not a theorem that
   replaces this proof. Launcher grep and searches of both library roots found no
   existing shorter proof of the unchanged statement.
4. PASS — The proof takes the direct Mathlib route and uses all three planned steps.
   Each original public import supplies notions or structures used by the signature;
   the added import is proof-only and correctly non-public. No original proof
   dependency is unused, so `## No longer needed` is complete. Read the unit record
   `dag/units/sk-thm-p1.json`, including `realized`: this is a lemma below its unit
   steps, and the unchanged route bypasses no realized statement or step.
5. PASS — Read the item's node and its three Mathlib leaves. The proof classifies
   the prime using the first leaf, constructs the evaluation-induced localization
   equivalence using the second, and transfers domain and integral-closedness using
   the third. The normal-ring definition is expressed by the unchanged localization
   condition. Existing `proof`, `proof_deps`, and document-based `proof_origin` match
   the written proof, so no node changes are needed.

Changes made by the second reader: appended this review only. The Lean proof and
imports were correct and are unchanged. One existing hole closed, zero holes added;
no decomposition and no pruning.
