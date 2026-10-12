## What changed

Proved `RingHom.zariskiPair_rank_one_propagation` in
`Sheaf.RingTheory.ZariskiPairRankOnePropagation`, with its signature unchanged.
Added the proof-only import `Mathlib.RingTheory.TensorProduct.Quotient`.
Updated the theorem docstring and the existing DAG node's proof, proof dependencies,
and proof origin to match the compiled proof.

The proof identifies `(A/I) ⊗[A] B` with `A/I`, computes rank one at every maximal
ideal by quotient base change, and transfers rank one to a contained prime using
Mathlib's rank specialization theorem. Finite flat stalks are free, and Mathlib's
rank-one linear-equivalence theorem gives the stated equivalence. The unit
`sk-thm-p1`'s realized statements and proof steps are untouched.

## Proved and sorry left

Closed one hole: `RingHom.zariskiPair_rank_one_propagation`
(node `lem-weil-pbc-zariski-pair-rank-one-propagation`).
No holes remain in the module; no new holes or modules were added.
This is a complete proof from Mathlib, not a decomposition into holed statements.
The local compiler succeeded without warnings. The delivery dry run also checks axioms.

## No longer needed

No original imports were removed: all three public imports supply the existing
statement's vocabulary and structures. The only added import is proof-only.
The proof does not need node `lem-weil-pbc-finitely-presented-flat-module-projective`
(Mathlib `Module.Flat.projective_of_finitePresentation`) or node
`lem-weil-pbc-finite-projective-rank-locally-constant`
(Mathlib `Module.isLocallyConstant_rankAtStalk`); both are removed from this node's
proof dependencies. These are Mathlib leaves, not separate Sheaf modules.
No Sheaf or WeilConjectures proof dependency modules are needed. Finitely presentedness
remains in the unchanged statement but is not needed by this proof.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's local-constancy/closed-complement argument
is valid but unnecessary: rank specialization for finite flat modules gives a
shorter proof. The previous node's search notes already mentioned this possibility.
The proof handles the zero ring because it first introduces a prime; nontriviality
of A/I is obtained only after producing its prime q. No hypothesis was added.
Searches used launcher LeanFinder and Loogle plus ripgrep in Mathlib and both roots;
no existing theorem combining all of these hypotheses was found.

## Second reading by J3

1. Compared the delivered Lean module against the repository with `diff -u`.
   Verdict: the sole existing declaration's signature is byte for byte unchanged;
   only its proof, proof docstring, and one private import differ. There are no
   definitions, new declarations, or change records to inspect.
2. Compiled the delivered module locally through `lcompile.py`, without errors or
   warnings. Compiled a scratch copy with
   `#print axioms RingHom.zariskiPair_rank_one_propagation`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Checked that the delivered
   source has no holes or forbidden declarations. The equivalence is constructed
   from the given bijectivity, not from an unproved existence statement.
3. No statements were split off and no nodes or modules were added. Checked the
   argument's edge cases: a zero base ring has no primes; after introducing a prime,
   a containing maximal ideal exists and contains I, so the quotient prime supplies
   precisely the nontriviality needed for rank one. Finite flatness supplies both
   free stalks and rank specialization without the unused finite-presentation
   hypothesis. Verdict: true with the original hypotheses and conclusion.
4. Read Mathlib's quotient tensor equivalence, rank base-change and specialization
   lemmas, local finite-flat freeness theorem, and rank-one linear-equivalence
   theorem. Also searched both library roots for Zariski-pair/rank-propagation
   declarations and inspected Mathlib's `Flat/Rank.lean`: its global bijectivity
   criteria would still require the rank calculation here, not shorten it.
   Verdict: a direct Mathlib proof, no unnecessary Sheaf dependencies. The two
   removed original proof dependencies are both listed under `No longer needed`.
   Checked `dag/units/sk-thm-p1.json`: this node is below the realized unit steps,
   none of which is bypassed. The new TensorProduct.Quotient import is private.
   The three original public imports supply statement prerequisites: in particular,
   making FreeLocus private in a scratch copy makes `Module.FinitePresentation`
   unavailable in the public signature, as the compiler confirms.
5. Compared the node JSON to the repository: changes are confined to `proof`,
   `proof_deps`, and `proof_origin`. The three steps track the Lean argument;
   proof dependencies retain localization and remove exactly the two unused
   projectivity/local-constancy leaves. The statement, Lean record, source, and
   unit are unchanged. Verdict: the DAG agrees with the proof.

Changes by the second reader: appended this review only; no Lean or node repair
was needed. One original hole is closed, zero holes are added or split off.
