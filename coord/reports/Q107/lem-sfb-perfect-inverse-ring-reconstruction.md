# Stage-1 delivery: lem-sfb-perfect-inverse-ring-reconstruction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-perfect-inverse-ring-reconstruction.json`: statement, split by reuse of the existing stronger reconstruction theorem; Mathlib verdict no match.
- `citations.json`: verbatim quotations for the unique cited node in step 1, including both the perfectness and projection-adjunct clauses.
- `report.md`: this report. `searches.jsonl` was produced by the prescribed search command.

New nodes: 0. New Mathlib leaves: 0. The original item statement, its five statement dependencies, original searches, created record and blueprint ancestry are retained.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item's blueprint tag, the existing theorem's tag, inverse/perfect combinations and Rlim found no declaration stating the reconstruction theorem. Ordinary projective models and unrelated derived limits are not attachments.

## WANTED

None. The needed Stacks source is available locally.

## Findings and repairs

The item is the all-perfect alternative of Stacks Tag 0CQG, `more-algebra.tex`, `lemma-Rlim-perfect-gives-perfect`. Its statement is correct, including elementwise nilpotence rather than a uniformly nilpotent ideal. No statement dispute and no route change.

A whole-DAG search for 0CQG and the source label found the pre-existing `lem-sfb-nil-ring-perfect-derived-limit`, which states both required conclusions with exactly the same hypotheses and also specifies naturality and transition compatibility of the projection adjuncts. This delivery reuses that theorem rather than creating a duplicate pseudo-coherent reconstruction or perfectness criterion. In particular it does not attempt to apply `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction`: that node assumes nilpotent transition ideals, a stronger hypothesis than the present elementwise nilpotence.

The reused result is in the same unit, `sk-thm-sf-ctf-stability`, and has no proof or statement dependency on this item. It is an existing unsplit DAG node, not a newly created restatement masquerading as a split. This delivery adds only a reuse edge to that previously stated theorem. Consolidating the existing duplicate node identifiers is a maintainer operation; this delivery changes neither the sibling node nor its users. The current blueprint's direct-image proof (3), unit and chapter were read; this supporting algebra input keeps the inherited effectivity route.

Whole-blueprint searches with `tools/blueprint_refs.py search` for `inverse limit perfect`, `0CQG` and `nil-kernel` found no imported equivalent. The item's nearest blueprint ancestor command returned None, matching its inherited `from.node: null`; its existing precise from.place and via chain are preserved.

Five actual Mathlib searches are appended to the inherited search records: LeanFinder with the full reconstruction statement and a second phrasing in terms of algebraization of finite projective complexes, Loogle `DerivedCategory, "limit"`, LeanSearch for perfect complexes over nilpotent transition kernels, and grep `perfect.*(limit|completion)|(limit|completion).*perfect|Rlim` in Algebra/Homology. I read all returned hits. They concern Frobenius-perfect rings, formal smoothness, ordinary adic completion and ordinary inverse limits. The grep hit at Mathlib/Algebra/Homology/CochainComplexPlus.lean:60 was opened: it is the finite-limit closure of bounded-below complexes, not this countable homotopy-limit reconstruction. The returned HomologicalComplex limit instances are likewise ordinary limits of complexes. No result states the present theorem or specializes to it in one line. Every appended search is copied from searches.jsonl with its actual tool and exact query; none of the services was unavailable.

## Unfinished work

None for this item. The existing reconstruction theorem remains its own stage-1 queue item; it is reused, not edited here.

## Not duplicates

No new nodes are created. The item is a weaker consequence of the already-existing `lem-sfb-nil-ring-perfect-derived-limit`; step 1 cites that node instead of duplicating its proof prerequisites. Both share source Tag 0CQG.

## Review by Q107

I read Stacks Tag 0CQG, its full proof and the immediately preceding Tag 0CQF in more-algebra.tex. The source's proof obtains pseudo-coherence and the comparison maps from 0CQF, then uses the Jacobson radical and maximal-residue-field criterion for perfectness. That confirms that the imported item's locally nilpotent kernels and all-perfect alternative are intentional; replacing them by nilpotent ideals would lose generality. I also opened the full statement of the existing nil-ring-perfect-derived-limit node, rather than relying on its title or its proof.

For step 1 I checked each input against that cited statement: the same positive-integer ring sequence, surjective homomorphisms, each kernel element nilpotent, the same unbounded module derived categories, the same definition of perfectness as bounded finite projectives, maps in D(A_(n+1)) to scalar restrictions, and invertibility of their scalar-extension adjuncts. The cited theorem then allows the same derived-limit object with its given projections. Its exact statements "Then $T$ is perfect over $A$." and "For every $n$, the scalar-extension adjunct of the projection $p_n:T\to T_n$ is an isomorphism in $D(A_n)$," are copied into citations.json. Thus both conclusion clauses, including the specified maps rather than mere existence of isomorphisms, follow directly. No auxiliary associativity, Nakayama, pseudo-coherent reconstruction or residue-field criterion is being applied without a node citation: those belong to the existing theorem, not to this one-step specialization. I read the derived-limit definition and perfect-ring-complex definition to verify the same notions; the derived-change-of-rings node is already in the item's statement dependencies.

I checked B1–B10: there are no new statement-only nodes, no missing new definition dependency, no unverified Mathlib match or fictitious search, and inherited blueprint provenance is retained. For C1–C8 I checked that the sole non-elementary assertion is supplied verbatim by the cited theorem, no hidden source tag is an extra dependency, the source is not used as a substitute for a DAG citation, there is no reverse dependency, and both nodes are in the same unit. For D1–D5 the important distinction is reuse: no new node relocates the item's conclusion; a previously present stronger statement is cited exactly as the duplicate-avoidance rule requires. For E1–E7 I checked the hypotheses and map direction explicitly.

Small cases: for a constant ring tower the hypotheses reduce to invertible transition maps of perfect complexes; for the zero tower both conclusions are zero-object assertions. For A_n=k[t]/(t^n), the statement recovers ordinary complete perfect reconstruction without using that presentation in the proof. An elementwise nil but non-nilpotent ideal such as (x_1,x_2,...) in F_2[x_1,x_2,...]/(x_i^2 for all i) can occur as one transition kernel: no fixed exponent is used by the reused theorem, so that edge case remains covered. No long step exceeds 2000 characters. The only correction to the original empty proof is the explicit reuse with verified hypotheses and comparison-map normalization.
