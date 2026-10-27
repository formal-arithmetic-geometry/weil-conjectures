# Stage-1 delivery: lem-sfb-pd-flat-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pd-flat-extension.json: split item; statement unchanged; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-pd-linear-substitution.json: new statement-only lemma; no Mathlib match. A matrix identity for divided-power multinomial expressions, without any structure on the target ideal and without flatness.
- dag/nodes/sec-six-functors-basics/lem-sfb-pd-generator-criterion.json: new statement-only lemma; no Mathlib match. Product and iteration axioms may be checked on an ideal generating set once the other axioms hold globally.
- citations.json: verbatim statement extracts for all seven step/node citations.

## Attachments

None. I searched WeilConjectures for the blueprint id, divided powers, gamma-extends and flat extension. No project declaration states the item or either new lemma. The Perfect.lean flat-extension result concerns perfect complexes, not divided powers.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Corrections and route

The original item was statement-only and correct. It had no proof to preserve. The statement, hypotheses, statement dependencies, inherited blueprint place and via chain are unchanged. No STATEMENT-DISPUTED issue was found.

I read GOAL.md, the human's three blueprint levels in SETUP.md, the six-functor-basics chapter, sk-thm-sf-ctf-stability unit, and the latest direct-image statement/proof. This is a commutative algebra tool below the complete-intersection/direct-image branch, not a replacement for a unit-level proof. blueprint_refs.py ancestor reports a null ancestor for this inherited chain; the new nodes inherit that null and prepend the item to its via list. They specify the actual Stacks proof sentences they support. Searches of all blueprint nodes for divided powers, 07GP and linear substitution found no matching statement. The sole linear-substitution blueprint hit is a vector integration definition and unrelated. Searches of the whole DAG for divided-power statements and 00HK found the existing equational-flatness node, which is reused.

## Not duplicates

lem-sfb-pd-linear-substitution vs lem-sfb-pd-flat-extension: the new lemma is the finite matrix identity in the 07H1 proof, assumes no flatness, constructs no maps on IB, and asserts neither existence nor uniqueness of an extension.
lem-sfb-pd-linear-substitution vs lem-sfb-ordinary-pd-polynomial-extension: the parent has a divided-power polynomial algebra and its universal property (07H5); the new identity involves an arbitrary target ring, a finite matrix, and formal finite sums, with no target divided powers.
lem-sfb-pd-generator-criterion vs lem-sfb-split-square-zero-divided-powers: that existing node constructs a particular structure on C plus M (09PH); it mentions 07GP as a source for its argument, but does not state the general criterion for arbitrary candidate maps and arbitrary ideal generators.
lem-sfb-pd-generator-criterion vs lem-sfb-pd-flat-extension: the item extends an existing structure along a flat map; the new lemma tests missing axioms of candidate operations on any ideal, with no ring map or flatness assumption.

## Review by Q10

I read dpa.tex Tag 07H1 (lemma-gamma-extends), including all of the flat-case proof and its footnote replacing Lazard by algebra.tex Tag 00HK. I also read 00HK itself, the full statements of the existing flat-map definition and equational-flatness node, and the ordinary divided-power definition. For the new matrix-identity node I read the two displayed formulas and their coefficient-comparison argument in 07H1. For the new criterion node I read dpa.tex Tag 07GP (lemma-check-on-generators), its statement and proof: multiplication propagates first, then iteration propagates using multiplication. These are genuine auxiliary claims, not renamed clauses of the item; both are left unsplit as required.

Step 1 uses the ordinary structure's addition and scalar axioms to expand a finite presentation, by induction on the tuple length. The substitution node defines exactly the expression P_n referenced here. Its positive-degree terms lie in IB because at least one exponent is positive. Thus neither uniqueness nor ideal membership conceals a separate theorem.

Step 2 uses the flat-map definition only to regard B as a flat A-module, and takes precisely the finite-relation factorization asserted by the existing equational-flatness node. I checked its hypotheses allow arbitrary commutative rings, arbitrary modules, empty tuples, and no finiteness or Noetherian condition. I explicitly use coefficients (x_i,-x'_k) and module elements (b_i,b'_k); the second coefficient block is negative but its module block is not. Consequently the two sums defining y_j are equal in A, not merely equal after applying f. This is what the matrix-identity node needs. Applying its equality twice proves independence without assuming injectivity or faithfulness of f. The two matrices can be empty. This step does not invoke Lazard, tensor exactness, or any uncited descent theorem.

Step 3 is an elementary computation from the newly defined formula: the degree-one terms give the identity, total degree supplies the scalar exponent, and concatenating tuples partitions the sum into the convolution for addition. Empty presentation gives zero in every positive degree. No cited theorem is needed for this reindexing of finite sums.

Step 4 uses the ordinary structure definition to apply f to the product and iteration identities. The one-term formula applies again to gamma_m(x), which belongs to I for positive m; thus the outer operation is evaluated at the correct element. The new generator-criterion statement supplies exactly the missing two axioms for the candidate maps, not the weaker assertion that a morphism preserves two already-existing structures. I checked its ideal is IB, its generating set is f(I), candidate positive operations land in IB (step 1), and the three global axioms are established in step 3. Compatibility and uniqueness are retained explicitly.

Mathlib searches were run with msearch.py and read as returned; queries and responses are in searches.jsonl and copied into node records. Each new lemma was searched by two natural-language phrasings (LeanFinder and LeanSearch), Loogle, and source grep. I read Basic.lean:78-92,259,329-351 and DPMorphism.lean:237-254. dpow_linearCombination presupposes divided powers on the ring in which the coefficients act; it does not provide the matrix identity before constructing divided powers on B. The constructor DividedPowers.mk requires product and iteration axioms globally. dpow_eq_from_gens and fromGens assume complete structures on both sides, so cannot supply the generator test. These are recorded as nonmatches, not unavailable services. The item itself was searched again under Q10 with all four tools; inherited searches remain intact.

I tested the statements and construction for I=0, B the zero ring, empty tuples, n=0 in the matrix identity, n=1, a zero matrix, an identity matrix, and an empty generating set for the zero ideal. For n=0 the unique zero multiindex contributes 1 even on an empty tuple; for positive n the empty-tuple sum is zero. No step cancels a factorial, treats a nonfaithfully flat map as injective, assumes finite generation of I, or assumes target divided powers before construction. Every proof step is below 2000 characters. No source error was found. I checked delivery-errors B through E: self-contained statements with definition citations, Stacks tags and labels, no proof in new nodes, no circular uses, no off-route theorem other than the existing Mathlib flatness tool, and exact quotes for every cited node.

## Unfinished work

Only the proofs of the two new statement-only supporting lemmas remain for their future stage-1 workers. Their sources and concrete statements specify what must be proved. Nothing required for this one-level split is omitted.

## Dry-run repair

The first server preflight rejected the adjacent TeX row break and sum command inside a substack as doubled backslashes (B4). I rewrote that summation bound on one line, with the same mathematical indexing condition. No statement content changed.
