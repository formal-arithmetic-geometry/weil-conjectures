# E1 worker report: lem-weil-pbc-dim-one-residue-field-extensions-finite

## Files

- dag/nodes/sec-proper-base-change/lem-weil-pbc-dim-one-residue-field-extensions-finite.json: split Stacks Algebra Tag 031F into four proof steps.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-dim-one-submodule-quotient-finite-length.json: new unsplit support node, stating Stacks Algebra Tag 00PE for arbitrary (possibly non-finitely generated) submodules of K^r. LeanSearch, LeanFinder, and pinned Mathlib source search found no exact match.

## Attachments and sources

No slopmaster2 attachment. The migrated item's slopmaster2 audit is "none"; source searches by both node IDs, blueprint docstring tags, "finite-extension-residue-fields-dimension-1", "length M/xM", and submodules of K^r found no exact declaration. Mathlib's isFiniteLength_quotient_span_singleton covers R/xR only, not arbitrary M/xM. The read-only E1 clone is older and lacks the item, so the lead should check the latest server audit before delivery.

The worker read Stacks algebra.tex at the F2 literature checkout before migration: Tag 00PE, label lemma-finite-length, lines 29171-29235; Tag 031F, label lemma-finite-extension-residue-fields-dimension-1, lines 29241-29264. The F2 literature checkout was no longer present during migration, so this is the earlier direct check, not a new read in the sandbox.

## B-E check

- B: The 00PE node introduces R, K, r, M, and x with the same hypotheses as the source. Its length, Noetherian, and dimension notions cite their definition nodes. It is unsplit and has no proof sketch. The blueprint ancestor is lem-weil-pbc-normal-constant-generic; the from.place identifies the 032P/031F route. Blueprint search found no duplicate. The item retains its original blueprint and maintainer fields.
- C: Step 1 cites the 00PE node for S/xS finite length. Step 2 constructs the strict preimage chain explicitly and obtains finite k-dimension. Step 3 uses the existing finite-dimensional-algebra and finite-algebra-over-a-field nodes for Artinianity and finitely many maximal closed-fibre primes, then the quotient-spectrum node for the correspondence with primes of S above m. Step 4 gives the fraction formula and kernel for the residue-field isomorphism. All cited node statements were read and have the hypotheses used here.
- D: The 00PE node is strictly smaller than 031F and is the lemma expressly invoked by its source; the other three steps prove the item. The dependency list is exactly the union of step uses, with no cycle introduced.
- E: For x a unit, both quotients in 00PE vanish; for r=0, M=0. For S=R, the one prime above m has degree-one residue extension. For S=K, S/mS=0 and there are no primes over m; Step 3 handles this. No finite-generation hypothesis on S is assumed.

## Checks and limitations

The JSON files parse, and the proof dependency union matches the steps. Before migration, review_split.py passed and blueprint_refs.py check reported zero errors on the rebased tree. The full DAG check reported unrelated existing reachability and route errors and zero cycles. No Git commands or server operations were run for the sandbox migration.

## Review by E1

I read Algebra Lemma 031F (`lemma-finite-extension-residue-fields-dimension-1`, algebra.tex lines 29241-29264) and Lemma 00PE (`lemma-finite-length`, lines 29171-29235) in the Stacks source. The item's domain map, one-dimensional Noetherian local base, finite fraction-field degree, and three conclusions agree with 031F. The new node states 00PE's hypotheses and both conclusions, including the bound for an arbitrary submodule of `K^{\oplus r}`; it adds no finite-generation assumption. The current item audit has slopmaster2 state `none`, and the read-only source search found no exact declaration for either node.

For Step 1, 00PE applies to `S \subset L \cong K^{\oplus n}` after choosing a nonzero `x` in the maximal ideal; the field-extension definition supplies the inclusion. For Step 2, the explicit preimage-chain argument transfers finite length to `B=S/\mathfrak mS`; the module-length definition then makes finite length exactly finite `k`-dimension because the `R`-submodules of `B` are its `k`-subspaces. Step 3 uses the cited finite-dimensional-algebra result for Artinianity, the finite-algebra-over-zero-dimensional-local-ring node for finite maximal spectrum, and the quotient-spectrum node for the correspondence with primes over `\mathfrak m`. Each cited statement has the required hypotheses; maximality then follows from the quotient field. Step 4 computes the localized residue field with the displayed fraction map and bounds its dimension as a quotient of `B`. No step requires `S` to be finite over `R`.

The new 00PE node is unsplit, has no proof or proof dependencies, defines its objects and cites its notions; its source label and blueprint place match the route through 031F. A search of current nodes by both tags and the submodule/residue-field notions found no duplicate 00PE fact. It is smaller than the item: its conclusion is the length estimate, while Steps 2-4 derive the three prime and residue-field claims. The dependency statements were read in full and no cycle is introduced by this new leaf. Edge checks: a unit `x` makes both quotients zero; `r=0` forces `M=0`; `S=R` gives one prime of residue degree one; `S=K` gives `B=0` and no prime above `\mathfrak m`. I found no correction to send back. Delivery shape and preflight remain for the lead's packaging step.
