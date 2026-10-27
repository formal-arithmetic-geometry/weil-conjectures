# Q47 stage-1 report

Files written:

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-groupoid-constant-rank-norm-annihilator.json`: item, statement node, split proof; no new nodes and therefore no Mathlib leaves created.
- `citations.json`: verbatim statement quotes for each proof-step citation.
- `report.md`: this report.

Attachments: none. The existing declarations/nodes used in the proof remain the cited DAG nodes.

WANTED: none.

The item was not already proved by a project declaration: searches of `lean/WeilConjectures/` and the slopmaster2 source checkout found no declaration tagged or named for this item. I searched the DAG and blueprint for duplicates. The existing nodes `lem-a1-finite-locally-free-norm-characteristic-polynomial` and `lem-a1-affine-groupoid-polynomial-norm-invariant` state the two substantive ingredients, so I did not create duplicate nodes or move a clause of the item into a new node.

## Review by Q47

I read the item against Stacks Project groupoids.tex, Tag 03BJ (integral over invariants), Tag 03BH (determinant trick), and Tag 0231 (groupoid definition), together with algebra.tex Tag 00DX (Cayley–Hamilton). I also read the complete statements of the two existing norm nodes cited by the proof and the groupoid-law definition node. The item hypotheses match the source's affine groupoid, finite locally free source and target of common positive rank, and identity section; the inherited `A ne 0` and `r >= 1` hypotheses make the monicity clause applicable.

Step 1 cites `lem-a1-finite-locally-free-norm-characteristic-polynomial`, whose statement explicitly gives the norm polynomial form, monicity for nonzero A, and the evaluated Cayley–Hamilton annihilation. I checked that its `varphi`, `b`, and degree specialize to `sigma`, `tau(a)`, and `r`.

Step 2 cites `lem-a1-affine-groupoid-polynomial-norm-invariant`, whose statement explicitly says the coefficientwise polynomial norm lies in `C[T]`, equivalently that its source and target pullbacks agree. I checked that applying it to `F=T-a` gives exactly the item’s invariant coefficients and the displayed identity `P_a = N_sigma[T](tau[T](T-a))`.

Step 3 is elementary from the polynomial evaluation definition and the equality supplied by steps 1 and 2: applying tau to `P_a(a)`, replacing each coefficient by its sigma image, and identifying the resulting sum with evaluation of `sigma[T](P_a)` gives zero. No uncited non-elementary fact is used.

Step 4 cites `def-a1-scheme-groupoid-laws`, whose explicit identity axiom says `t(e(x))=x`; contravariance gives `epsilon ∘ tau = id`. Applying epsilon to step 3 therefore descends the zero equality to `P_a(a)=0`. This checks the source's root descent while using the identity section supplied in the item.

I tested the edge cases conceptually: for the identity groupoid (rank one), `sigma=tau=id` and `P_a(T)=T-a`, so every displayed comparison reduces to direct substitution. For a trivial finite constant group action of order r over a nonreduced ring such as `Z/4Z`, the polynomial is `(T-a)^r`, its coefficients are invariant, and it vanishes at a. These checks also confirm that reducedness is unnecessary. The positive-rank and nonzero-base assumptions avoid the zero-ring monicity ambiguity. No global basis, reducedness, or Noetherian hypothesis was introduced. Every cited statement was copied verbatim into `citations.json`, and the proof dependency list is exactly the union of the step citations.

Mathlib searches were run with `msearch.py` for LeanFinder, LeanSearch, Loogle, and Mathlib grep. The inspected hits concern finite group actions or generic characteristic polynomials; none states the locally free affine-groupoid norm polynomial with invariant coefficients and identity-section evaluation, so the item remains a project statement rather than a Mathlib leaf.

What was corrected: the imported node had no proof. I supplied the four-step proof, made `proof_deps`, `proof_origin`, `status`, and `split_report` explicit, and preserved the inherited statement, dependencies, source, and blueprint provenance. No statement correction or source error was found.

Validation repair: the first full dry run required a longer verbatim quote for the groupoid identity citation; I expanded that quote to include the adjacent explicit axioms without changing the proof. The standalone server DAG check passed.
