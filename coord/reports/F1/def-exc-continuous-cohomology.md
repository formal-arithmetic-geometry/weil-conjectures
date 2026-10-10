# Stage-one delivery: def-exc-continuous-cohomology

## Files written

- `dag/nodes/sec-curve-estimates/def-exc-continuous-cohomology.json`: split the definition by citing the two assertions embedded in it; no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-exc-discrete-modules-abelian.json`: new statement, unsplit; no verified Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-exc-cochains-derived-invariants.json`: new statement, unsplit; no verified Mathlib match.

## Attachments

None. The search for `def-exc-continuous-cohomology`, `continuousCohomology`, discrete group modules and cochains in the slopmaster2 `WeilConjectures/` and `Comparator/` source found no declaration stating this item. Related Mathlib search results concern topological-module cochain cohomology rather than the right derived invariant functor in the discrete module category.

## Wanted

WANTED: the master blueprint file `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/def-exc-continuous-cohomology.md`, for comparison of the item's imported wording with its original source. It is absent from this machine's `literature/`; the imported node supplies its statement. Stacks tags 04JP, 04JR, 0A2H, 03VI and 0DVG independently cover its mathematical clauses.

WANTED: S. S. Shatz, *Profinite Groups, Arithmetic, and Geometry*, II.2, Proposition 5 and Theorem 8, for a printed proof of the comparison in `lem-exc-cochains-derived-invariants`. Stacks 0DVG asserts that comparison for profinite groups but says "insert future reference here" at the proof citation. This new node is intentionally unsplit.

## Issues found

The imported node puts three different kinds of content in a definition: the discrete-action and invariants definitions, the abelian-category assertion, and the assertion that continuous cochains compute derived invariants. The two assertions now have their own statement nodes; the original statement and its finite-ring hypothesis were not changed. The Mathlib source directory named by `SETUP.md` is absent from the read-only source checkout, and LeanSearch returned HTTP 500. I streamed the relevant pinned Mathlib source file at revision `0df444a`: its `TopRep` cohomology is cochain homology, and its header lists comparison and exactness work as TODOs. A full source-tree grep could not be done, so no leaf was claimed.

## Unfinished

The two new statements remain unsplit for the next stage-one workers. The local blueprint and Mathlib source trees were unavailable, as noted above. No Lean was written or built.

## Review by F1

I read the imported item's JSON, its unit `sk-prop-h2`, and its chapter `sec-curve-estimates`. The item is a background definition for this unit rather than the unit's key proposition, so I did not alter the unit record. I read the Stacks source at its pinned commit through the raw `etale-cohomology.tex` stream: tag 04JP is label `definition-G-module-continuous` and gives the $A$-linear action category and the open-stabilizer equivalence; tag 04JR is label `definition-galois-cohomology` and gives derived invariants; tag 0A2H is label `section-group-cohomology` and records the invariant functor and the ring-module version. Tag 03VI, label `trace-section-profinite-cohomology`, confirms the profinite specialization. Tag 0DVG, label `section-continuous-group-cohomology`, gives the inhomogeneous differential and asserts the profinite comparison. These clauses agree with the item for a finite ring and profinite group. The imported blueprint file itself was unavailable, which is recorded above.

There are no proof steps in the definition node. Its first cited statement, `lem-exc-discrete-modules-abelian`, says exactly that the particular category in the item's sentence is abelian and has enough injectives. Its second cited statement, `lem-exc-cochains-derived-invariants`, says exactly that the cohomology of the displayed continuous inhomogeneous complex agrees with the right derived invariant functor. `def-weil-abstract-derived-category` supplies the ordinary derived-category notion. I checked the statements of these cited nodes; the second new node does not assume the item it supports, so there is no circular dependency. Neither new statement contains a disguised proof or any proof steps.

For the category node I checked the hypotheses against Stacks 04JP and 0A2H: a left module over a ring, a topological group, an action by linear maps, discrete topology and open stabilizers. Requiring finite $A$ and profinite $G$ is a specialization. I also read tag 04JF, label `lemma-G-modules`, in `injectives.tex`; it states functorial injective embeddings for precisely $R$-$G$ modules, not just abelian $G$-modules. Kernels inherit open stabilizers from their ambient modules, and quotient elements inherit them from a representative, so the exactness clauses have the right objects. For the cochain node I checked the same action and discreteness hypotheses in 0DVG, plus the profinite hypothesis of its comparison assertion. I wrote the differential explicitly, including its degree-zero term; the item's "usual differential" hides this convention. The underlying $A$-module comparison uses the $R$-$G$ version of the derived invariant functor from 0A2H. The sources' statements are accurately reported, including the absent comparison proof reference.

As small-case checks, for trivial $G$ the category becomes ordinary $A$-modules, invariants are exact, and the cochain differential alternates between identity and zero, leaving only degree-zero cohomology. For finite discrete $G$ this is the usual finite-group cochain complex. For $M=0$ both derived invariants and every cochain group vanish. I also checked degree zero for arbitrary $G$: the kernel of $m\mapsto(g\mapsto gm-m)$ is precisely $M^G$. These rule out common shifts and a wrong choice of coefficient category. A finite $A$ need not be commutative, and the new statements retain that generality.

Before creating the nodes I searched the whole DAG by tags 04JP, 04JR, 0A2H, 0DVG, 03VI and by the category/cochain phrases, and used `tools/blueprint_refs.py search` for discrete modules, continuous cochains, the abelian-category claim and the comparison claim. No separate blueprint node stated either assertion; the only relevant exact source was this item. I searched the Lean source by item id and by the cohomology terms. LeanFinder found `continuousCohomology` on topological modules and Loogle found `TopRep` cohomology; neither states a derived-invariants comparison for the discrete-module category. The pinned Mathlib file `Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean` confirms the difference and explicitly leaves related comparison work as TODOs. LeanSearch and the whole-tree Mathlib grep could not run successfully on this machine, so I left both new nodes unsplit and recorded that limitation honestly. No return was received for this item; the corrections made during this review were to isolate the two mathematical assertions, add the precise 04JF source for injectives, and keep the cochain comparison as an obligation instead of treating Stacks' unsupported final sentence as a proof.
