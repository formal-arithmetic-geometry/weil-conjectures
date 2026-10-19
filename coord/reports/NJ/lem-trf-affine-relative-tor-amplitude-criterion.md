# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-relative-tor-amplitude-criterion.json`: item, split into six proof steps; statement unchanged; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-relative-tor-amplitude-localization.json`: one new statement-only lemma, Stacks 0B67 (1) iff (2); not in Mathlib after the recorded searches.
- `citations.json`: 18 step/node entries, each quoting an exact substring of the cited statement.

No Mathlib leaves. No Lean or unit file was written, and no compiler, Lake, build, local preflight or local DAG checker was run. The chapter, unit and historical blueprint ancestry are retained.

## Attachments

None. I searched the node id, relative Tor amplitude / tor dimension, and the algebraic localization notions in the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`, and checked the master reference tree. There is no declaration stating the item or the new algebraic complex criterion. Existing categorical Tor statements and the absolute affine criterion do not state the relative assertion. The source checkout's sorried declarations are not treated as completed proofs.

## Literature wanted

None.

## What was wrong and what changed

The item was an unsplit statement-only child of the already reviewed affine relative-dualizing comparison. Its statement agrees with perfect.tex, Tag 0DHY, `lemma-tor-dimension-rel-affine`, including the unrestricted ring map and unbounded complex. Its extra inverse-image-test sentence is true, but needs a proof: at a chosen image point any module over the base local ring is the stalk of a module skyscraper. Step 4 supplies that argument. There is no STATEMENT-DISPUTED and no statement weakening.

I did not replace the relative criterion by the existing absolute criterion. In the former, the base for tensor is R and the sheaf of rings is f-inverse O_V; in the latter it is A and O_U. I also did not invoke an absolute-O_U open locality theorem on the different inverse-image ring. Instead Steps 2 and 5 use the existing ringed-space K-flat stalk computation, on the actual ringed space and on its open subspaces.

The inherited Mathlib searches are retained. Additional searches in searches.jsonl were made through msearch.py, with exactly their actual query texts recorded. The new child's searches include LeanFinder, Loogle, grep and LeanSearch, and a second semantic phrasing. All services used for those recorded searches returned; an unknown Loogle identifier is recorded as zero hits with that diagnostic, rather than a fabricated theorem. The returned flat/free-locus, localization and exactness results are only ingredients; none states the relative derived-tensor amplitude equivalence. No unexecuted query is claimed.

## Not duplicates

lem-trf-relative-tor-amplitude-localization vs lem-pc-affine-sections-tor-bound-stalk: the existing node treats the coordinate algebra in degree zero and only an upper homological Tor bound, in the forward direction; the new node treats arbitrary unbounded algebra-module complexes, both endpoints of an arbitrary cohomological interval, and both directions.

lem-trf-relative-tor-amplitude-localization vs lem-pc-tor-vanishing-localized-algebra: the existing node localizes the regular coefficient algebra B in one Tor degree; the new node detects relative amplitude of any complex and localizes the base as well.

lem-trf-relative-tor-amplitude-localization vs lem-pc-tor-vanishing-localized-base: the existing node concerns two modules already over one localized base and one implication in a single Tor degree; the new node is the equivalence for arbitrary algebra-module complexes at all source primes.

lem-trf-relative-tor-amplitude-localization vs lem-pc-tor-localization-denominators: the existing node clears denominators for a class in Tor of a degree-zero coefficient algebra; it does not detect a complex's Tor amplitude over contracted base primes.

lem-trf-relative-tor-amplitude-localization vs lem-pc-localized-polynomial-tor-bound: the existing node assumes a Noetherian base and a finite module over a localized polynomial algebra and changes the bound by the number of variables; the new node assumes none of these and preserves the same interval.

lem-trf-relative-tor-amplitude-localization vs lem-pc-polynomial-tor-bound: the existing node compares a base ring with a polynomial ring and shifts a bound; the new node is a prime-localization equivalence for a general ring homomorphism and an arbitrary complex.

lem-trf-relative-tor-amplitude-localization vs lem-pc-affine-tor-amplitude-criterion: the existing node compares sheaves on Spec A with A-module tensors; the new node is exclusively algebraic and compares the base R with contracted base-prime rings after source localization.

lem-trf-relative-tor-amplitude-localization vs lem-trf-affine-relative-tor-amplitude-criterion: the new node is Stacks 0B67's algebraic input, with no schemes, inverse-image ring, sheaves, inverse-image tests, or local-to-global finite-interval clause. The item's proof still establishes all geometric identifications and the finite-cover argument; it is not an application of a renamed geometric clause.

The whole-DAG tag search for 0B67 produced the six first existing nodes listed above. Whole-DAG keyword searches also found the absolute affine criterion, affine quasi-coherent test criterion, and relative stalk tensor comparisons, which were read and reused where applicable. `tools/blueprint_refs.py search` for `0B67`, `Tor amplitude localization`, and `affine relative Tor amplitude criterion` found no blueprint node stating the proposed child. The broader `relative Tor` search found the purity divisor-class node, about a different coefficient and geometric construction. The new child's id and the item's exact id/tag were also searched in the blueprint and project Lean sources. Both same_as fields are empty; the new child's from.node and via list follow the ancestor command.

## Proof idea for the statement-only child

Source read: more-algebra.tex, Tag 0B67, `lemma-tor-amplitude-localization`, including its displayed localized cohomology identity. The base A and algebra B there are renamed R and A here. The source gives exactly the equivalence of the two conditions of the child; the maximal-ideal version is unnecessary.

One way to fill the omitted forward implication later is to resolve a test module L by a bounded-above free R-resolution P. Its localization P_p is a free R_p-resolution of L when L is already an R_p-module. Tensoring the unrestricted A-complex with P computes its derived tensor, and exact source localization gives the same tensor with K_q and P_p. Thus a global vanishing gives the localized one, without requiring K or A to be R-flat. Conversely, resolve an R-module N by such a P. For every q the localization of H^i(K tensor_R P) is H^i(K_q tensor_{R_p} P_p). The assumed local amplitude kills these localizations. An A-module whose localizations at all primes vanish is zero (a nonzero element has a proper annihilator contained in a maximal ideal). That is the source's converse proof. This explanation is deliberately in the report: the new node itself has no proof or proof dependencies.

## Review by NJ

I read perfect.tex 0DHY and cohomology.tex 09U9 in the local literature, and verified the same statements on the Stacks tag pages. For the new node I read more-algebra.tex 0B67 and its tag mapping. I checked the current main-20261015 blueprint's local-term proof and the inherited auxiliary ancestry through the affine coherent relative-dualizing comparison. This split only supplies its generic relative Tor input; it does not replace a step of the local-term unit, change a chapter or unit, or introduce any SGA source. The generic off-unit tools are explained individually in split_report.tool_uses.

Step 1: I opened the statements of lem-pc-kflat-resolution, lem-pc-inverse-image-structure-stalk-iso, lem-weil-pbc-spec-tilde-stalk-localization, lem-pc-relative-inverse-image-stalk-restriction and lem-weil-pbc-module-stalk-exact. The first applies to any ringed site, so it applies to B=f-inverse O_V, not just O_U. The ring-stalk node explicitly identifies the canonical structure map, and the scalar-restriction node explicitly treats an arbitrary complex; these are the needed hypotheses. The tilde node supplies the actual module localization at the source prime and the ring localization. Its germ formula is natural for every differential, so using it degreewise produces the complex identification. Exact stalks preserve the chosen quasi-isomorphism. No derived affine equivalence is used to assert a stalk compatibility it does not state.

Step 2: I opened lem-pc-stalk-kflat-tensor-homology, the exact-stalk node, the module-skyscraper definition and lem-pc-skyscraper-complex-stalk-recovery. The tensor statement allows any ringed space, any test sheaf and any integer degree, with exactly the chosen K-flat representative and a ring-stalk isomorphism. Therefore it gives the displayed comparison after Step 1. It produces the actual stalk module, not all modules automatically. The converse supplies that missing quantifier using the skyscraper recovery statement. The exact-stalk zero test is applied to 0 -> H^i -> 0; it is not an uncited general assertion about sheaves. This proves the stalk criterion inside the item from the existing comparison; a duplicate stalk-criterion child was unnecessary.

Step 3: I matched both conditions of the new 0B67 statement word for word with the localized condition in Step 2 and with the item's module condition. The contracted prime and base R_p, not A_q as tensor base, agree. This is the substantive algebraic lemma left to split later and it is strictly smaller than the geometric item.

Step 4: I reopened the skyscraper recovery, inverse-image stalk statement and module inverse-image definition. The inverse-image theorem is stated for abelian groups and commutative rings, so I use its abelian formula only. The module scalar compatibility is written out from the definition: choose representatives on a common neighbourhood, multiply them, then take the germ. This explains why the abelian isomorphism is linear over the canonical ring-stalk isomorphism. Every R_p-module L is available as the base skyscraper stalk, even if p is not closed. The sheaf can be non-quasi-coherent. Thus the restricted inverse-image tests really detect every localized tensor test.

Step 5: I checked that the ringed-space K-flat theorem and skyscraper recovery apply on every ringed open subspace. Stalks at points inside it agree by the cofinal neighbourhood system. No assertion that inverse-image tests stay globally quasi-coherent or that all opens are affine is used. The affine-scheme qcqs statement supplies quasi-compactness of U alone. A nonempty finite subcover allows min a_j and max b_j; if U is empty I explicitly choose [0,0]. The same fixed interval works for all test modules because the local hypotheses quantify over all modules before choosing the cover. The argument repeats the previously proved stalk criterion, rather than hiding a new uniformity theorem.

Step 6: This is the reverse finite-interval implication and uses the already proved fixed-interval equivalence on U itself, so it is elementary and has no external citation. I checked M=0, A=0 (empty source), the identity map R=A, arbitrary shifts, and singleton intervals. For a nonflat test, R=Z, A=F_p and M=A has amplitude [-1,0] and does not have amplitude [0,0]; both the global and the unique stalk test detect Tor_1 with F_p. For R=A=k[e]/(e^2), M=k in degree zero has unbounded negative derived tensors with k; neither condition incorrectly infers finite Tor dimension from its bounded ordinary cohomology. For an unbounded complex over a field with nonzero cohomology in arbitrarily many degrees, the degree-zero test module k immediately defeats any finite interval. These checks cover the unrestricted hypotheses of the new lemma and item.

For B1-B10, the child is self-contained, statement-only, and has the correct tag/label, no proof sketch in its statement, no Mathlib match claim and no unsupported search record. Its derived, localization and K-flat notions cite existing nodes, and amplitude is defined inline by universal vanishing. All six same-tag candidates were read and distinguished above. For C1-C8, every non-elementary input of each step has an actual node and a verbatim quote; no proof of another node is used as its statement. The off-unit citations are general tools on the retained route. For D1-D5, the child is algebraic 0B67 rather than a geometric clause of 0DHY, and the item carries the stalk, inverse-image and finite-cover arguments. For E1-E7, the hypotheses and scalar rings were checked at their uses as described above. No step exceeds 2000 characters; the longest is about 1250 characters and none hides an auxiliary comparison beyond the cited statements and the written germ/cofinality arguments.

Corrections made during self-review: I removed the temptation to cite the absolute affine criterion for a relative-base statement; I kept the actual inverse-image ring in every K-flat comparison; I wrote the all-modules stalk test using skyscrapers instead of claiming that the stalk tensor comparison alone supplied all modules; and I separated the empty-source case before forming extrema. The item statement needed no correction.

## Unfinished work

The item is fully split. The new algebraic localization lemma is intentionally unsplit, as required for a one-level split. No other mathematical gap is left in the item's proof.

## Validation

The remote srvcheck.py check_dag invocation exited 0: no finding introduced by the sandbox or on its nodes. The required deliver.py --no-push invocation exited 0 and printed OK (not pushed) at 38a8a975f8: preflight passed. It ran the server preflight, including DAG and split review checks. The dry run had no mathematical or structural failure to repair. The push invocation is the next step; no concurrent deliver.py invocation is active.
