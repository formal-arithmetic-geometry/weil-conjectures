# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-approximation-opcycle.json`: existing statement, now split in six steps; statement and statement dependencies unchanged. Mathlib searches found no exact declaration or one-line specialization.
- `citations.json`: fourteen step/node citations, each quoting the cited statement verbatim. This is the sandbox verification artifact consumed by delivery.
- `report.md`: this report.

## New nodes

None. Zero new nodes and zero new Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, approximation/opcycle keywords and flatness. The general categorical `ObjectProperty.flat_opcycles_of_exactAt` assumes universal ordinary tensor exactness, which is a fact this item must derive. `Module.Flat.opcycles_of_exactAt` is for ordinary modules; `FlatModelOpcyclesFlat` concerns schemes and stalks. None states the arbitrary-ringed-site approximation assertion with all its hypotheses. They are not attachments.

## WANTED

None. The relevant Stacks source is available locally.

## Audit and changes

Read the chapter and unit records, the current latest blueprint's `sk-thm-sf-ctf-stability/_section.md`, and `sk-thm-sf-ctf-stability-direct-images.proof.md`, particularly (3), along with the inherited item and its parent perfectness criterion. This is supporting algebra in the existing prerequisite chain, not a replacement for the six-functor route. `blueprint_refs.py ancestor` prints None for this pre-existing chain; retained its existing provenance and supplied the precise source place. Whole-blueprint searches for flat approximation and opcycles found no equivalent assertion; the constant-projection approximation hit has different objects and conclusion.

Read `sites-cohomology.tex`, Tag 08G7, label lemma-perfect-precise, from its statement through the flatness conclusion for E-prime. The item isolates exactly this part, before finite presentation is used to obtain a finite-free retract. The proof expands its cone/kernel argument by a flat resolution of the kernel, and is honestly marked agent-written. Read also the bounded-flat K-flat lemma 06YQ, the K-flat resolution construction 06YS, the derived-tensor definition/construction 06YU, and the cokernel argument 08G0. The statement needs no correction and no finiteness hypothesis has been imported.

The first draft incorrectly claimed the spliced complex mapped to P by identity in the retained degrees and zero below: its chain-map equation at a-2 would require the kernel inclusion to vanish. Corrected before delivery: the actual chain map goes to the good lower truncation tau_ge_a P, using the cokernel quotient in degree a. Functorial truncation of the supplied derived morphism then compares this object to K. The proof never assumes f has a chain-map representative. No earlier delivery was run.

The search log records six actual msearch calls, with two semantic phrasings, LeanSearch, Loogle and two source regexes. Read the returned module-flatness criteria and general resolution/truncation candidates; the former apply to modules over a ring and the latter do not imply the item in one line. Kept the item's inherited searches and added only queries actually present in this sandbox's searches.jsonl. No unavailable service was reported as a negative result.

## Review by NF

I checked B through E against the actual statements and source text, rather than against dependency names. There are no new-node statements to validate or duplicate pairs to distinguish. The item introduces the ringed site, coefficient ring sheaf, degrees, derived object and approximation; its original TeX and all hypotheses are retained. Its proof uses only existing nodes, with the generic off-unit tools explained in split_report.tool_uses.

Step 1 uses the statement of lem-pc-kflat-resolution to choose a flat-term K-flat representative of K. The statement of lem-sf-ringed-kflat-single-tensor-comparison explicitly permits a nonflat degree-zero second factor, so it applies to the unit sheaf; the tensor-unit clause of lem-pc-sheaf-modules-tensor-closed gives the explicit inverse maps. Thus the Tor test really gives ordinary cohomology vanishing of K.

Step 2 uses lem-pc-kflat-bounded-flat-replacement, which explicitly preserves a specified upper bound, supplies flat terms, and has a termwise epimorphic quasi-isomorphism. Applied to Z[0] with bound zero, it gives the augmented flat resolution used here. I checked the index E^j=F^(j-a+2), its joining differential, both zero composites, and bounded-aboveness from boundedness of P. No projective or locally free resolution is presumed.

Step 3 uses only the explicit good-truncation definition and retained-cohomology assertions of def-kun-truncations and the cohomology/quasi-isomorphism/localization definitions in def-weil-abstract-derived-category. The quotient map to T is a chain map because q d=0. The augmented resolution kills cohomology below a, including degree a-1; at degree a the quotient kernel is ker(d_P^a)/im(d_P^(a-1)). Above it the complex agrees with P. This is the elementary calculation, fully written, rather than a hidden identification lemma.

Step 4 uses the truncation functors and adjoint units actually stated in lem-weil-heart-short-exact-triangles(1), and the retained-cohomology assertion of def-kun-truncations. Truncation therefore acts on the given derived morphism f. Both its truncation and the unit on K are isomorphisms on every cohomology. I checked the often-missed bounded-below hypothesis of lem-weil-pbc-derived-plus-iso-on-cohomology: E, T, K and tau_ge_a K have zero cohomology below a, and def-weil-pbc-bounded-derived-subcategories identifies D-plus as a strictly full subcategory. E may be unbounded to the left as a complex; that does not violate this cohomological condition. No unbounded conservativity assertion is taken from a bounded-below lemma.

Step 5 uses the exact bounded-above flat-to-K-flat statement of lem-weil-pbc-independent-bounded-flat-kflat and the explicit single-tensor comparison of lem-sf-ringed-kflat-single-tensor-comparison. The assumptions on site size and the coefficient sheaf match those of the item. Tensoring a derived isomorphism is functorial. Degree a-1 lies strictly below the input Tor interval. The symmetry in lem-pc-sheaf-modules-tensor-closed supplies the order of factors required by the next criterion, with no total sign since N has degree zero.

Step 6 uses the statement of lem-weil-pbc-site-flat-opcycles-tor-criterion, which is for arbitrary small ringed sites, all-flat complexes and universal ordinary tensor exactness at n-1. All three requirements hold for E with n=a. It concludes flatness of coker(d_E^(a-1)); the very same objects and differential occur in P, so the claimed sheaf is exactly Q. I did not use the ordinary-module analogue, any stalkwise test, or enough points. In particular the proof does not mistakenly assert H^(a-1)(P tensor N)=0: the lower kernel of P may survive tensoring, and it is the resolved complex E to which the criterion applies.

Small cases checked: a=b still gives vanishing at a-1 and the same argument; P with only a flat term in degree a has Z=0 and returns that term; an acyclic two-term flat P gives the same cokernel computation; P=0 gives Q=0. Over the one-point integer site, the complex Z --2--> Z in degrees a-1,a has nonflat cokernel Z/2 and cannot meet the amplitude hypothesis with lower endpoint a (tensor with Z/2 detects degree a-1); thus the proof does not falsely certify this standard counterexample. If P has a nonzero lower kernel, the flat resolution removes exactly that kernel and leaves the differential whose cokernel is tested untouched. None of these checks needs flatness of Z, nor finite generation of P's terms.

Every proof step is shorter than 2000 characters, and I reviewed the actual constructions for hidden lemmas regardless of length. Every cited use has a verbatim statement in citations.json. No new statement-only node rephrases a clause of the item; all six steps carry its argument. The server review_split check passed with zero new nodes. No Lean file was written and no compiler or build command was run.

## Unfinished work

No mathematical work remains in this split. Full delivery dry run and push follow this report; any failure is repaired before delivery.
