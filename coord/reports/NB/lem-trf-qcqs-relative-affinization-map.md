## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-qcqs-relative-affinization-map.json` (statement; split in five steps; no exact Mathlib match), `citations.json`, and this report. The msearch service wrote `searches.jsonl`.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. All supporting statements already exist. In particular, the compatible-local-maps node applies to an arbitrary source morphism, not only an affine source; using its actual statement avoids manufacturing a relative-Spec universal-property node or restating the item's canonical-map clause.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item blueprint tag and by relative spectrum/affinization found no declaration covering the whole item. `AlgebraicGeometry.affine_algebra_local_maps` in `WeilConjectures/AlgebraicGeometry/AffineAlgebraLocalMaps.lean` is an existing helper, not an attachment for the item. Likewise `affine_morphism_relative_spec` supplies relative spectra but not the arbitrary-source map in this item.

## Sources and searches

Read `literature/stacks-project/constructions.tex`, Tag 01LY (`lemma-canonical-morphism`), Tag 01LT (`lemma-spec-affine`, especially the inverse construction from an algebra map), and Tag 01LX (`lemma-spec-properties`). Read Schemes Tag 01LC (`lemma-push-forward-quasi-coherent`) and Morphisms Tag 01SA (`lemma-affine-equivalence-algebras`). The existing local-maps statement and its project proof were opened to check that its overlap and section-map clauses apply without affineness of the source. The gluing statement was also opened. The proof expands the identity-algebra construction of 01LY by affine-base local maps and gluing; it does not assume that an anti-equivalence restricted to affine sources already represents maps from arbitrary sources.

Whole-DAG statements and source tags were searched for relative spectrum and pushforward quasi-coherence. `tools/blueprint_refs.py search` was run for `relative spectrum`, `affinization`, `structure sheaf`, and `canonical morphism`; no imported blueprint node states this item exactly. The ancestor command gives `lem-trf-local-term-locality`; its recorded blueprint update and the immediately preceding relative-Spec embedding split were read. This item supplies the relative-affinization construction explicitly used by the latter's step 2, in Stacks 01SM (2) implies (4), on the existing chain to the geometric quotient presentation. The unit and chapter records were read and preserved.

All fresh Mathlib searches used the prescribed msearch command and their exact queries and output summaries are retained in `mathlib_searches` and `searches.jsonl`. Both semantic phrasings were read: one returns normalization and its local maps, which use integral closures rather than the direct image algebra; the other returns affine morphism and affine-chart infrastructure. Loogle's `AlgebraicGeometry.Scheme.toSpecΓ` is the absolute map only. LeanSearch returns absolute Spec/Gamma and quasi-affine results. The grep results include `Modules/Tilde.lean:567,587`, whose surrounding source was read: they do not assert qcqs relative affinization. `GammaSpecAdjunction.lean:466` was read for `Scheme.toSpecΓ_appTop`, which identifies the absolute identity-section map but does not give the relative construction. These hits do not make the item a one-line Mathlib leaf. The inherited searches from the item's creation are preserved separately, including the inherited unavailable LeanSearch result; the fresh LeanSearch call succeeded.

## WANTED

None.

## Problems found and changes

The statement is correct as written and is unchanged. The imported item had no proof. No statement dispute or route change is needed. All non-elementary facts now cite existing statement nodes; no new node duplicates an existing fact or restates a clause of the item. In particular, the proof does not assume affine intersections of arbitrary affine opens, nor affineness of inverse images under the arbitrary qcqs source morphism. The algebra map used to construct the scheme map is explicitly the inverse of the relative-Spec structure-algebra isomorphism, so the final chart identity has the correct variance.

## Unfinished work

None for this one-level split. Its existing dependencies retain their own states; no Lean was written or compiled.

## Not duplicates

No new nodes, hence no new/existing pairs to distinguish.

## Review by NB

I checked the item's hypotheses and all clauses against 01LY: it needs only a quasi-compact quasi-separated morphism of schemes, produces a quasi-coherent direct-image algebra, a relative spectrum, and a map over the original base, with the canonical-map formula over every affine base open. The additional chart notation is precisely the compatible structure-algebra chart of 01LX and the existing relative-Spec node, rather than a strengthened geometric conclusion. No finite-type, separated, Noetherian, nonempty, or affine-source hypothesis was introduced.

In step 1 I read the statements of `def-weil-pbc-comm-algebra-sheaf`, `lem-weil-pbc-spec-tilde-free-module`, `pqf-def-coherent`, and `pqf-lem-pushforward-qcoh`. The first describes an algebra as a ring sheaf with its structure map, so f-sharp supplies the algebra data. The free-module lemma at rank one supplies the affine structure-sheaf identification; the definition makes this quasi-coherent locally; and the pushforward statement has exactly the given qcqs hypotheses and gives quasi-coherence of the desired underlying module. This avoids citing merely a definition as if it proved pushforward preservation.

In step 2 I read clause (2) of `lem-weil-pbc-affine-morphism-relative-spec`: it supplies both the algebra isomorphism and the fact that the morphism corresponding to its component on each affine open is an isomorphism. Thus the step takes the chart property from the statement itself, not from a construction buried in its proof. Step 1 verifies its sole extra assumption, quasi-coherence of the algebra.

In step 3 I read every clause of `lem-weil-pbc-affine-algebra-local-maps`. Its hypotheses distinguish the arbitrary source f from the affine target g. Taking g to be pi and alpha to be a inverse satisfies them. Its statement explicitly supplies the factorization over S, compatibility on all overlaps, and the section-map normalization. The proof uses all three, and uses no extension of the affine anti-equivalence to nonaffine source objects without justification.

In step 4 the statement of `lem-weil-pbc-scheme-morphism-gluing` gives both existence and equality from agreement on an open cover. The cover condition follows pointwise from the affine neighbourhoods in the scheme definition. Step 3 already supplies overlap equality, so no unproved affine-intersection assertion is needed. Applying the uniqueness clause to pi composed with c and f proves the base equation as an equality of scheme morphisms, not merely an equality on points.

In step 5 I checked the direction of both section maps: a_U goes from A(U) to sections on Y_U, whereas the local section map supplied by step 3 is a_U inverse. Their composite is literally the identity on A(U), with the standard restriction-to-open-subscheme identifications made explicit. `lem-weil-pbc-morphism-into-affine-scheme` asserts a bijection for any scheme X_U and any commutative ring, so injectivity identifies this composite with the canonical map defined by the identity, including when X_U is not affine. This calculation is the full chart clause, not just existence of an unspecified factorization. `citations.json` contains a verbatim quote from the actual statement of each node in each step's uses list.

I tested the empty source: A is the zero ring sheaf, the relative spectrum is empty, and the maps and chart identity are the unique maps on empty schemes. For f the identity, the structure algebra and its chart maps reduce to the structure sheaf and the usual affine identifications. For the structure morphism of a nonaffine proper scheme with only constant functions (for example projective space over a field), c need not be an immersion; the proof asserts no such condition and the Gamma-Spec bijection still applies. I also checked that a nonseparated base causes no problem: overlaps are handled by the existing local-maps theorem rather than presumed affine. None of the five proof steps exceeds 2000 characters or hides an additional local comparison lemma. All proof dependencies are pre-existing Mathlib leaves or recorded Lean-closed nodes, except definition nodes, so no off-unit route replacement or additional tool-use authorization is needed. There was no previous delivery to repair; the main corrections during self-review were explicitly using rank-one tilde quasi-coherence, choosing a inverse in the correct direction, and spelling out the final section-map composition.
