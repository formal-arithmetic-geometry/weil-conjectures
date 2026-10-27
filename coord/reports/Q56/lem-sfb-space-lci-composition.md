# Worker report: lem-sfb-space-lci-composition

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-space-lci-composition.json`: item, statement; split into six proof steps, statement unchanged, no Mathlib match.
- `lem-sfb-koszul-immersion-composition.json`: new statement-only node; no Mathlib match. Koszul-regular immersion composition without Noetherian assumptions.
- `lem-sfb-lci-polynomial-local-factorization.json`: new statement-only node; no Mathlib match. Polynomial immersion charts for an lci scheme map, including a prescribed target open.
- `lem-sfb-scheme-lci-etale-locality.json`: new statement-only node; no Mathlib match. The scheme lci condition is etale local on source-and-target.
- `citations.json`: one verbatim statement quote for every cited node of every item step.
- `searches.jsonl`: actual msearch results, retained unmodified. `write_split.py` is a sandbox-only preparation script, not a delivered project file.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, local-complete-intersection names, lci composition, and Koszul-regular immersion composition, and read the hits. The source has unrelated Koszul duality and smooth-over-field results, not the theorem here. The read-only slopmaster2 search also found no exact attachment. No Lean was written or compiled.

## WANTED

None. All sources used are present in `literature/stacks-project/`.

## Findings and corrections

The item's mathematical statement is correct and retained verbatim. Its imported proof was empty. Stacks 06C8 omits the proof with the instruction to use the scheme version 069J; this delivery supplies that reduction and actually carries out 069J's polynomial ambient construction. The etale clause has a direct identity/empty-sequence factorization and does not need new syntomic or flat-lci equivalence nodes. This is the definition of lci applied to the smooth chart map, not a different mathematical route.

The new polynomial-factorization node is an existence result about one lci map, not the composition assertion or one of the item's conclusions. The locality node is a descent theorem about one scheme map and arbitrary chart choices. Koszul-regular immersion composition is the genuinely smaller immersion input to the construction. None moves an entire item clause to a new node. Polynomial base change is proved coefficientwise in the item rather than turned into a fourth node: its Koszul differential acts separately on each monomial coefficient, and a cycle involves only finitely many coefficients. No derived comparison or unproved tensor-exactness assertion is hidden there.

The ancestor command reports `blueprint.from.node = None` for this inherited chain; that existing maintainer-owned value is preserved on the item and used on its children as the command instructs. Each new node has the complete inherited place plus the specific 06C8/069J proof input. I read the current latest unit section at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, the recorded unit and chapter, and the inherited detailed route in the item. No unit or chapter route has been changed. Whole-blueprint searches for `lci`, `local complete intersection`, `local complete`, `Koszul-regular immersion`, `polynomial factorization`, `06C4`, `067Q`, `069E`, and `069N` found no equivalent blueprint node. Searches for the tags and keywords in the whole DAG likewise found no duplicate of any new statement.

## Not duplicates

lem-sfb-koszul-immersion-composition vs lem-sfb-regular-immersion-composition: the existing node is Tag 067Q assertion (1), finite regular sequences; the new node is assertion (2), finite Koszul-regular sequences, without assuming that Koszul regularity implies regularity.

lem-sfb-koszul-immersion-composition vs lem-per-regular-lci-geometric-calculus: the existing node assumes Noetherian schemes and concerns regular immersions with codimension and smooth-geometric consequences; the new node only concerns Koszul-regular immersion composition and permits arbitrary schemes.

lem-sfb-koszul-immersion-composition vs def-per-regular-closed-immersion-codimension: the existing node defines a regular closed immersion and a sourcewise codimension function; it asserts no composition theorem and uses regular rather than Koszul-regular sequences.

lem-sfb-koszul-immersion-composition vs def-sfb-relative-finite-hilbert-groupoids: the existing node defines relative Hilbert groupoids and the lci condition; it does not state stability of Koszul-regular immersions under composition.

lem-sfb-koszul-immersion-composition vs lem-pur-smooth-pair-regular-immersion: the existing node produces regular equations for a closed immersion between two smooth schemes over a common base; the new node assumes two Koszul-regular immersions, does not assume smoothness, and proves their composition is Koszul-regular.

lem-sfb-scheme-lci-etale-locality vs lem-sfb-scheme-unramified-etale-locality: the existing statement is the three locality conditions for unramifiedness; the new statement is those conditions for relative Koszul lci, with different hypotheses and conclusion.

lem-sfb-scheme-lci-etale-locality vs def-sfb-relative-finite-hilbert-groupoids: the existing node gives an existential chartwise definition of space lci as part of its Hilbert-groupoid definitions; it does not prove source-and-target locality or invariance under arbitrary compatible charts.

lem-sfb-scheme-lci-etale-locality vs lem-sfb-space-relative-lci-parameter-open: the existing node assumes two flat locally finitely presented space maps and closedness of a source point map, and produces a universal open subset in a parameter space; the new node treats unrestricted scheme lci and its etale chart locality, not any parameter locus.

For further nearby nodes, `lem-sfb-unramified-lci-koszul-etale-charts` requires formally unramifiedness and produces closed immersion charts; it does not assert arbitrary lci polynomial charts or lci etale locality. `lem-sfb-lci-etale-pointwise-invariance` is over a field and compares complete-intersection local rings, not relative Koszul lci maps. `lem-sc-koszul-regular-flat-base-change` concerns a sequence under a flat ring map, not composition of immersions; the polynomial case needed here has its explicit elementary proof. `lem-sfb-syntomic-smooth-composition` assumes flat maps and cannot establish the nonflat item. `lem-sfb-space-etale-presentation-property-criterion` requires the scheme property already be etale local and does not itself prove this for lci.

## Mathlib searches

Each new node has recorded LeanFinder, LeanSearch, Loogle and grep searches, with a second semantic phrasing. Queries and results were read and copied from the msearch log; no search was invented. Services returned usable results. Search hits for ordinary immersion composition, smooth composition, regular/weakly regular sequence concatenation and generic descent lack the required Koszul assertion. I read the returned scheme morphism source files and `Mathlib/RingTheory/Regular/RegularSequence.lean`, whose line 21 explicitly lists Koszul regular sequences as TODO. The existing etale-implies-smooth node and smooth-composition node are reused instead of duplicating the matching pieces. The item is not a Mathlib leaf: its unrestricted algebraic-space lci composition is not a one-line specialization of those pieces.

## Review by Q56

I checked delivery-errors B through E against the actual sources and every node statement used. For the item I read spaces-more-morphisms.tex 06C8, the preamble and definition 06C4, and the complete scheme proof more-morphisms.tex 069J. I also read 06C9, spaces-morphisms.tex 04XX and 06CP to compare the imported etale route. For the new immersion node I read divisors.tex 067Q (2) and its reference to concatenating Koszul-regular sequences; assertion (1) is intentionally not substituted. For the polynomial node I read more-morphisms.tex 069E, the paragraphs around 069F and 069G: factorization independence allows the chosen polynomial immersion, and the assertion is local near the point, so it needs neither separatedness nor a global closed embedding. For the locality node I read the explicit preamble to spaces-more-morphisms.tex 06C4 and its cited results more-morphisms.tex 069N, 069P and descent.tex 04R2. The new nodes have statements only, with all objects and notions introduced and their definition dependencies named.

Step 1 uses the new locality statement to satisfy the hypothesis of the existing presentation criterion. I opened that criterion and checked both its every-chart conclusion and its existence clause. I also opened the existing unramified/etale-compatible-charts node: its atlas-existence clause applies to every space map without assuming unramifiedness, so applying it successively to g and f constructs U -> V -> T with all three required surjective etale atlases. The algebraic-space definition supplies the first scheme atlas. The Hilbert-groupoid definition really does state the existential chartwise lci condition, including the empty sequence. Thus this step does not infer every-chart testing merely from a definition.

Step 2 uses exactly the local closed-immersion/smooth factorization in the Hilbert-groupoid definition and the new polynomial chart existence theorem. The target open V_0 contains a(u), as required, and the new theorem gives U_0 mapping into that same V_0. Step 3 uses affine-space, closed-immersion and Koszul-sequence definitions only; on every affine patch where a finite list generates I, the polynomial quotient has kernel IA[t], and the finite coefficient argument proves all positive-degree exactness. This is two lines of algebra after expanding the differential and does not assume f or g flat. Its use of Tag 067P is explicitly proved for this special polynomial base change, rather than an uncited general flat base-change theorem.

Step 4 applies the new Koszul-immersion composition node to precisely i-prime and its polynomial thickening j. I opened `sbc-lem-affine-space-smooth`, `lem-trf-smooth-composition` and `lem-pc-open-immersion-smooth-composition`: their statements give respectively the smooth projection, the smooth composite to T, and its restriction to the ambient open. The final ambient open is necessary because a polynomial immersion need not be globally closed; after taking it, the definition's closed-immersion condition is satisfied. The first and third existing smooth nodes used here are tools, not substitute lci arguments. Step 5 applies only the sufficient surjective-source direction of the presentation criterion, already justified for the lci property in step 1.

Step 6 opens `lem-sfb-unramified-etale-compatible-charts` for the scheme etale chart and `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` for smoothness; only the smoothness clause is used, with no hypothesis on a field. I checked the empty Koszul complex directly and the identity closed immersion from the definition. The presentation criterion then gives the desired space assertion. The two non-Mathlib off-unit tools (affine-space smoothness and etale-implies-smooth) are declared in `split_report.tool_uses`; the smooth-composition and open-restriction nodes are Mathlib leaves.

I tested the statements and the construction on empty source/empty target charts, identities, n=0, empty Koszul sequences and arbitrary zero rings. Zero-length factors give identity embeddings; empty schemes make the pointwise conditions vacuous. A quotient k[t] -> k at t=0 demonstrates why the argument must allow nonflat lci maps: only the polynomial ambient projection is used in base change, and its exactness argument does not demand this quotient be flat. Nothing assumes regular equals Koszul-regular outside the Noetherian setting. No step is longer than 2000 characters, and no step contains a hidden non-elementary comparison. `citations.json` quotes the actual statements for every uses-entry; I checked those quotations literally. All statement dependencies are used by their statements, proof_deps is the exact union of uses, and no edge to a user of this item was introduced. No SGA source is used.

## Unfinished work

No part of this item's one-level split remains unfinished. The three new lemmas are intentionally unsplit queue items. Required server dry-run and delivery results are recorded below when complete.

The first dry run stopped at duplicate-tag review. I opened all additional listed statements and added the six explicit pair comparisons above; none states the new fact. No mathematical statement was changed in this repair.
