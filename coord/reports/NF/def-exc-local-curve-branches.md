# Worker report: def-exc-local-curve-branches

## Files written

- `dag/nodes/sec-smooth-purity/def-exc-local-curve-branches.json`: definition split using seven existing ingredient references; no whole-item Mathlib match. All original hypotheses, both products and the structural map are preserved.
- `citations.json`: `[]`, since this definition has no proof steps.
- `report.md`: current repair report and substantive self-review.
- `dependency-snapshot.json`: current statements, statuses and SHA-256 hashes of every cited node, for the second reader. This is sandbox evidence, not a delivery node.

New nodes: 0. New Mathlib leaves: 0. The five existing Mathlib leaves are the Noetherian, Krull-dimension, finite-minimal-prime, localization and integral-closure references. The two original scheme-normalization references remain explanatory references.

## Attachments

None. Read-only searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `/home/ubuntu/weil-newtargets-master/WeilConjectures` and `dag/lean_names_upstream.json` for the item id, `branchAlgebra`, `normalizationAlgebra` and `localCurveBranches` returned no declaration defining the complete pair of products and its structural map. I read the normalization declarations and docstrings at `WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean:179–190,296–309`. They construct scheme normalizations, rather than this ring-valued branch algebra. No upstream sorry declaration was counted as finished.

## Wanted sources

None. The shared checkout lacks its untracked literature payload, but the actual sources are available read-only under `/home/ubuntu/weil-launcher-nt/literature/`. I read the complete master blueprint file `blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-exc-local-curve-branches.md`, both cited normalization blueprint definitions, and the Stacks sources and tag index identified below. This resolves the previous report's source-availability limitation. No download or write to any literature directory was needed.

## Return repaired

The return reports an operational refusal: `coord/.merge.lock` remained held for 120 seconds by another item's merge. Its requested repair is to rebuild on the current DAG, reread changed citations and adjust the split before redelivery. The brief assigns this worker the no-push handover; the fresh second reader performs redelivery.

I reread all seven current dependency statements, rather than assuming that the previous approval survives changes to the DAG. Their current statements still supply every ingredient used here. `dependency-snapshot.json` records exactly the versions inspected; no old dependency snapshot was available in this sandbox, so I do not claim a historical byte-for-byte comparison. No dependency must be renamed or replaced.

This is not an unchanged re-push. The sandbox now specifies that the list contains all minimal primes, expands the prime-ideal condition explicitly, identifies the exact defining display and structural-map paragraph in `source.place`, and replaces the stale source-unavailability assertion in `split_report` with an actual comparison against the master source. Fresh wrapper searches and their verdict are recorded. The delivery tool rebuilds a fresh commit against current `origin/newtargets-dag` while preserving maintainer-owned fields; its temporary worktree is the required rebase mechanism. No direct git command is run by this worker.

The previous report contained several old dry-run hashes and a statement that delivery would follow. They are superseded by this worker report; they are not evidence that this repaired sandbox has passed. Only the new dry run below validates this handover. Stage 1 forbids compilation, so the repair's generic request to compile is inapplicable: no Lean, compiler, Lake or build command is run.

## Mathematical corrections and scope

No STATEMENT-DISPUTED was found. The original source has a reduced one-dimensional Noetherian local ring, its minimal primes, the product of quotient fraction fields, the product of their integral closures, and the coordinate quotient/inclusion map. The sandbox expands that same definition; commutativity is the ambient algebraic convention, not an additional geometric restriction. It does not assert finite normalization, locality of the product, a decomposition into DVRs, or an identification with a separately defined total quotient ring.

The source's two scheme-normalization references alone do not spell out the ring-level notions. The split therefore also cites the five existing ingredient nodes. This is an auxiliary definition of `sk-prop-a1-kummer`, not its key statement. I read the chapter record, the unit's statement and all five unit steps; no unit realization, statement or route is changed. Imported-node `blueprint.is` remains the item id and `blueprint.from` remains null. No other blueprint definition states the same complete construction, so `same_as=[]`.

## Mathlib and duplicate searches

All inherited `mathlib_searches` entries have matching tool/query records in `searches.jsonl`; no unperformed search is added. This repair used only the prescribed `/home/ubuntu/weil-launcher-nt/msearch.py NF def-exc-local-curve-branches` wrapper for Mathlib searches:

- LeanFinder: `Define the branch algebra of a reduced one dimensional Noetherian local ring as the product of integral closures of minimal prime quotients in their fraction fields`.
- A second LeanFinder phrasing: `Define normalization of a reduced ring as a product indexed by minimal prime ideals, with factors the integral closure in the fraction field of the prime quotient`.
- Loogle: `integralClosure, FractionRing`.
- Grep in `RingTheory`: `integralClosure.*minimalPrimes|minimalPrimes.*integralClosure|branch.?Algebra|normalization.?Algebra`.
- LeanSearch: `Product of integral closures of a reduced ring modulo its minimal prime ideals in fraction fields`.

The first semantic query returned eight hits: dimension-at-most-one preservation under integral closure, Dedekind localizations, quotient algebra structures and a ramification theorem. I read `Mathlib/RingTheory/DedekindDomain/Basic.lean:56–84`; `Ring.DimensionLEOne.integralClosure` is a property of one integral closure, not this definition. The second phrasing returned normalized-factor theorems and scheme-normalization reducedness. Loogle's single hit `integralClosure.isDedekindDomain_fractionRing` requires a Dedekind domain and a finite separable extension; I read its actual context at `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:230–248`. It gives neither product nor the coordinate map. The focused grep returned zero hits. LeanSearch returned Internal Server Error and remains `unavailable`, rather than an absence verdict.

I also read the existing ingredient declarations directly: `Ideal.finite_minimalPrimes_of_isNoetherianRing` at `Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean:26`, `integralClosure` at `Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:216`, and `FractionRing` and its domain field instance at `Mathlib/RingTheory/Localization/FractionRing.lean:716,737`. These confirm reusable factors, not a whole-item leaf.

Whole-DAG searches for branch algebra, normalization algebra, minimal primes and Tags 00GP/00FR, and whole-blueprint searches `tools/blueprint_refs.py search 'branch algebra'`, `search 'integral closure'` and the ancestor lookup, found the item, its two explanatory definitions and the punctured-branches theorem. The latter assumes excellent strictly henselian local data and proves a decomposition; it is not a duplicate definition. No new node is introduced.

## Not duplicates

No new nodes; all ingredient nodes already exist and are cited directly.

## Unfinished work

No mathematical stage-1 repair remains. This worker leaves the accepted sandbox for a fresh second reader and does not push. No agents were started and no shared-project, live-project, source-checkout or launcher file was written.

## Review by NF

I read the actual master source named above and compared every clause, rather than relying on the earlier report. Its hypotheses and its defining displays agree with the sandbox: the factors are indexed by all distinct minimal primes, Q(R) uses their fraction fields, B(R) uses integral closure in those same fields, and r maps to the image of its residue class in each factor. The added prime-ideal explanation makes explicit that each quotient is a nonzero domain. I read both normalization blueprint sources: their affine rings use the same integral-closure notion, and neither definition includes finiteness. No new node requires a separate source review.

There are no proof steps, so the C1/C4 audit concerns the seven statement dependencies. I opened every current node, whose statements are recorded in `dependency-snapshot.json`, and checked their exact uses:

- `def-weil-pbc-noetherian-ring` says every ideal is finitely generated. This agrees with Stacks 00FM (`section-Noetherian`, algebra.tex:5980–5985), which I read. No finite-type or excellent hypothesis is inserted.
- `def-weil-pbc-krull-dimension-ring` defines dimension by lengths of strict prime chains. I read Stacks 00KE (`definition-Krull`, algebra.tex:14326–14344); it imposes no normality or regularity condition.
- `lem-sc-finite-minimal-primes-over-ideal` explicitly states finiteness of primes minimal above any ideal of a Noetherian commutative ring. Take I=0; its only ring hypothesis is already present. Stacks 00FR (`lemma-Noetherian-irreducible-components`, algebra.tex:6134–6150) gives the zero-ideal case directly. I checked the exact existing Mathlib declaration at the line given above. This node is not used to claim B(R) finite over R.
- `def-weil-pbc-module-localization` gives fractions, their equivalence relation, addition, scalar multiplication and the map m to m/1. I read Stacks 00CM (`section-localization`), 00CN (`definition-multiplicative-subset`) and 07JZ (`definition-localization-module`), algebra.tex:1035–1080,1138–1168. Specialize M=A_a and denominators to its nonzero elements. Primality gives a nonzero domain, so 1 is allowed and denominators are multiplicatively closed. The scalar product specializes to fraction multiplication. The domain cancellation law makes nonzero x/s invertible by s/x, proving these are precisely fraction fields without another theorem dependency.
- `def-weil-pbc-integral-closure` explicitly supplies the subring of integral elements containing the base-ring image. I read Stacks 00GI (`definition-integral-ring-map`), 00GO (`lemma-integral-closure-is-ring`) and 00GP (`definition-integral-closure`), algebra.tex:7441–7453,7541–7554,7568–7576, and checked these tag/label pairs in tags/tags. Apply with A_a mapping to K_a. This gives exactly each factor and its structural map.
- `def-sc-normalization` defines normalization in the function field as a relative spectrum of the integral-closure sheaf. Its current statement and actual blueprint source agree. Its source-linked scheme declaration is explanatory here; no gluing or finite-normalization theorem is borrowed from a definition.
- `def-fin-normalization-extension` similarly defines normalization in an extension field and gives the affine integral closure. I compared its current statement with its actual blueprint file and the scheme declaration cited above. It is not used to assert that arbitrary branch normalization is finite or that the displayed product is local.

The map's well-definedness is elementary from those exact statements. For a in A_a, its image in K_a satisfies the monic polynomial T-a and belongs to the specified integral closure. Thus r maps to ((r mod p_a)/1)_a. Each coordinate preserves zero, one, sums and products by the quotient and fraction formulas and the same subring operations. Coordinatewise preservation gives the ring homomorphism to the product and hence the R-algebra structure. No product-integral-closure theorem is needed: the product is the definition, not a comparison conclusion.

For small cases I checked R=k[t]_(t), giving the single field k(t) and B(R)=R; the nodal ring (k[x,y]/(xy))_(x,y), giving two fraction fields and B(R)=k[x]_(x) times k[y]_(y); and the cusp k[t²,t³]_(t²,t³), giving B(R)=k[t]_(t). These distinguish one branch, several branches and a nonnormal branch and confirm that locality and normality of R have not been silently conflated. Fields and the zero ring fail dimension one. The source assumes no excellence, and none is used to define these objects. These examples are sanity checks, not new theorem assertions or cited proof steps.

Against B1–B10, all objects are introduced, notions are cited or expanded inline, TeX is preserved, no child contains a proof sketch, and no new leaf or duplicate is claimed. Against C1–C8, no definition is cited for an absent theorem, no proof of a cited node is used as its interface, and no unit-route step is replaced. Against D1–D5, this is a definition split with actual ingredient notions, not a parent theorem moved to a child. Against E1–E7, I checked the domain, multiplicative-subset and integral-closure hypotheses and the explicit coordinate map as above; no mathematical source error was found. The repair improves source verification and definition precision instead of claiming that a rebase alone repairs mathematics.

## Validation

The installed deliver.py parser accepts group, item and `--no-push`; the brief's trailing dot is rejected with usage. The supported required invocation is `python3 /home/ubuntu/weil-launcher-nt/deliver.py NF def-exc-local-curve-branches --no-push`. It builds a fresh temporary worktree commit on current origin/newtargets-dag and runs the maintainer's stage-1 preflight. Its new result is captured in `repair-dry-run.log`. No push will be performed by this worker.


## Second reading by NF

I independently opened the sandbox node, the current shared-DAG item and all seven dependency statements, the complete archived master blueprint definition, both normalization blueprint definitions, the unit and chapter sources, and the Stacks passages below. This is a definition: there is no theorem proof to move into a child. No mathematical statement correction or STATEMENT-DISPUTED is needed.

- Item `def-exc-local-curve-branches`: PASS against the complete master blueprint display and following structural-map paragraph (order 1917). Reduced, dimension exactly one, Noetherian and local are preserved. The explicit commutative convention, definitions of reduced/local/prime, enumeration of all distinct minimal primes, both products, integral-closure factors and coordinate map do not add a hypothesis or change the object. Finiteness of normalization and decomposition into local rings remain unasserted.
- Proof steps: none (`proof=[]`), as appropriate for a definition. The only well-definedness facts are available from the cited definitions and the finite-minimal-prime statement; `citations.json=[]` is correct because there are no step citations.
- Dependency `def-weil-pbc-noetherian-ring`: PASS against Stacks 00FM, `section-Noetherian`, algebra.tex:5981–5985. Its exact statement is every ideal finitely generated, the hypothesis used here.
- Dependency `def-weil-pbc-krull-dimension-ring`: PASS against Stacks 00KE, `definition-Krull`, algebra.tex:14327–14344. Dimension one means prime chains of supremum length one; neither dimension at most one nor a regularity assumption is substituted.
- Dependency `lem-sc-finite-minimal-primes-over-ideal`: PASS against its exact current statement and Stacks 00FR, `lemma-Noetherian-irreducible-components`, algebra.tex:6135–6150. Setting I=0 gives the required finite set; Noetherianity is already present. I also read `Ideal.finite_minimalPrimes_of_isNoetherianRing`, Mathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean:26–43.
- Dependency `def-weil-pbc-module-localization`: PASS against its fraction equivalence and scalar-operation statements and Stacks 00CM/00CN/07JZ, `section-localization`, `definition-multiplicative-subset`, `definition-localization-module`, algebra.tex:1039–1080,1138–1168. For a proper prime p, 1 is nonzero in A=R/p, and xy=0 forces x=0 or y=0. Thus the nonzero denominators form a multiplicative set. The given equality criterion makes A to S^-1 A injective; a nonzero x/s has x nonzero and inverse s/x by the given operations. This establishes the stated fraction-field interpretation in elementary lines from that interface. I read Mathlib/RingTheory/Localization/FractionRing.lean:708–744: the localization uses nonzerodivisors, which in this domain are precisely the nonzero elements.
- Dependency `def-weil-pbc-integral-closure`: PASS against the full current statement and Stacks 00GI/00GO/00GP, `definition-integral-ring-map`, `lemma-integral-closure-is-ring`, `definition-integral-closure`, algebra.tex:7442–7453,7542–7552,7569–7576. Apply it to A_a to K_a; it supplies exactly the subring and inclusion of the base-ring image. I read the `integralClosure` carrier and algebra-map field at Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:216–224.
- Dependency `def-sc-normalization`: PASS against its archived blueprint (order 914), current statement and source abbreviation at WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean:179–190. It is an explanatory normalization reference, with no finiteness theorem borrowed.
- Dependency `def-fin-normalization-extension`: PASS against its archived blueprint (order 1014), current statement and source abbreviation at WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean:296–309. On each domain factor the extension is K_a/K_a, of degree one; no extra finite-extension hypothesis is needed. The affine integral closure agrees, and no gluing result is used in this ring definition.
- Coordinate structural map: PASS. The image of a in A_a in K_a satisfies T-a, so lies in its integral closure. Each coordinate is the quotient ring map followed by a/1 into that subring; quotient, fraction and subring operations preserve zero, one, addition and multiplication. The product operation is coordinatewise, hence gives the claimed ring map and R-algebra structure. Nothing here uses an absent injectivity or finite-module theorem for R to B(R).
- New nodes: none; B1–B7 and the per-new-node elementary/duplicate/restatement/Mathlib checks have no new object to reject. Whole-DAG tag/key-word searches and independent `blueprint_refs.py` searches for branch algebra and integral closure found no duplicate of the full definition. `lem-exc-punctured-curve-branches` is a decomposition theorem requiring excellence and strict henselianity. `lem-weil-pbc-reduced-noetherian-total-ring-fractions` identifies a localization with a product of fields and does not define B(R); it is not a dependency needed to make the present product definition.
- Edge cases: PASS for the domain R=k[t]_(t) (one factor), the reduced node (k[x,y]/(xy))_(x,y) (two factors), and the cusp k[t^2,t^3]_(t^2,t^3) (a nonnormal domain). A field has dimension zero and the zero ring dimension minus infinity, so neither is an allowed R. An empty minimal-prime list cannot occur: dimension one supplies p_0 strictly contained in p_1, and a prime strictly below p_0 would give a forbidden chain of length two. Hence p_0 is minimal; the finite-minimal-prime lemma supplies the finite enumeration. No scheme or n-parameter occurs in the item. These checks do not assert normalization finiteness for arbitrary R.
- Attachment audit: PASS. My own read-only searches by item id and branchAlgebra/normalizationAlgebra/localCurveBranches in both source trees and the upstream-name index found no whole-item declaration. The two scheme normalizations above are different objects. No upstream-master sorry statement is treated as a proof.

Changes made in this second reading:

- Corrected the inherited verdict for `IsFractionRing integralClosure minimalPrimes`: a type-rejected Loogle query is inconclusive, not evidence of absence. The original raw search record remains intact.
- Ran independent wrapper searches using total-fraction-ring/direct-product terminology, the accepted Loogle pattern `"integralClosure", "minimal"`, and a new normalization/product grep. Recorded their actual results in the item's `mathlib_searches`; the wrapper appended the raw records to `searches.jsonl`. The semantic hits concern normalized prime factors, scheme reducedness or localizations; Loogle returned zero hits; grep returned three normalized-factor product theorems and the fraction-ring docstring already read. None defines this branch algebra. No new nodes or Mathlib leaves were added.
- Added this source-by-source second reading. The mathematical statement, dependency list, empty proof, empty citations and the first worker's `## Review by NF` remain as read.

The earlier worker's no-push handover is superseded by this second reader's authorized dry run and delivery. The installed `deliver.py` accepts two positional arguments; its parser rejects a trailing dot, so I use the documented invocation without that unsupported argument. No Lean, compiler, Lake or build command is run and no agent is started.

Second-reader validation: `deliver.py NF def-exc-local-curve-branches --no-push` printed `OK (not pushed) deliver/NF/def-exc-local-curve-branches at 55261a0ff6: preflight passed`. No failure required a mathematical repair. This replaces the older worker validation for the current handover.
