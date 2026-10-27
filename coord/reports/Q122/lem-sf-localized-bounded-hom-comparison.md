# Q122: lem-sf-localized-bounded-hom-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-sf-localized-bounded-hom-comparison.json`: statement, split; no Mathlib match found for the entire localized ordinary sheaf-Hom comparison criterion and its naturality/sign clauses.
- `citations.json`: one exact statement quotation per proof-step citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed because this item is a tool extracted from the unit's proposition, not its key statement.

## Attachments

None. Searching the exact blueprint tag in `lean/WeilConjectures/` returned none. Searches for localized Hom, bounded Hom and stupid Hom led to `StupidTailHomShortExact.lean`, `BoundedExactTermHomQuasiIso.lean`, `HomComplexShiftLeft.lean`, and the localized external-cochain files. Their declarations give smaller interfaces already in the DAG, or require that f be a quasi-isomorphism and each source term have an exact Hom functor. They do not give this item's hypothesis of arbitrary f and termwise scalar-localized invertibility together with every stated naturality and sign clause. I did not attach a partial result or a declaration with sorry.

## WANTED

None.

## What needed correction

There was no existing sandbox node, proof or report to recover. I read and retained the existing sandbox search log (including the second LeanFinder phrasing) and copied the current live item. The item statement is unchanged. Its source, inherited metadata, blueprint reference and prior searches are retained. I removed `def-pur-derived-internal-hom` from statement dependencies: the object here is the ordinary product Hom complex on fixed representatives, viewed in D(R); no derived internal Hom occurs. The proof does not treat ordinary Hom as a functor on arbitrary derived objects.

Stacks 08JC states triangulatedness of RHom, with a proof using termwise split ordinary Hom sequences and omitting details. Applying its RHom conclusion directly to ordinary Hom on arbitrary representatives would be unjustified. The split instead cites the existing ordinary-Hom tail lemma and writes the degreewise inclusion/projection description, followed by the canonical natural short-exact-sequence triangle theorem. Thus it supplies the needed argument without changing the statement or requiring projectivity of the terms.

## Searches and existing interfaces

The Q122 `searches.jsonl` was read before continuing, and no service search was repeated. It records a plain-language internal sheaf Hom criterion, a second finite-filtration phrasing, a Loogle query for HomComplex and iso, and a grep for stupid truncations/internalHom shifts. The additional logged grep `homComplex.*shift|shift.*homComplex|stupidTrunc` inspected truncation files and HomComplexShift imports. All actual Q122 tool/query pairs have been appended to the item's `mathlib_searches`, with their returned candidate names/files. Prior Q110 searches, including its unavailable LeanSearch entry, remain unchanged.

Read candidates include Mathlib's sheafHom (ordinary sheaves of types), HomComplex cochains and their shift formulas (external cochains), derived fractions (`left_fac_of_isStrictlyGE`, `right_fac_of_isStrictlyLE`), the t-structure single-object realization theorem and good/stupid truncation infrastructure. None states this item's map-specific assertion for ordinary internal sheaf Hom under scalar localization. In particular, external shifted cochains are not a one-line specialization to a sheaf-valued total Hom complex. No Mathlib leaf is claimed.

Whole-DAG statement searches for termwise/degreewise split Hom sequences, Hom shifts and scalar-localization triangles found all five needed interfaces. Whole-blueprint searches with `tools/blueprint_refs.py` for `Hom shift`, `bounded Hom`, `08JC`, `source-shift`, `localized bounded` and `stupid tail` gave no node stating this item. The `Hom shift` hit was a Weil internal-Hom statement, not this assertion. The ancestor tool confirmed `prop-sf-dualizable`. I read its main-20261015 proof, the current node and its extraction description, and the unit and chapter records. This remains precisely the finite stupid-tail argument in the local perfect-complex route.

## Not duplicates

No new nodes are created. Existing nodes are cited directly: `lem-pc-stupid-tail-hom-short-exact`, `lem-weil-pbc-complex-ses-triangle`, `lem-weil-linear-scalar-localization-triangulated`, `lem-pur-hom-complex-shift-left` and `lem-sf-triangle-morphism-iso`. The nearby `lem-pc-bounded-exact-term-hom-quasi-iso` assumes exact term-Hom functors and a quasi-isomorphism; it is not a duplicate of this map-specific localized criterion.

## Review by Q122

I read Stacks `sites-cohomology.tex`, Tag 0A8X (`section-hom-complexes`), including its product and differential, and Tag 08JC (`lemma-RHom-triangulated`), including its termwise-split observation. I also read `derived.tex`, Tag 0152 (`lemma-derived-canonical-delta-functor`) with its natural cone construction and sign, Tag 05R6 (`proposition-construct-localization`) and Tag 014A (`lemma-third-isomorphism-triangle`). I checked those labels against the local tag map. The finite localized induction is an agent-written application of these tools, so the proof origin is agent, not falsely attributed to the blueprint as an independent document proof. There are no new node sources to check and no SGA source is used.

Step 1 uses the statement of `def-pc-cochain-complex-modules` for the differential and chain-map equations. The inclusion and quotient are chain maps at the cut, and the degreewise identity sequences explicitly give the splittings. This does not assert a splitting as complexes; that distinction is essential when d_P at r is nonzero.

Step 2 uses the full statement of `lem-pc-stupid-tail-hom-short-exact`: it allows any chain map f and only assumes the chosen source vanishes below k. Applied to T_r with k=r, that hypothesis holds regardless of whether r is in [a,b]. I read the node and its Lean declaration source. The statement gives the three comparison arrows as a morphism of short exact sequences up to arrow isomorphisms. To identify the canonical maps actually required here, the step additionally uses the product and functoriality stated in `def-pur-hom-complex`: isolating the j=r factor gives the inclusion and projection, with no exactness assumption on the sheaf Hom functor. Associativity proves both postcomposition squares, on the actual representatives, and does not rely on a hidden choice from the cited node's proof.

Step 3 uses the abelianness in `def-weil-sheaf-of-modules-category` and precisely the naturality clause of `lem-weil-pbc-complex-ses-triangle`. I checked that this node supplies the connecting morphism for arbitrary degreewise short exact sequences of complexes, not just an existence assertion about some triangle. It explicitly states the equality with u_1[1] and u_3. This gives the displayed connecting square with c_G and c_T, so every square is justified rather than merely called compatible.

Step 4 uses exactly the triangulatedness and exactness asserted by `lem-weil-linear-scalar-localization-triangulated`. The scalar ring in that node is A, its element is t, and its category is D(R). Central multiplication by A on R-module sheaves commutes with all R-linear maps and differentials, hence acts on complexes, homotopies and their derived localization, giving the stated A-linear structure and A-linear shifts. The ring sheaf R is not confused with the scalar ring A. An exact functor preserves the two distinguished triangles and their shift square. No cohomological localization theorem or pointwise criterion is substituted for this statement.

Step 5 uses `lem-pur-hom-complex-shift-left` with m=-r. Its statement gives a natural isomorphism without projectivity or boundedness requirements. The statement does not specify a component sign, so I did not claim it does: I wrote and checked that normalization directly from the differential in `def-pur-hom-complex`. In degree q both complexes have Hom(P^r,V^{r+q}), while the shifted differential is (-1)^r d_V. The identity (-1)^{r(q+1)}(-1)^r=(-1)^{rq} proves the chain equation. Squaring the sign proves invertibility, and linear postcomposition proves the square for f. This covers negative r and q as well. The shift-commutation clause of `def-weil-linear-scalar-localization` then identifies the localized comparison with the shift of the assumed one.

Step 6 uses exactly the two-isomorphisms conclusion of `lem-sf-triangle-morphism-iso`, applied in the triangulated category from step 4. The induction claim is explicit, its base is r=b+1, and at each step the first and third components are known invertible before deducing the middle. `def-pur-hom-complex` makes Hom(0,V) the zero complex, so the base and the empty-support case have identity comparisons. The use of the support bound at T_a=P is valid; when a>b the zero-source argument is made separately rather than using an invalid induction interval.

I tested the proof on P=0, an empty interval, a single nonzero source degree, a two-term complex with a nonzero differential, negative and odd shifts, t invertible, t=0 or nilpotent, zero coefficients and arbitrary unbounded M,N. A single term reduces to the signed square; the two-term case retains a genuinely nonzero connecting morphism and is handled by the natural SES triangle, not by a false direct-sum splitting of complexes. At t=0 or nilpotent, localized Hom modules are zero and identities equal zero; the exact-localization and two-isomorphisms statements still apply. No quasi-isomorphism, injectivity, flatness or projectivity hypothesis is smuggled into the argument.

Against B–E: no new statement-only node is needed; no elementary consequence or clause of the item was made a node. I opened each cited statement, and `citations.json` contains exact verbatim statements for every use. The substantive steps cite theorem interfaces rather than only definitions. All six steps are under 2000 characters, so none hides a long secondary comparison. The generic off-unit tools are declared in `split_report.tool_uses`; they support the same finite-tail route and replace no unit step. The server dry run will check acyclicity and the remaining mechanical requirements. No Lean file, compiler, Lake command, repository write or direct git command was used.

## Unfinished work

None in the proposed one-level split. The existing theorem nodes retain their own states; this delivery does not claim to finish their proofs or implement Lean.
