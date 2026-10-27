# Worker report: lem-sfb-stack-fibre-regular-slice-flat

## Files written

All five node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-stack-fibre-regular-slice-flat.json`: item, split into six proof steps; statement unchanged; no exact finished project declaration found.
- `lem-sfb-space-fibre-regular-slice-flat.json`: new statement-only input, Stacks 06LW; no Mathlib match.
- `lem-sfb-space-strict-local-flatness.json`: new statement-only input, Stacks 04KF/04NG, with the etale-local-ring convention 04KG and locality 04KH/04KJ; no Mathlib match.
- `lem-sfb-smooth-cover-flat-lfp-descent.json`: new statement-only input, Stacks 06M2 specialized using 06ET and 06EV; no Mathlib match.
- `lem-sfb-regular-sequence-faithfully-flat-ascent.json`: new Mathlib leaf, `RingTheory.Sequence.IsRegular.of_faithfullyFlat`, Mathlib/RingTheory/Regular/Flat.lean:92-94; the faithfully-flat variable is at line 81.

Also wrote `citations.json` (one verbatim statement quotation for every step/node citation), this report, and sandbox-only preparation and search records. The scripts are not project files. `search-results.json` preserves the actual command outputs and `searches.jsonl` is the search command's unmodified log.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag, regular/slice/flat terminology and the candidate new notions. The related depth-two and closed-fibre power-series files concern Noetherian schemes/rings, not this arbitrary algebraic-stack assertion. Sorry declarations were not counted as finished proofs. Mathlib is used as a leaf, not an attachment.

## WANTED

None. All mathematical sources used here were available in the read-only Stacks checkout.

## Corrections and scope

The imported item is true with its stated etale-chart hypothesis; I retained every hypothesis and conclusion. Its source formulates regularity in the strict local ring. Step 1 explicitly supplies the needed faithfully-flat ascent from the given ordinary local ring, rather than treating the two formulations as identical. No hypothesis of Noetherianity, smoothness of q, surjectivity of q, or quasi-compactness of any cover has been inserted.

The existing unit and chapter bindings are inherited. I read `dag/units/sk-thm-sf-ctf-stability.json` and `dag/chapters/sec-six-functors-basics.json`. This is a supporting prerequisite down the existing stable-curve/Deligne--Mumford-atlas branch, not the key statement of that unit; no unit realization fields were changed. The existing nearest blueprint ancestor is null and the exact inherited place and via chain are preserved. `tools/blueprint_refs.py ancestor` confirmed that null ancestor. The new nodes point through this item and continue that chain.

The item had no proof at all. Its new proof follows the actual atlas argument of 06MD; it does not use 06MD itself as an opaque new node. In particular it explains the two fibre products, the field extension, the open image and the surjective cover of the zero scheme. No source error or statement dispute was found. The three geometric new nodes remain statement-only and are not recursively split.

## Not duplicates

lem-sfb-regular-sequence-faithfully-flat-ascent vs lem-per-regular-lci-geometric-calculus: the latter concerns regular immersions, dimensions, and smooth morphisms of Noetherian schemes; it does not state preservation of an arbitrary specified ring regular sequence under an arbitrary faithfully flat ring extension. Their shared 00LM citation does not identify their statements.

lem-sfb-regular-sequence-faithfully-flat-ascent vs lem-weil-pbc-weakly-regular-sequence-localization-prime: the latter localizes a weakly regular sequence at a prime containing its elements; it does not allow a general faithfully flat algebra, and its localization map need not be faithfully flat on the original ring. The new node is the exact Mathlib faithfully-flat lemma.

The tag search found no other existing nodes sharing the source tags of the new geometric inputs (04KF, 04KG, 04KH, 04KJ, 04NG, 06LW, 06M2, 06ET, 06EV). Whole-DAG keyword and declaration searches and whole-blueprint searches for slice, regular sequence, strict local, etale local, smooth surjective, faithfully flat, and the relevant tags found no existing statement that supplies these inputs.

Additional nearby candidates were read: `lem-pur-fiber-regular-sequence-neighbourhood` only spreads regularity of equations in a ring and does not assert flatness of their quotient; `lem-pur-flat-quotient-fiber-regular-sequence` already assumes quotient flatness; `lem-weil-pbc-grothendieck-regular-sequence-flat` assumes Noetherian local rings. None proves 06LW for arbitrary algebraic-space bases. The stack source-descent input is separate from `lem-sbc-smooth-flat-surjective-source-descent`, which proves descent of smoothness for schemes, and `lem-trf-etale-descent-through-source-cover`, which proves descent of etaleness for schemes. Existing `lem-sfb-stack-chartwise-smooth-etale-calculus` supplies stability, composition and open-source locality, but not smooth-surjective source descent. Existing `lem-sfb-space-flat-proper-fp-locality` is target-fppf descent and discusses finite presentation rather than this source-local finite-presentation assertion. I reused `lem-sfb-flat-lfp-space-universally-open` instead of creating another openness lemma.

The new algebraic-space slicing input is strictly below the item: its target is an algebraic space and its regularity is already strict-local. The item carries the additional stack-to-space atlas reduction, chart-to-strict-local comparison, field-extension regularity argument, open-image construction and smooth-cover descent. Thus it is neither an identical statement nor a new node containing all of the item's proof.

## Review by NR

I read Stacks `stacks-morphisms.tex`, Tag 06MD (`lemma-slice`), statement and complete proof, and compared it to the item. The source allows an algebraic-space source, whereas this item only asks for a scheme source, so the specialization is valid. Its single point of fibre regularity is preserved: no neighbourhood regularity is assumed at the outset. I followed its smooth-atlas route throughout.

For the new algebraic-space input I read `spaces-more-morphisms.tex`, Tag 06LW (`lemma-slice`), including the reduction to etale scheme charts and the call to 06LI. Its arbitrary-base, flat and locally finitely presented hypotheses are exactly those stated in the new node. It gives an open of the ambient space containing the projected point, not merely an open of the zero locus. That distinction is needed in step 5. This fact is not already the stack conclusion: it is applied only after passing to the atlas.

For the new strict-local input I read `spaces-properties.tex`, Tags 04KF (`lemma-describe-etale-local-ring`), 04KG (`definition-etale-local-rings`) 04KH (`lemma-etale-site-locally-ringed`), and 04KJ (`lemma-morphism-locally-ringed`), and `spaces-morphisms.tex`, Tag 04NG (`lemma-flat-at-point-etale-local-rings`), statement and proof. The node states both the ordinary-chart strict-henselization identification and precisely the flatness comparison used in the proof; it does not equate an ordinary local ring with its strict henselization. Geometric points and local homomorphisms are explained in its own statement; the existing triples node provides the strict-henselization construction.

For smooth-source descent I read `stacks-properties.tex`, Tag 06M2 (`lemma-check-property-after-precomposing`), including its scheme-base-change proof, and `spaces-descent.tex`, Tags 06ET (`lemma-flat-fpqc-local-source`) and 06EV (`lemma-locally-finite-presentation-fppf-local-source`). Smooth coverings are among the allowed coverings. The two properties descend separately; finite presentation or quasi-compactness is not asserted. I also read the actual Mathlib declaration at Flat.lean:92-94 and its variables at line 81, not just its search hit: it takes an arbitrary finite list, assumes Module.FaithfullyFlat, and concludes regularity of exactly the mapped list, including the nonzero final quotient. This is an exact leaf, with no local-ring or Noetherian bridge required. Stacks algebra.tex 00LM explains the same preservation in the flat-local situation of the application.

Step 1 uses the chart identification in the new strict-local node, the actual faithful-flatness statement of `lem-sc-strict-henselization-faithfully-flat`, and the Mathlib regular-sequence ascent leaf. I read the former node and `more-algebra.tex` 07QM(1): the source local ring is arbitrary, so the item's lack of Noetherianity causes no problem. The three statements together say precisely what the step uses.

Step 2 takes only base-change stability and smooth/flat/local-finite-presentation permanence from `lem-sfb-stack-chartwise-smooth-etale-calculus`; I read its entire statement. The smooth surjective atlas is part of the item's explicit algebraic-stack hypothesis. Surjectivity lifts a field point after a field extension. The cited moduli-groupoid definition is used for its explicit 2-fibre-product object formula, which makes the identification of F' with F times_k k' a direct construction on objects and arrows. It is not cited as a theorem providing a new atlas. The fibre products are algebraic spaces by applying representability of the diagonal to the product of the two scheme sources.

Step 3 uses `lem-weil-pbc-field-extension-base-change-faithfully-flat` only for the ring map D to D tensor_k k', and `lem-weil-pbc-faithfully-flat-surjective-spectrum` only for its surjectivity on points. Their statements were opened and agree with those uses. This verifies flatness and surjectivity on etale affine charts of F, whose existence and structure sheaf are in `def-trf-algebraic-space`; it does not assume F is a scheme. The new strict-local node then supplies a flat local map for compatible geometric points. The statement of `lem-weil-pbc-flat-local-hom-faithfully-flat` applies to these two local rings without any Noetherian hypothesis, and the Mathlib leaf supplies regularity. I expanded the change of algebraically closed field: the separable algebraic closure of the residue field inside it is unchanged under an algebraically closed overfield, so the pointed-etale-neighbourhood colimit in `lem-weil-pbc-strict-henselization-triples` is unchanged. The step cites that construction explicitly. This repairs a possible hidden identification rather than asserting that geometric stalks at unrelated points coincide.

Step 4 applies the new 06LW node only to T to W. Its base and source are algebraic spaces, its fibre is the displayed F', its point is z', and its specified equations are the pullbacks of the original ones. Every hypothesis has been established in steps 2 and 3. The cited statement gives both flatness and local finite presentation of H to W on one ambient open T'.

Step 5 uses the smooth-implies-flat-and-lfp clause and the base-change clauses in the existing stack calculus, and the precise openness assertion of `lem-sfb-flat-lfp-space-universally-open`. I read both statements. Openness produces an open subset U_1 of the scheme U containing u. The map T' to U_1 is surjective by its definition as the image. The equality H=T' times_{U_1} Z follows because both closed subspaces are cut out by the same pulled-back ideal generators; this is the direct affine quotient calculation, not an assumption that a set-theoretic image inclusion factors through a closed subscheme. Smoothness and surjectivity of H to Z are then actual base changes of T' to U_1.

Step 6 uses the existing calculus for composition of flat and locally finitely presented maps, and the new source-descent statement for the smooth surjection H to Z. These maps are representable by algebraic spaces. Its two conclusions are exactly the two clauses of the item. There is no attempt to descend from a mere subset covering or to assert global flatness away from the constructed open.

I checked the B--E failure modes with the sources and nodes open. The new unsplit inputs contain statements and no proofs, introduce their own objects, and use existing definition nodes or inline conventions; TeX is single-escaped in the JSON and every nontrivial literature place includes its tag and label. Searches were run through msearch and copied from its actual output; LeanSearch was rate-limited on the item query and is recorded as unavailable, not as an empty match. Two distinct natural-language searches were run per candidate and the exact Mathlib leaf was verified in source. No duplicate or one-clause replacement was added. The six steps have no hidden induction, omitted standard lemma, reliance on a cited node's proof rather than its statement, or unsupported non-elementary geometric assertion. The longest step is below 2000 characters. The new inputs are strictly below the item and do not cite it. The supplied citations file contains verbatim node text for every step citation. Off-unit generic strict-henselization and ring-flatness tools are declared in split_report.tool_uses, without changing the maintainer-owned tool_uses field.

Small cases checked: r=0 gives Z=U_1 and is consistent with the proof and all input statements; a nonempty regular list lies in the maximal ideal since its quotient is nonzero; the zero ring has no regular empty list under this convention and never occurs as a point's local ring. A faithfully flat extension of a nonzero ring remains nonzero, so the Mathlib leaf covers the empty list as well. If U or the fibre were empty the hypothesis specifying v could not hold. The argument uses no perfectness or algebraic-closure assumption on k, no separability of k'/k, no Noetherianity of S, and no quasi-compactness of the smooth atlas. These are precisely the cases where substituting the nearby Noetherian scheme lemmas would fail. No forbidden SGA source is used.

## Unfinished work and validation

The item has a complete stage-1 proof. The three new geometric statements are deliberately unsplit children, not unfinished parts of this one-level split. No Lean files, compilers, Lake, repository writes, or direct repository git commands were used.

The required server `review_split` check passed. Full delivery dry-run results and push results are recorded by the delivery command and will be appended here once available.

The initial full dry run returned two packaging issues: the Mathlib match needed its explicit integer `line` field (now 92), and the descent node needed individually bracketed notion references for the citation parser. Both are repaired. During the final source audit I also added the precise locality citation 04KJ to the strict-local input; its statement and Mathlib searches are unchanged. The server check_dag check passed with no introduced finding.


## Repair of the returned delivery (2026-10-22)

The return at `coord/returns/NR.md:121` names returned head
`61d26d6616f7a5af2d265fc95f160f18bfe8001f`: its mathematical review passed,
but the side completion had not been promoted into the DAG used by the queue.
I first ran the required dry run on the retained sandbox. It exited successfully:
`OK (not pushed)` at `aad245eda1c`. This established that the current delivery
path accepts the overlay; it did not establish that the old delivery had landed.

I compared the returned commit, the retained sandbox, and current origin main
`112a35c543056f8acbaaed81db1a1daa5d4cba83`, using a read-only object reader
stored in this sandbox and no Git command. All five retained node files were
identical to the returned head before this repair. On current main the item is
`unsplit`, with its original statement and statement dependencies unchanged;
the four child nodes are absent. All 17 external nodes used in the item's
statement or proof are byte-equivalent as JSON objects between the returned
head and current main. Thus there is no changed external statement requiring a
replacement citation, and no live child completion to overwrite. The delivery
command rebuilds its single commit on freshly fetched current main and preserves
maintainer-owned metadata. Promotion itself remains L's operation.

Under my NR review signature I re-read every external cited statement, including
the strict-henselization triples construction, faithfully-flat strict
henselization, field-extension base change, spectrum surjectivity, flat local
maps, chartwise stack calculus, algebraic-space definition, moduli-groupoid
2-product formula, and universally open flat-lfp morphisms. Each still supplies
exactly its use in the six steps described above. I re-read the complete 06MD
proof, the 06LW statement and chart reduction, 04KF and 04NG, and smooth-source
descent 06M2 with 06ET/06EV. The same non-Noetherian hypotheses and the empty-list
case remain valid. Existing citations.json quotations still match every current
statement; no replacement searches are needed because no statement or search
question changed. I read the retained search outputs again: the geometric hits
concern schemes, while the faithfully-flat regular-sequence declaration is the
exact leaf at Mathlib/RingTheory/Regular/Flat.lean:92.

This is not an unchanged re-push: in step 2 I now give the forward and inverse
operations on objects for the 2-fibre-product comparison, obtained by composing
with the selected 2-isomorphism and its inverse. In step 5 I replace a literal
equality of closed subspaces by its canonical identification and write the
base-change formula B tensor_A A/I = B/IB, including compatibility with chart
restrictions. These are elementary elaborations of the existing argument, with
no new lemma, changed route, new hypothesis, or changed target statement. The
split_report records the return, comparison base and concrete proof adjustments.
All child statements, sources, blueprint links and actual Mathlib search logs
are retained. Each proof step remains below 2000 characters. The final dry run
and push below must validate this repaired version, rather than the preliminary
unchanged audit version.


## Latest return repair and review by NR

The latest return is the 2026-10-22 11:42 UTC entry for head
`422175aca6b8f7d552ee3f6c74bf723e9a43f6ac`, rather than the earlier
`61d26d6616f` entry described above. I compared that latest returned head with
current origin main `a6b3221a848a711584d34e5b199ba7a5c9f0d699` using the retained
read-only object reader. All 17 external cited nodes are unchanged as JSON
objects; the live item remains unsplit with the same statement and statement
dependencies, and all four children remain absent. The retained sandbox matched
that latest returned head before the edits of this retry. The first required
dry run of this retry passed at `b11d5281940` with `OK (not pushed)`.

I re-read the statements of all cited nodes and the Stacks 06MD proof, the
06LW statement and its chart reduction, 04KF/04KG/04KJ, 04NG, and
06M2/06ET/06EV. No citation needs replacement on the current base. The 17
verbatim entries in citations.json still cover every step/node pair and are
substrings of the current cited statements. I read the retained search results:
none of the scheme or ring flatness hits supplies the geometric stack/space
inputs, while IsRegular.of_faithfullyFlat is exactly the new ring leaf. Thus
no search question changed, and no searches were repeated or invented.

I made two additional proof clarifications relative to the latest returned
head. In step 5 the smoothness of the factor through the open image now follows
from the explicit identification T' times_U U_1 with T', so the precise
base-change clause of the already cited stack calculus applies. In step 6 I
checked the source-descent lemma's two representability hypotheses explicitly:
H to Z is a morphism of algebraic spaces, and Z to the stack is representable
by its diagonal, using the scheme-source fibre-product argument already written
in step 2. These changes preserve the statement, atlas proof route and all
child statements. They close the hypotheses of the cited results without
introducing another lemma or hiding an extra comparison. Every step is still
under 2000 characters. The empty regular list, empty fibre, arbitrary field
extension and absence of Noetherianity or cover quasi-compactness were checked
again and give the same outcomes recorded in the review above.

This retry delivers actual proof edits and an updated current-base comparison;
it is not an unchanged re-push. The delivery tool constructs its commit on the
freshly fetched current DAG. L remains responsible for the promotion which
caused the landing refusal; no maintainer metadata or live repository files
were edited by this worker. A final dry run is required after these edits.


## Latest returned head repaired (2026-10-23)

The return now in coord/returns/NR.md is the 2026-10-22 16:12 UTC entry
for `e91a2ebf74af175dcbaabd12cb58d94668c44b15`. The preceding repair
entries above are history, not this retry's base. I compared that returned
head against current origin main `da64f5d221ce20f720a509463e8173763296e0b9` using the retained read-only
object reader. All 17 external nodes cited by the statement or proof are
unchanged as complete JSON objects. The item's statement and statement
dependencies are unchanged; on current main it is still unsplit and its four
children are absent. The retained sandbox initially matched the latest
returned head exactly. The required initial dry run passed at c9c47e1554b;
the delivery command subsequently confirmed that identical content would not
be pushed, and made no push. All those commands exited before this repair.

I have now made actual changes relative to e91a2ebf74a. Every proof step had
literal doubled TeX backslashes in its parsed text, contrary to B4; I reduced
them to single TeX commands, without changing any statement or search output.
In step 3 I made the geometric-point comparison explicit: the residue field
of a pointed etale neighbourhood is finite separable over the chart's residue
field, so its embeddings into an algebraically closed overfield land in the
same separable closure. The indexing triples and their transition maps are
therefore unchanged, which gives the claimed strict-local-ring identification.
This is the direct use of the cited triples construction, not a new geometric
lemma or a change of the atlas route. Every step remains below 2000 characters.

Under the Review by NR signature above I re-read the latest cited statements
and the complete Stacks 06MD atlas argument, the 06LW slicing statement and
chart reduction, 04KF, 04KJ, 04NG, and 06M2 with 06ET and 06EV. Step 1 still
uses faithful-flat strict henselization and regular-sequence ascent; step 2
uses base-change calculus and the explicit groupoid product; step 3 uses the
field-extension and spectrum statements, the triples construction and flat
local maps; step 4 uses exactly 06LW for T to W; step 5 uses openness and the
quotient base-change calculation; step 6 uses composition and smooth-source
descent with both representability hypotheses. I verified the empty regular
list, nonzero point-local rings, arbitrary field extension, and the absence
of Noetherian or quasi-compactness hypotheses again. None of these checks
changes the target or the three geometric child statements.

I read the retained Mathlib search results and the exact regular-sequence
leaf in Flat.lean:92-94 again. The geometric hits still concern schemes or
rings rather than these algebraic-space and stack assertions. No search
question changed; all actual logs and unavailable-service verdicts are kept.
The verbatim citations are checked against the current statements before
final dry run. The delivery tool constructs the new commit on freshly fetched
current main; promotion into the queue's live DAG remains L's responsibility.


## Repair of the changed calculus citation — Review by NR (2026-10-23)

This section is the current repair; the preceding retry sections are retained
history. The return is the 2026-10-23 05:16 UTC entry for delivery head
`43dc2c2e70f02621953a15906a9d9f7bb0634757`: the independent reader approved
the mathematics, but landing refused the changed statement of
`lem-sfb-stack-chartwise-smooth-etale-calculus`. The required initial dry run
on the retained sandbox exited successfully, `OK (not pushed)` at
`7ac3dab8d2e`, before any edits in this repair. No delivery process was left
running.

I compared that returned head with the current DAG at
`2a9e3ddb1754209c4ea1bfffe785fead79706c66`, using the retained read-only Git
object reader without issuing Git commands. The five sandbox node files
initially matched the returned head exactly. The live item is still unsplit,
with unchanged statement and statement dependencies; all four child nodes
are absent. Of the 17 external statement/proof dependencies, only the calculus
node changed. Its other changed fields are its proof, dependency lists,
review/status and tool-use metadata; this split uses its statement alone.
The other 16 external node records are unchanged as complete JSON objects.

I opened the entire current calculus statement and compared its text to the
returned version. The existing base-change, composition, smooth-implies-flat
and locally-finitely-presented, open-source locality and surjectivity
permanence clauses remain. The added clauses specify surjectivity as lifting
a field-valued object after a field extension, identify that convention with
the representable chart test, specify open covers by their pullbacks to
schemes, and clarify that the diagonal is representable by algebraic spaces.
None adds a hypothesis that fails here. In particular an atlas need not lift
an object over the original field. I read the full Stacks 06MD atlas proof,
including its field extension, 04XC (`lemma-property-spaces-too`), algebraic.tex
045B/045C (composition/base-change for representable properties), and
stacks-properties.tex's surjectivity definition and composition/base-change
lemmas. The revised calculus convention supplies exactly the lifting used
in 06MD, rather than an unjustified same-field lift.

I repaired the split concretely in three places. Step 2 now cites the
calculus's field-extension lifting formulation when choosing k', w and the
2-isomorphism. W to the stack is a smooth surjective atlas, and its diagonal
is representable by algebraic spaces, so the two scheme-source products are
algebraic spaces as required by the unchanged base-change clauses. Step 5
now distinguishes surjectivity onto the open image on points and invokes the
current chart-test/field-extension equivalence. Thus the smooth surjection
H to Z obtained by base change is a surjection in the exact convention of
the descent input. Step 6 explicitly uses that convention when applying
`lem-sfb-smooth-cover-flat-lfp-descent`; both maps are representable by
algebraic spaces, as its statement requires. The step-2 groupoid comparison,
step-5 quotient/base-change calculation, and the proof route are retained.

I re-read the statements used by all six steps. Step 1 uses the strict-local
chart identification, faithfully-flat strict henselization and regular-list
ascent. Step 3 uses only the field-extension faithfully-flat ring map,
surjectivity on spectra, algebraic-space charts, strict-local flatness,
flat-local faithful flatness, ascent and the pointed-etale-triples colimit.
Step 4 applies the algebraic-space slicing statement to T over W after those
hypotheses are established. Step 5 additionally uses the universal openness
of flat locally finitely presented space maps. Step 6 uses composition and
the smooth-source descent statement. The current statements still contain
each of these assertions. I regenerated all 17 step/node quotations in
citations.json directly from their current statements, including the added
calculus clauses; each is now a literal substring with no TeX normalization
needed. No cited proof is used in place of its statement.

For the retained child statements I re-read 06LW and its etale-chart
reduction, 04KF/04KG and 04KJ, 04NG, and 06M2. These respectively give the
space slice on an ambient open, chart strict henselizations and locality,
flatness on strict local rings, and descent through a representable smooth
surjection. The precise Mathlib leaf remains
RingTheory.Sequence.IsRegular.of_faithfullyFlat at Flat.lean:92-94, with
FaithfullyFlat at line 81; I read that declaration and its module variables.
I read the retained search outputs/log: the geometric hits concern schemes
or ordinary stalks, and the ring ascent hit is exact. Statements and search
questions are unchanged, so no searches were repeated or invented, and the
unavailable LeanSearch verdict is retained.

I checked B--E again for this repair: no child proof or new duplicate is
introduced, every non-elementary input is cited, and the item is proved by
the same atlas reduction rather than by a child restating it. In particular
the changed calculus is used only for assertions still explicitly in its
statement. No hypothesis of Noetherianity, quasi-compactness, separability
of k'/k, or surjectivity of q has been introduced. The r=0 case has the whole
source as its zero locus and nonzero point-local rings; an empty fibre
cannot satisfy the specified-point hypothesis. Faithfully-flat ascent
preserves the nonzero quotient required for regularity. All six proof
steps are below 2000 characters (541, 1154, 1687, 440, 1241, 962).

This repair changes the proof, citations and current-base review, not merely
the delivery base. The required delivery tool reconstructs the overlay on
the freshly fetched current DAG and runs server checks. The final dry run
and push follow this report; their authoritative commit and exit results
are the delivery command's outputs. No repository or launcher file, Lean
source, compiler or Lake tool was used for writing or building.


## Current-base revalidation by NR (2026-10-23)

This continuation addresses the same 05:16 UTC return for head
`43dc2c2e70f02621953a15906a9d9f7bb0634757`. The retained repair above was
already present when this session started. As required I ran its dry run
first, waited for it to exit, and obtained `OK (not pushed)` at `237fc808603`.
I then compared the returned head against current origin main
`b6d2df74e8d1dc0ee08d51ef2088ae933b0dce27` using the retained read-only
object reader. The only changed external dependency remains
`lem-sfb-stack-chartwise-smooth-etale-calculus`; its current statement is
exactly the version quoted in the retained repair. All other 16 external
records are unchanged. The four retained children are still absent on main.
No current completion is overwritten.

I re-read the complete current calculus statement, Stacks 06MD's complete
atlas proof, and 04XC and 04XI. In step 2 the atlas lifts the field object
only after k'/k, exactly as the new lifting clause permits; no same-field
lift is assumed. In step 5 smoothness is the explicit open base change
T' times_U U_1 = T', and surjectivity is the image condition. I additionally
wrote the chart argument: a point of U_1 lifts first to T' and then to any
surjective etale scheme chart E of T'. The new calculus identifies this
algebraic-space surjectivity test with its field-extension convention.
In step 6 the smooth cover H to Z is a base change of that surjection and
both morphisms in the descent statement are representable. Thus the changed
citation still supplies exactly the hypotheses and permanence clauses used.
This continuation makes an additional proof edit and updates the base review;
it does not merely re-push unchanged content.

For the other steps I re-opened every cited statement. Step 1 uses precisely
the strict-local chart comparison, faithful-flat strict henselization, and
regular-sequence ascent. Step 3 uses faithful-flat field extension, spectrum
surjectivity, compatible strict local rings, flat-local faithful flatness,
and regular ascent, with the old geometric-stalk identification written
using the pointed-etale triples construction. Step 4 applies only the
space slicing input to T over W. Step 5 uses universal openness only after
flatness and local finite presentation are known. Step 6 composes those
properties and applies source descent separately for each. The full
statements contain each quoted assertion; no cited proof supplies an
unstated theorem.

I re-read the retained children's sources: 06LW's statement and etale-chart
reduction, 04KF/04KG, 04KH/04KJ, 04NG, and 06M2 with 06ET/06EV. Their arbitrary
base hypotheses match the retained statements. I re-read the exact Mathlib
regular-sequence ascent declaration at Flat.lean:92-94 and its faithfully-flat
variable at line 81, and the retained search results. The geometric hits
are scheme statements or ordinary stalk statements; none states the space
or stack inputs. No statement or search question changed, so the actual
search records, including unavailable LeanSearch, are reused unchanged.

I checked B--E against these files: all children remain statement-only or
an exact Mathlib leaf, none restates the stack assertion, and all non-elementary
inputs remain cited. The explicit chart-point argument is elementary from
surjectivity and is included in the step, not promoted to a new node. The
source equations still define the same closed subspace by the displayed
quotient calculation. No Noetherian, separability, or quasi-compactness
hypothesis is used. For r=0 the zero locus is the source; an empty fibre
cannot have the specified point, and point-local rings are nonzero, as
required for the regular empty sequence. All six steps remain below 2000
characters. I regenerated all 17 verbatim citation entries from the current
statements and verified coverage of every step/node pair. The final dry run
and push must validate this edited version. All writes remain in the sandbox.
