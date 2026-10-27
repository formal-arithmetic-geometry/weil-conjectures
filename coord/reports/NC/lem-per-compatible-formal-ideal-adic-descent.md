## Worker report

Item: lem-per-compatible-formal-ideal-adic-descent. Group NC, 2026-10-24. Stage 1 only; no Lean was written or compiled. The repository was read only; all authored files are in this item's sandbox.

Files written: the item under dag/nodes/sec-deligne-laumon-a1/, the following three statement-only nodes in that directory, this report, and citations.json. Search commands wrote searches.jsonl; write_split.py records the construction of the JSON files.

## New nodes

- lem-per-flat-primary-fibre-recovery: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source searches. This is a theorem about an arbitrary flat map and primary ideal, not a clause of the compatible-formal-ideal theorem.
- lem-per-jacobson-adic-completion-faithfully-flat: statement, unsplit; no exact Mathlib match. Flatness alone and separatedness alone were the closest returned results.
- lem-per-flat-ideal-finite-intersection: statement, unsplit, with a complete project attachment candidate. Mathlib's kernel preservation and localization-only intersection lemmas are not the exact statement.

## Attachments

Ideal.map_iInf_of_flat belongs to lem-per-flat-ideal-finite-intersection, lean/WeilConjectures/Mathlib/RingTheory/Flat/Equalizer.lean:84 (module WeilConjectures.Mathlib.RingTheory.Flat.Equalizer). Its finite-family statement includes the empty family and its proof at lines 86–94 has no sorry. The binary argument at lines 45–81 was also read; no sorry occurs there. This is a candidate for the independent closure audit, not a claim to have run that audit. It is recorded in lean_candidates. There is no exact project declaration for the delivered item: searches by its blueprint tag and by compatible formal ideals / primary completion / Rotthaus found none. Other declarations about formal glueing and compatible affine ideals have different objects and conclusions.

## Literature and proof origin

WANTED: Rotthaus, *Komplettierung semilokaler quasiausgezeichneter Ringe*, Nagoya Math. J. 76 (1979), pp.173–180, especially Theorem 3 Claim 4 and (4.1)–(4.3), pp.178–179, for lem-per-compatible-formal-ideal-adic-descent. The paper is not in this clone's literature directory, and Cambridge's PDF could not be read through the web tool. I did not download it. The item retains its existing bibliographical source. The delivered proof is explicitly agent-written from the local Stacks text; it is not presented as a verified transcription of the unavailable paper. The source's primary-component strategy, already specified in the item's source place and parent split, is retained.

I read literature/stacks-project/algebra.tex at lemma-hathat-finitely-generated (05GG), lemma-radical-completion (05GI), lemma-completion-flat (00MB), lemma-completion-faithfully-flat (00MC), lemma-completion-Noetherian-Noetherian (0316), lemma-zero-at-ass-zero (0311), lemma-bourbaki (0312), and lemma-flat-intersect-ideals (0BBY), checking the tag-to-label table. The associated-prime argument used in 0330's proof was also inspected as context. The new completion node is exactly the full 00MC assertion. The new intersection node is the finite induction of 0BBY, also exactly stated in the project source. The recovery node is a consequence of flatness and 0311/0312, stated for the entire fibre rather than just minimal primes.

Here is the argument intended for the recovery node (kept in this report, not in its unsplit statement): if s is outside sqrt(q), multiplication by s on R/q is injective by primaryness. Flatness preserves that injection on S/qS. Every associated prime Q of S/qS therefore contracts inside sqrt(q), and it contains q and hence sqrt(q) on contraction, so it contracts exactly to sqrt(q). Apply the injectivity of the map to localizations at associated primes from 0311. Testing at all primes of that fibre includes every associated prime, so it detects membership in qS. The zero target ring gives the allowed empty fibre. This establishes the stated generalization without assuming reducedness of S/pS.

## What changed and what was wrong

The item was statement-only and unsplit. Its statement and statement dependencies are unchanged. No dispute or source error was established. The radicality assumption on pC is retained, but the whole-fibre form of primary recovery does not require it. This is explicitly disclosed in proof step 7; no hypothesis was silently changed. Nonmaximality is essential in the transfer step because compatibility was only assumed there. Step 1 proves that a nonmaximal source prime cannot have a maximal prime of C above it, using the finite-quotient identification and the geometric-series Jacobson argument.

The old empty proof gave neither the maximal-primary case nor the equality identifying the contracted ideal in the source completion. Both are now written. The choice of one fixed e_p, rather than independently chosen ideals for each P, is used exactly in step 6. No singular-locus interpretation, nonzero ideal, or J-completeness enters.

## Blueprint and duplicate searches

Read the chapter and unit records sec-deligne-laumon-a1 and sk-p-dl-a1-perverse, and the current latest blueprint's lem-per-artin-gabber-affine-curve statement and proof. Read the existing local-G-ring lifting parent and its prescribed ideal-descent step. tools/blueprint_refs.py ancestor returned lem-per-artin-gabber-affine-curve. The inherited via chain is retained and prepended with this item for the new nodes. Their places identify the ancestor's regular-model/purity step through the existing G-ring lifting chain and this item's precise primary-descent use.

Whole-blueprint searches were run for primary, completion ideal, semilocal completion, flat primary, completion flat, primary extension, ideal intersection, flat intersection, Jacobson completion, primary fibre, primary reduced, and completion faithfully. No blueprint node states any of the three new facts. Whole-DAG searches used the same notions, the exact candidate declarations, and the Stacks tags. Source searches also found the exact finite-intersection project theorem. The general associated-prime nodes were read and are ingredients of recovery, not statements of recovery. The completion node extends the local-maximal-ideal result to arbitrary ideals inside the Jacobson radical, needed here for a possibly nonlocal semilocal ring.

## Mathlib searches

Every newly recorded query was run through the required msearch.py command and is in searches.jsonl. Results in mathlib_searches preserve the actual log records (tool, verbatim query, hits, digest, and service status) with a verdict after reading the displayed hits. All four services used responded successfully. The inherited item searches were preserved; new searches address the same item independently for this delivery.

For recovery, the second semantic query tested the reduced-minimal-prime variant suggested by the source; the hits were going-down and prime-localization theorems, not ideal recovery. I then kept the stronger whole-fibre statement for which the injectivity argument above applies. Lasker.comap_localized₀_eq_iInf was read: it is uniqueness for a given primary decomposition under localization, not recovery after a flat algebra extension.

For faithful completion, AdicCompletion.flat_of_isNoetherian provides only flatness; the returned Hausdorff and tensor-completion theorems do not individually state faithfulness. For finite intersections, the localization-specific IsLocalization.map_inf and Mathlib's Module.Flat.ker_lTensor_eq were read. The latter needs the quotient/product kernel identifications; the exact already-proved project declaration was therefore recorded as an attachment candidate, not mislabelled as Mathlib.

## Review by NC

I checked the actual node statements against every use. Step 1 uses the completion-Noetherian statement to know C is Noetherian, the new full-Jacobson completion statement for faithful flatness, and the mod-power statement for each canonical finite quotient. The geometric-series argument is written in the step: the inverse-limit inverse proves the Jacobson containment, and the quotient isomorphism proves both directions needed for maximal-prime contraction. It does not assume that every prime of a completion comes from the base.

Step 2 uses lem-per-noetherian-primary-decomposition exactly for its finite primary decomposition and its definition of primaryness. Contraction and radical contraction follow from the written power test. K contains J^nC, so the radicals of all its components contain JC. The empty decomposition is explicitly included.

Step 3 uses the finite-generation/radical-power statement to put a power of rC in a maximal-primary component, and the finite-quotient statement to descend that open ideal. It does not assert that an arbitrary ideal of the completion descends. The inclusion rC in the maximal radical comes from step 1 and was verified before the power bound was applied.

Step 4 uses the localization-Noetherian statement for B_p and C_P; the completion-Noetherian statement for U,T; the local-completion-local-ring statement for their maximal ideals; the local-completion-faithful-flat statement and the contraction statement to contract QT correctly; and the radical-power bound to prove QT is open at its maximal ideal. Primary saturation under localization is written out, so no unquoted primary-extension theorem is used.

Step 5 uses the local-completion-local-ring statement to identify pU, the radical-power bound to get an open ideal A, and the mod-power statement for B_p to show A=qU. The kernel/finite-quotient computation is spelled out: every class of A has a representative from qB_p and the error is already in qU. The source maximal ideal maps into the target maximal ideal because it is generated by images of p; units stay units. These verify locality of the canonical comparison without confusing the two maximal ideals.

Step 6 uses local-completion faithful flatness and ideal contraction for C_{P'} to T_{P'}. The inclusion in the fixed source completion U was already proved in step 5. For every P' over p, p contains J and is nonmaximal, and step 1 makes P' nonmaximal. Thus the exact compatibility hypothesis applies with the same e_p. This is the essential transfer: it is an extension of one ideal inclusion along U to each target, not an asserted equality of the different targets.

Step 7 uses the new recovery node exactly with R=B, S=C, and q the contraction of the chosen primary component. B,C are Noetherian and the map is flat by step 1; q is proper and p-primary by step 2. Step 6 supplies the inclusion in every localization requested by recovery. The recovery node asks for the entire fibre, and the proof supplies the entire fibre. It neither asks for reducedness nor silently uses a minimal-prime-only version.

Step 8 uses the finite-intersection node exactly for the finite family q_i. Contraction commuting with intersection follows by membership; the two inclusions that identify the middle intersection with K are written. Step 9 uses the faithful-flat contraction node for the two B-ideals a_{n+1}+J^n and a_n after checking that their extensions are equal. The inclusion J^{n+1}C in J^nC and extension of sums are from the definitions.

Every cited node was opened and its statement was copied verbatim into citations.json for its actual step. No quote was taken from a proof or a definition in place of a theorem. Off-unit completion/ideal tools are explicitly declared in split_report.tool_uses; they implement this prescribed commutative-algebra input and do not replace the unit route. All nine non-elementary steps are below 1000 characters, so none is over the 2000-character hidden-lemma threshold. The maximal-primary and open-completion computations remain proof steps because they are direct finite-quotient arguments, not new clause nodes.

For the three new statements I checked standalone objects, all hypotheses, TeX, definition references, and absence of a proof inside the statement. Primaryness and its radical are defined inline in recovery; flatness, Noetherianity and prime localization cite their actual definitions. Recovery was tested on the identity map, on q=(x^2) in k[x] followed by the polynomial flat extension, on nonreduced primary quotients, and on the zero target ring. It does not assume a primary ideal stays primary after extension. Faithful completion was checked for I=0 (identity), the zero ring, and a product of two Noetherian local rings (so the local-only node would not suffice). Its Jacobson hypothesis is not dropped. Finite intersections was checked for zero ideals, the empty index family, and a localization that turns an ideal into the unit ideal. The item was checked for E=C, E=0, J=0, Artinian semilocal B, and no nonmaximal primes over J: in the last two cases every primary component is dealt with by step 3, so vacuous compatibility creates no gap.

Corrections made during self-review: the initial proposed recovery indexed only minimal primes and required reduced pC. Replacing it with the whole-fibre version removes an unnecessary identification and makes explicit why the available compatibility suffices. I also retained the maximal-primary argument instead of treating it as automatic; and I requested the already-proved intersection attachment rather than reproducing its proof. No statement correction to the item was needed.

## Not duplicates

lem-per-flat-ideal-finite-intersection vs lem-weil-pbc-quasi-coherent-ideal-intersection: the existing statement concerns The intersection of two quasi-coherent sheaves of ideals is quasi-coherent (sheaf intersections or annihilators under localization); the new node concerns extension of any finite family of ideals along any flat ring map.

lem-per-flat-ideal-finite-intersection vs lem-weil-pbc-annihilator-localization-finite: the existing statement concerns Annihilator of a finite module commutes with localization at an element (sheaf intersections or annihilators under localization); the new node concerns extension of any finite family of ideals along any flat ring map.

lem-per-flat-primary-fibre-recovery vs lem-sbc-power-series-punctured-germ-detection: the existing statement concerns Germ detection on the punctured power-series zero section; it does not recover an arbitrary primary ideal extended by an arbitrary flat map from the localizations on its radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-sbc-power-series-prime-extension: the existing statement concerns Prime extension to multivariate power series; it does not recover an arbitrary primary ideal extended by an arbitrary flat map from the localizations on its radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-sbc-open-section-associated-germ-detection: the existing statement concerns Associated germs detect sections on opens of Noetherian affine schemes; it does not recover an arbitrary primary ideal extended by an arbitrary flat map from the localizations on its radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-sbc-depth-two-punctured-function-detection: the existing statement concerns Detecting functions at punctured-spectrum germs; it does not recover an arbitrary primary ideal extended by an arbitrary flat map from the localizations on its radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-sbc-power-series-punctured-global-sections: the existing statement concerns Global sections on a power-series open with punctured zero section; it does not recover an arbitrary primary ideal extended by an arbitrary flat map from the localizations on its radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-trf-flat-local-maximal-associated-tensor: the existing statement concerns Maximal associated prime criterion for flat local tensor extension; it does not recover an arbitrary primary ideal extended by an arbitrary flat map from the localizations on its radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-weil-pbc-associated-primes-flat-base-change: the existing node computes associated primes of a tensor product; the new node detects ideal membership by all localizations on a specified radical fibre.

lem-per-flat-primary-fibre-recovery vs lem-weil-pbc-module-injects-localizations-associated-primes: the existing node detects module elements at associated primes; the new node identifies the fibre that suffices for a flatly extended primary ideal, with no input associated-prime list.

lem-per-flat-primary-fibre-recovery vs lem-weil-pbc-associated-primes-flat-quotient: the existing node bounds associated primes after flat quotient base change; the new node gives an ideal-recovery intersection equality.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-trf-completed-maximal-localizations-detect-zero: the existing statement concerns Completed maximal localizations are complete local flat tests for zero derived objects and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-trf-completed-conormal-resolutions: the existing statement concerns Algebraic and formal conormal complexes resolve completed differentials and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-trf-generic-center-formal-normal-slice: the existing statement concerns Generic smooth centers and completed normal coordinates and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-trf-nodal-points-reduced-algebraically-closed: the existing statement concerns A curve with only smooth points and nodes over an algebraically closed field is reduced and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-trf-diagonal-taylor-faithful-flatness: the existing statement concerns Faithfully flat Taylor realization at the residue-field diagonal point and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-sfb-nodal-ideal-scalar-gluing: the existing statement concerns Componentwise scalar gluing for a nodal cluster ideal and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-weil-pbc-local-completion-faithfully-flat: the existing node treats only completion at the maximal ideal of a local ring; the new statement treats arbitrary Jacobson-contained ideals of a possibly nonlocal ring.

lem-per-jacobson-adic-completion-faithfully-flat vs lem-weil-pbc-completion-dimension: the existing statement concerns The completion of a Noetherian local ring has the same dimension and at most particular local completions; the new node is faithful flatness for any Noetherian ring and any ideal contained in its Jacobson radical.

## Unfinished work

No remaining gap in the item assembly. The two general unsplit algebra statements remain queued for their own one-level splits, as required; the third has a project attachment candidate for the independent audit. Delivery preflight and server checks are the next required validation.
