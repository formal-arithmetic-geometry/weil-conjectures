# Q86: lem-trf-affinoid-canonical-reduction-finite-type

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affinoid-canonical-reduction-finite-type.json: statement, split with four proof steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-finite-affinoid-canonical-reduction.json: one new statement-only node, unsplit; no Mathlib match. This is relative module finiteness of reductions under an arbitrary finite map, not finite type of one reduction over the residue field.
- citations.json: four step/node entries, each copying the cited statement verbatim.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag, affinoid, TateAlgebra, canonicalReduction and canonical reduction. The few ordinary scheme-reduction matches do not concern this theorem. No sorry-free project declaration gives the item or the new relative theorem.

## WANTED

WANTED: Bosch–Guentzer–Remmert, Non-Archimedean Analysis, Corollary 6.3.4/3 and Theorem 6.3.5/1, for the item and lem-trf-finite-affinoid-canonical-reduction. The local literature checkout has no archival book. The online book scan was too large for the web reader. No document was downloaded or written to the repository.

WANTED: Temkin, A new proof of the Gerritzen-Grauert theorem, introduction printed p.2 and section 2, https://math.huji.ac.il/~temkin/papers/Gerritzen_Grauert.pdf, archival copy for the new node. Read the primary author PDF online: the introduction explicitly gives equivalence of finiteness of a strict-affinoid map and its reduction map, citing BGR 6.3.5/1; it fixes the nontrivially valued strict-affinoid setting. This suffices to verify the smaller node's statement, not to claim that its proof has been supplied.

WANTED: Bosch, Lectures on Formal and Rigid Geometry (April 2008), section 1.2 Corollary 10 and section 1.4, for the already-existing normalization and supremum nodes. Read the author's primary PDF https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf online. Their existing source locations are retained.

## What was wrong or missing

The imported item had a correct statement but no proof. Its descriptive BGR reference was not an argument. The proof now normalizes by a Tate algebra, computes that Tate algebra's reduction coefficientwise, uses relative module finiteness, and gives explicit algebra generators. In particular integrality alone is not substituted for finiteness: an integral algebra need not be finite type. Nor is finiteness of the spectral unit ball as a valuation-ring algebra assumed. The parent's distinguished-presentation theorem depends on this item, so citing it would be circular. None of the chosen existing dependencies reaches this item (checked the 49-node union of their dependency closures).

The current latest blueprint sk-i-curve-zero is the contracting-correspondence proof. This node was created as a historical analytic input below lem-trf-local-term-locality, as its retained blueprint.from explicitly says. This split repairs that existing supporting lemma without replacing a step of the current unit or changing the chapter. The item is not the unit's key node, so no unit realization file was changed.

## Search record and Not duplicates

Searched the entire DAG statements for affinoid plus reduction/finite, relative finite maps, BGR 6.3.5/1 and 6.3.4/2; searched project source by the corresponding notions. Ran tools/blueprint_refs.py ancestor for the item and search for affinoid, canonical reduction, finite reduction and 6.3.5. There is no blueprint relative-reduction theorem: affinoid has zero blueprint matches; canonical/finite reduction matches concern unrelated sheaf coefficient reduction. The existing analytic nodes are reused.

## Not duplicates

lem-trf-finite-affinoid-canonical-reduction vs lem-trf-affinoid-canonical-reduction-finite-type: the new node treats a specified finite map A to B and asserts module finiteness over the source reduction; the item asserts finite algebra generation over the residue field without a specified finite map. Choosing a normalization, computing its reduction, and assembling generators are necessary steps between them.
lem-trf-finite-affinoid-canonical-reduction vs lem-trf-affinoid-powerbounded-integral: the existing node gives individual integral equations over the image of a presentation unit ball, not finite modules on canonical reductions.
lem-trf-finite-affinoid-canonical-reduction vs lem-trf-finite-affinoid-spectral-equation: the existing node gives elementwise optimal spectral polynomial equations; integral equations alone do not give finite modules on reductions.
lem-trf-finite-affinoid-canonical-reduction vs lem-trf-affinoid-distinguished-presentation: that node chooses a new surjective presentation with full unit-ball surjectivity and depends on this item; it does not state the relative theorem for a specified finite map.
lem-trf-finite-affinoid-canonical-reduction vs lem-trf-tate-reduction-norm-lifting: the existing node assumes surjectivity on reductions and gives exact norm lifts; the new node assumes module finiteness and neither requires nor claims surjectivity on reductions.

Mathlib searches were run only through msearch.py; all results are recorded from searches.jsonl. Two distinct natural-language phrasings were tried for the new node and the item, alongside Loogle and whole-Mathlib grep. Hits concern finite morphisms of schemes, quasi-finite residue fields, finite quotients, and ordinary finite-type quotient algebra descent. Read RingTheory/Finiteness/Defs.lean lines 164–190 and RingTheory/Finiteness/Quotient.lean: module_finite_of_liesOver applies to quotients of already finite modules; it does not show that spectral unit balls form a finite module. No hit supplies the analytic result. No new Mathlib leaf.

## Review by Q86

I read delivery-errors B–E, both copies, and checked the actual statements of every cited node. The item agrees with BGR 6.3.4/3 as confirmed by the standard normalization argument and the finite-map theorem. I read Temkin's primary PDF introduction and section 2 for the new node: both reductions use the spectral seminorm and strict affinoids, over a complete nontrivially valued field. The algebraically closed reduced specialization in the new node is within those hypotheses; no characteristic-zero or discrete-valuation restriction has been introduced. BGR and the confirming primary PDFs are absent from local literature, so proof_origin.by is honestly agent, not document. No SGA route is used.

Step 1 uses the actual spectral Banach norm statement to make the unit ball a ring and the strict ball an ideal, and uses the actual Tate-normalization statement to obtain an injective module-finite map from a Tate algebra. The given nonzero quotient makes its presentation ideal proper, exactly the normalization hypothesis. The source is reduced by its coefficient-series construction; no domain assumption on C is made.

Step 2 uses precisely the existing supremum-calculus statement: finite maximal residue fields, quotient-Gauss bound, and equality with Gauss norm on a Tate algebra. I checked that algebraic closedness identifies finite residue fields with K and the quotient-Gauss estimate makes those evaluations continuous. The reverse correspondence comes from kernels of K-characters. The coefficient reduction is written out: cofinite convergence makes the norm-one support finite; the remaining coefficients have supremum less than one by a finite/tail argument. This addresses the important dense-value-group case; individual coefficients below one without this argument would not suffice. Ring compatibility and polynomial coefficient lifts finish the identification. This is one routine coefficient argument, not an unproved identification hidden behind 'transport'.

Step 3 uses exactly the new node's module-finiteness conclusion and its norm bound, not any proof of that node. The A and C of step 1 are nonzero reduced strict affinoids over the required K. Finite module generators lift to representatives by the definition of quotient; variable images lie in the unit ball by the norm bound. No requirement of norm-one lifts for arbitrary elements is used.

Step 4 is elementary: expand a class as a finite module linear combination, write its coefficients as polynomials using step 2, and the displayed combined list generates as an algebra. The two- or three-line finite-module-to-finite-algebra argument is kept as a step, not a new node. No ordinary commutative algebra lemma is hidden here.

Tested small cases: C=K (d=0), C a Tate algebra (identity normalization), a finite product K times K (finite reduced but not a domain), and arbitrary characteristic. The new relative statement includes the identity map, finite products and a projection between reduced affinoids. Its conclusion is module finiteness, not surjectivity; e.g. K to K times K need not be surjective on reductions. The excluded zero algebra and nonreduced dual-number algebra are not silently used. All definitions of affinoid and reduction are inline or cite their correct definition nodes. The new node has no proof, proof dependencies, or proof sketch in its statement. Every new blueprint field is filled and the inherited chain is preserved. Every step is below 2000 characters and the total assembly proof is below 3000 characters. Citations.json quotes are verbatim full statements. No statement correction was necessary.

## Unfinished

No missing step in the item's assembly proof. The new relative finite-reduction theorem remains an honest statement-only stage-1 task; its own proof is not claimed here. Required dry-run and push results are reported by the delivery command.
