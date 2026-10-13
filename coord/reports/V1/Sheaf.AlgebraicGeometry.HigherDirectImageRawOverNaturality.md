## What changed

Repair of the X-dd64f landing return: the reported failure is the batch tool
copying its source tree, before any Lean compiler error. The requested repair
uses deliver3.py to fetch sheaf-dag and reconstruct the single delivery commit
on that base, with WEIL_SERVER_COMPILE=1 for the explicitly requested server
check. The local single-file compilation passed in 28.0 seconds. The reviewed
mathematical proof and statement correction are retained; no landing-tool
script is changed. This worker prepares only a dry run; the second reader
will deliver the refreshed commit. The first repair dry run rebuilt commit
680da2a55f on freshly fetched sheaf-dag and printed OK: local compile, axiom
probe, explicitly enabled server compile, and stage-3 preflight all passed.
The final dry run includes this repair record. Nothing is pushed.

In `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality`, proved
`AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_restriction` by specializing
`higherDirectImageRawTrianglePullback_restriction` to the canonical coefficient map.
The coefficient map is explicitly constructed; no witness is chosen from an existence theorem.

Factored `higherDirectImageRawOverPullback` through the existing raw triangle construction.
Its expansion has exactly the previous five factors; the equality proofs agree by proof
irrelevance. Every existing signature and visibility is preserved. The triangle import
is now public because the public definition uses that construction. This avoids repeated
elaboration of the expanded derived expression; an earlier restriction-only proof with the
expanded definition exceeded 60 seconds, whereas the factored version compiled in 33 seconds.
The change record is `coord/changes/higherDirectImageRawOverPullback-factor-triangle.md`.
No external module is adapted.

Updated the restriction node's proof to record the specialization, and the conjunction
node's proof dependencies to name its actual component theorems. The comparison node and
its named hole remain unchanged. No new modules or nodes are added.

Repair H3: replaced the entire restriction node statement with the reviewer-requested
over-W specialization and recorded `statement_change`, preserving every Lean signature.
The correction record is
`coord/changes/higherDirectImageRawOverPullback-restriction-statement.md`.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_restriction`
(node `sbc-lem-higher-image-raw-over-restriction`).

One hole remains in the delivered module:
`AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_comparison`
(node `sbc-lem-higher-image-raw-over-comparison`). It is exactly `:= by sorry`.
No holes are added or split off. The already proved
`AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_toSheaf` retains its original
conjunction proof.

The restriction proof uses the existing named statement
`AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback_restriction`, which remains
holed in its own module (node `sbc-lem-higher-image-raw-triangle-restriction`). This is an
existing proof dependency, not a new hole of this delivery.

## No longer needed

Removed direct proof imports:
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`;
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
- `Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom`.

The first two modules' required declarations remain available transitively from the public
imports. The completed restriction proof does not use `higherDirectImageRawTransition_toHom`
(node `sbc-lem-higher-image-raw-transition-to-hom`); its module is removed from this module's
proof imports. That theorem remains a useful candidate for the uncompleted comparison
proof, so this partial delivery does not assert that its argument is mathematically
unnecessary for closing that remaining hole. No other mathematical nodes are pruned.
The old direct proof dependency `lem-weil-pbc-inverse-image-composition` of the
restriction node is now supplied through the triangle restriction node; it is retained
in the statement dependencies and the unfinished comparison plan. For the conjunction
node, the former direct dependencies `def-sbc-module-higher-image-transitions` and
`sbc-lem-higher-image-raw-triangle-restriction` are now reached through the component
nodes and remain needed transitively. Only
`sbc-lem-higher-image-raw-transition-to-hom` loses its direct import edge in this module;
no claim is made that any of these modules leaves the targets' whole import closure.
The obsolete private helpers `raw_presheaf_map_apply` and `pullback_class_naturality`
are removed: the delivered proof uses the existing triangle statement directly.

## Where the brief, the DAG or earlier work was wrong

The comparison component's node repeats the derived adjunction argument, whereas the
existing `higherDirectImageRawTransition_toHom` already packages its morphism equality.
I tried specialization, identification of the homology map with `higherDirectImageOverMap`
by functoriality and associativity, and evaluation with the fixed free-sheaf section map.
Full versions repeatedly exceeded the 60-second compile limit; these attempts are not
included as incomplete proofs. The comparison declaration remains its original named hole.

The restriction node's inherited prose incorrectly stated the general triangle result,
while its Lean record states the over-W specialization. Repair H3 replaces the entire
prose statement with the requested over-W version and records the old statement,
reason, source, and base citers in `statement_change`. The mismatch is now corrected. The existing general triangle node and theorem supply
that specialization without changing any signature or adding any assumptions. Identity
arrows, arbitrary integer degrees, zero classes and empty schemes impose no additional
conditions on this application. The unit record has no realized node at this component;
its geometric route is preserved.

## Earlier second reading (a previous round; superseded)

1. Compared the complete delivered module with the repository file using `diff -u`
   and the declaration parser. All six existing public declarations retain byte-identical
   signatures, visibility and docstrings. The only public definition body changed is
   `higherDirectImageRawOverPullback`, recorded in
   `coord/changes/higherDirectImageRawOverPullback-factor-triangle.md`. Its coefficient
   morphism is the single-complex comparison followed by the inverse `upperStarComp`
   at G, exactly the original last factor before shifting. The triangle supplies exactly
   the original first four factors; its equality proof differs only by proof irrelevance.
   A standalone scratch theorem importing the compiled original module proves by `rfl`
   that its pullback equals the factored RHS (56.6 seconds), with only the three
   permitted axioms. This verifies definitional equality without relying on any
   unproved restriction or comparison statement.
   The change record lists the 202 downstream modules and seven direct textual users,
   matching a fresh `tools/downstream.py --uses higherDirectImageRawOverPullback` check.
   None requires adaptation. Verdict: no Lean statement or mathematical meaning changed by the factorization.
   Repair H3 separately corrects the restriction node prose as recorded below.

2. Compiled the delivered module with `lcompile.py`: clean, 29.6 seconds. There is
   exactly one textual `sorry`, the unchanged named comparison theorem; no forbidden
   declaration form, hollow definition or arbitrary chosen witness occurs. A scratch
   copy with `#print axioms` for all six public declarations compiled in 28.6 seconds:
   the three definitions use only `propext`, `Classical.choice`, `Quot.sound`;
   the three theorems additionally use `sorryAx`. For restriction this is inherited
   from the already existing triangle restriction theorem; comparison remains open.
   The conjunction is consequently still conditional on those existing holes.
   Verdict: one original local hole closed, zero added; not an axiom-free completed module.

3. No new statement, node or split-off hole is introduced. Read the triangle pullback
   construction and its restriction theorem, the transition-to-Hom theorem, and
   `HigherDirectImageTransitions`. The restriction specialization uses
   a = f.left, h = B.hom composed with k, h' = A.hom composed with k,
   K = (B*G)[0], K' = (A*G)[0], and the explicit coefficient morphism.
   The hypothesis a composed with h = h' follows from associativity and `Over.w`;
   no geometric hypothesis or restriction on q is introduced. Identity arrows, q = 0
   or negative q, zero classes and empty schemes remain admissible. Repository searches
   for raw pullback/restriction and Mathlib searches under restriction/pullback and
   `NatTrans.naturality` found no shorter packaged specialization than the existing
   triangle theorem. Verdict: genuine specialization of an existing general dependency,
   with no new restatement presented as progress.

4. Read the proof from the conjunction through its two component declarations.
   The conjunction proof is unchanged; restriction follows the shortest available
   packaged route. The comparison hole and its original natural-language argument stay.
   The public triangle import is necessary because the public definition uses its
   construction. Transitions supplies `higherDirectImageOverMap`; cohomology presheaf
   supplies the raw presheaf and comparison. Removed proof-only imports are documented.
   Checked all former `proof_deps` of the two edited nodes: the report now distinguishes
   removed direct edges from composition, transition and triangle dependencies still
   used transitively. Read `dag/units/sk-lem-failure-field.json`: its `realized` record
   is `statement: []`, `steps: [[]]`, and this specialization bypasses no realized unit
   statement or step. Verdict: route preserved; only direct import pruning claimed.

5. Repair update to the earlier second reading, addressing reviewer X-4d817 H3:
   the restriction node now states exactly the requested over-W specialization,
   with K_B=(B^*G)[0], K_A=(A^*G)[0], and the canonical coefficient identification.
   Its existing Lean record and the delivered proof have those same parameters.
   The old general prose is preserved verbatim in `statement_change.old_statement`
   and the correction record
   `coord/changes/higherDirectImageRawOverPullback-restriction-statement.md`.
   This correction changes `statement` and adds `statement_change` in addition to
   the previously reviewed proof fields; Lean records and signatures are preserved.
   No base DAG node cites this restriction node in stmt_deps or proof_deps; the
   conjunction's new dependency in this delivery needs precisely the corrected
   specialization. Each proof_deps still equals the union of its proof steps' uses.
   The general triangle theorem remains the dependency supplying the specialization.
   Verdict: the recorded correction resolves the prose/Lean mismatch; it introduces
   no new theorem, hole, hypothesis, or target change. This paragraph updates the
   existing reading for the requested repair; no additional reader was started.

Second-reading changes: retained the earlier proof and provenance review, and updated
point 5 to describe the explicit H3 statement correction instead of acknowledging an
unresolved mismatch. No Lean proof was rewritten during this repair.

## Earlier second reading (a previous round; superseded)

1. Compared the only delivered Lean module against the repository with `diff -u`
   and the project's declaration parser, and separately compared the six public
   signature substrings byte for byte. All signatures, visibility and existing
   docstrings are unchanged. The two removed helpers were private. The public
   definition factorization and public triangle import have a change record.
   Independently compiled scratchpad/FactoredCheck.lean against the original shared
   module: the equality of its original pullback and the factored triangle expression
   is proved by `rfl` (59.1 seconds), with only propext, Classical.choice and Quot.sound.
   The triangle expansion has the same five factors, with equality witnesses identified
   by proof irrelevance. Verdict: no change to any Lean statement or target meaning.
   The restriction DAG prose correction is explicitly recorded; it describes the
   existing specialized Lean statement, rather than asserting the general triangle lemma.

2. Compiled the delivered module locally with lcompile.py: no errors or warnings,
   32.6 seconds. Independently made and compiled scratchpad/CurrentReadingAxioms.lean
   with `#print axioms` for all six public declarations (32.2 seconds). The definitions
   have only the three permitted axioms. Each theorem additionally has sorryAx:
   comparison is the single unchanged local named hole, restriction inherits the
   existing triangle theorem's hole, and the conjunction depends on both components.
   No forbidden declaration form, hollow definition or arbitrary existential witness
   appears. Verdict: one of two original local holes closed, zero holes added;
   this is a reduction to an existing dependency, not an axiom-free completed module.

3. No statement, module, node or hole was split off. Read the existing triangle
   construction and restriction theorem, the raw transition-to-Hom statement, and
   the higher-image transition definitions. The explicit coefficient morphism is
   the single-complex comparison followed by the inverse composition identification
   at G. Its triangle is f.left with B.hom composed with k and A.hom composed with k;
   associativity and Over.w prove the triangle relation. The application places no
   further hypotheses on schemes or on the integer degree. Identity arrows, empty
   schemes, zero classes, and negative degrees are allowed by this specialization.
   Fresh repository searches for higherDirectImagePresheaf pullback/restriction and
   triangle restriction, plus msearch loogle for CategoryTheory.NatTrans.naturality,
   found generic naturality but no shorter packaged specialization. The upstream
   higherDirectImagePresheafToSheaf_naturality varies coefficients at a fixed
   structure morphism and does not close the remaining comparison. Verdict: a true
   specialization of an existing dependency; no disguised restatement added.

4. Read downward from the conjunction to its comparison and restriction components.
   Retained the direct specialization proof and the unchanged comparison hole.
   Transitions and CohomologyPresheaf supply public signatures and definitions;
   the now-public triangle import supplies the body of the public pullback definition.
   The three removed direct proof imports and every displaced old proof dependency
   are accounted for in No longer needed, including dependencies still needed
   transitively. No whole-closure module pruning is claimed. The unit
   dag/units/sk-lem-failure-field.json has realized.statement = [] and
   realized.steps = [[]]; no realized unit step is bypassed. Verdict: route and
   justified direct import pruning preserved.

5. Compared both delivered nodes against their repository versions. Restriction
   changes only the recorded prose correction and proof fields; conjunction changes
   only proof fields. For each, proof_deps is exactly the union of proof-step uses.
   The Lean records and declaration signatures are unchanged. The corrected
   restriction statement describes the same canonical over-W coefficients as its
   Lean declaration. Its statement_change.old_statement matches the repository
   verbatim, and a fresh scan of all repository node dependencies confirms that
   its base citers list is empty. The conjunction newly uses precisely this
   specialization. No new-node field requirements apply. Verdict: DAG and Lean agree.

Second-reading changes: clarified the restriction-statement change record's Users
paragraph, which had copied discussion of the separate definition factorization;
appended this independent five-point review. No Lean proof or signature changed.

## Second reading by V1

1. Independently compared the delivered module with the repository using diff -u
   and stage3_delivery.decl_table. All six existing public declaration statements,
   visibility flags and docstrings are identical. The only public definition-body
   change and import promotion have the factor-triangle change record. Compiled
   scratchpad/FactoredCheck.lean against the original shared module: rfl proves
   equality to the delivered triangle expression in 51.4 seconds, using only
   propext, Classical.choice and Quot.sound. The first four factors and the explicit
   coefficient map reproduce the original five-factor construction; the triangle
   equality witness agrees by proof irrelevance. Verdict: no Lean statement or
   target meaning changes. The separately recorded restriction-node prose correction
   matches its already existing over-W Lean signature.

2. Independently compiled the actual delivered source and a fresh scratch copy,
   scratchpad/SecondReadingFreshAxioms.lean, with #print axioms for all six public
   declarations. The fresh copy compiled cleanly in 27.4 seconds. All three
   constructions use only the permitted three axioms; all three theorems additionally
   use sorryAx, from the unchanged comparison hole and existing triangle restriction
   hole. Exactly one textual sorry remains, in the named comparison theorem with its
   source and natural-language proof; there are no forbidden forms, hollow definitions,
   existentially chosen coefficient data, or lines over 100 characters. Verdict: one
   of two original local holes closed, zero added; this is not an axiom-free completion.

3. No new or split-off statement is delivered. Read HigherDirectImageRawTrianglePullback,
   HigherDirectImageRawTransitionToHom, HigherDirectImageTransitions, and the upstream
   comparison naturality theorem. The specialization is a=f.left, h=B.hom composed
   with k, h'=A.hom composed with k, K=(B*G)[0], K'=(A*G)[0]; its coefficient map is
   explicitly the single-functor comparison followed by the inverse upperStarComp
   at G. Associativity and Over.w establish the triangle relation. Identity arrows,
   zero classes, empty schemes and every integer degree require no extra hypothesis.
   Fresh rg searches under raw restriction and presheaf comparison, and msearch
   loogle for NatTrans.naturality, found generic naturality but no shorter packaged
   result. The upstream comparison naturality varies coefficients at a fixed scheme
   morphism and does not close comparison along f. Verdict: a valid specialization
   of an existing dependency, with no restatement added as progress.

4. Read downward from the conjunction to both components and their imports. The
   conjunction remains its original pair assembly. Restriction uses the existing
   triangle result directly; comparison remains the original named hole. All three
   public imports serve public signatures or construction bodies. No proof-only
   import is promoted without a public construction needing it. No longer needed
   accounts for every displaced old proof_dep, including composition and transitions
   retained transitively and the transition-to-Hom candidate for the unfinished proof.
   A fresh downstream scan finds the recorded 202 importers and seven textual users;
   none requires adaptation because the factorization is definitionally equal.
   sk-lem-failure-field.realized has statement=[] and steps=[[]], so no realized
   unit step is bypassed. Verdict: unit route preserved; only direct-edge pruning,
   not whole-target-closure module pruning, is claimed.

5. Compared both delivered JSON nodes field by field. Naturality changes only proof,
   proof_deps and proof_origin. Restriction additionally has the explicit recorded
   prose correction and statement_change; its old_statement is byte-identical to
   the repository statement, and a fresh scan confirms no base node cites it.
   Lean records stay unchanged. Each proof_deps equals the union of step uses:
   restriction names triangle restriction, and conjunction names its two components.
   The corrected prose fixes K_B and K_A and the canonical coefficient map exactly
   as the Lean declaration does. No new-node requirements apply. Verdict: DAG agrees
   with the delivered proof and the recorded correction.

Second-reading changes: appended this independent review with freshly reproduced
signature, definitional-equality, axiom, dependency, search and downstream checks.
No Lean proof, signature, node or change record needed further repair.
