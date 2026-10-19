# Stage-1 report: lem-trf-separably-closed-value-group-divisible

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-separably-closed-value-group-divisible.json`: unchanged statement, six-step proof with a complete elementary unequal-value calculation.
- `dag/nodes/sec-trace-formula/lem-trf-separably-closed-artin-schreier-root.json`: Mathlib leaf, `IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C'`, `Mathlib/FieldTheory/IsSepClosed.lean:117–120`.
- `dag/nodes/sec-trace-formula/lem-trf-separably-closed-prime-to-char-root.json`: Mathlib leaf, `IsSepClosed.exists_pow_nat_eq`, `Mathlib/FieldTheory/IsSepClosed.lean:129–141`.
- `citations.json`: verbatim statement quotes for each cited node in each of the six steps.

The retained helper nodes and search evidence are preserved. A proposed additional valuation-arithmetic node was withdrawn into `.msearch/withdrawn-valuation-node.json`: its short argument belongs in the item as elementary Step 2, and the final delivery has only the original two new nodes.

## Attachments

None. Searching `WeilConjectures/` in the designated slopmaster2 source for the item tag and separably-closed value-group/divisibility wording found no matching declaration. Upstream master sorry declarations do not establish completion.

## WANTED

WANTED: local archival copy of literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, finite-height argument PDF lines 1565–1571, for lem-trf-separably-closed-value-group-divisible. The PDF was read online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf on 2026-10-18; no PDF was downloaded or written into the repository. In Step 4 (PDF lines 1565–1571), Temkin states that an easy induction on height proves the value group |K^×| divisible. The detailed valuation and Artin–Schreier argument in this split is agent-written because the local archival copy is absent.

## Not duplicates

- lem-trf-separably-closed-artin-schreier-root vs lem-sc-artin-schreier-k: the latter assumes algebraic closedness and includes the kernel; this helper gives root existence with only separable closedness.
- lem-trf-separably-closed-artin-schreier-root vs lem-sc-field-artin-schreier-sequence: the latter is an exact sequence of etale sheaves, whereas the helper gives a field element solving the polynomial equation.
- lem-trf-separably-closed-prime-to-char-root vs lem-sc-primitive-root: primitive roots of unity with algebraically closed ground field differ from arbitrary power roots over a separably closed field.
- lem-trf-separably-closed-prime-to-char-root vs lem-sc-artin-schreier-k: power-root existence differs from Artin–Schreier surjectivity/kernel.

## Repair of the return

C1/C4/E1: the missing unequal-value identity is now PROVED, rather than assumed. New elementary Step 2 first derives the valuation inequality for nonzero sums by dividing by the term of smaller value. For v(r)<v(s), nonvanishing follows because v(-s)=v(s); if v(r+s)>v(r), applying the proved inequality to (r+s)+(-s)=r contradicts the strict inequalities for both summands. This proves equality for arbitrary ordered value groups. Step 4 applies it to z^p and -z. The proof explicitly excludes z=0 and shows p≥2 using the field characteristic. There is no discretely valued or rank-one hypothesis hidden in this argument.

A4: the sandbox item's created record now has by=worker, item=lem-trf-separably-closed-value-group-divisible, date=2026-10-18, group=Q102. The incorrect original created.item named lem-trf-residual-curve-value-group. All two new nodes name the present delivery item and Q102.

Source place: the sandbox source.place, proof sources, proof_origin and blueprint references now identify the finite-height passage at PDF lines 1565–1571, rather than presenting the divisibility claim as a quoted Proposition 4.3.1 page-27 sentence. Only the assertion is attributed to Temkin; the Artin–Schreier proof is agent-written.

## Maintainer metadata repair required

The installed deliver.py calls merge_split_node on an existing item and retains the origin's protected created and source fields. Reading deliver.py's packaging loop and tools/README.md's field-ownership table confirms this. Consequently the sandbox corrections to created and source cannot reach the generated delivery commit through the authorized tool. I have not modified the launcher or the shared repository. Please apply these explicit corrections in the maintainer's authorized metadata repair:

- created.item: lem-trf-separably-closed-value-group-divisible (currently lem-trf-residual-curve-value-group). The sandbox also records group Q102 rather than N4.
- source.place: Temkin, Stable Modification, finite-height argument, PDF lines 1565–1571: the explicit sentence that separable closedness makes the ground-field value group divisible; local archival copy unavailable. Preserve source.document and source.url.

The proof_origin, step sources and report carry the corrected provenance through the ordinary delivery, so the mathematical proof is reviewable. These two protected origin fields remain a packaging/maintenance limitation, not a mathematical claim of completed metadata repair.

## Review by Q102

I read the standing stage-1 brief, the complete B–E delivery-error checks, SETUP's three blueprint levels, GOAL, dag-sync, the worker role, the item's chapter and unit, the current shared item, all sandbox nodes, all cited definition statements, and the retained searches.jsonl. The current shared item is still unsplit and has the same statement and origin metadata as the returned work. Its historical ancestry is retained. I did not replace the unit route or edit its realized fields.

For the item, the valuation calculation is checked directly from its self-contained subring hypothesis. I read Stacks algebra.tex, lemma-valuation-group (00ID), definition-value-group (00IE), and lemma-properties-valuation (00IF), including their omitted-proof notices. Because the latter does not provide the missing proof, I supplied that proof in Step 2. I also read Temkin, Stable Modification, online at the URL recorded above, and verified the finite-height source passage at PDF lines 1565–1571: it states the divisibility assertion via an induction on height but does not spell out the root construction used here. The maintainer's correction of its location is applied wherever split-owned provenance can carry it.

Step 1 uses def-weil-field for field operations; def-kun-separably-closed supplies the standing field hypothesis, although separable closedness is not yet used in the order construction. Membership of b/a in V defines the quotient order; independence of unit representatives, antisymmetry, totality and translation invariance are each justified explicitly. Step 2 uses only field operations and that order: 1+y/x lies in V by subring closure, and the second inequality rules out cancellation at unequal values. This is the elementary calculation behind the return, not a citation of a discrete-valuation lemma.

Step 3 takes from def-pc-field-characteristic exactly the criterion that an integer maps to zero iff the characteristic divides it. Thus the factor m prime to p maps to a nonzero element, meeting the power-root leaf's hypothesis. Step 4 takes from the Artin–Schreier leaf exactly z^p-z=a, verifies z is nonzero and outside V in the negative-value case, and applies proved Step 2 only after establishing the strict inequality of the two values. Characteristic 1 is excluded by 1_K≠0, and primality follows from the absence of zero divisors. Inverting a handles the other sign. Step 5 takes precisely b^m=c from the power-root leaf and multiplies the value equations; its root is nonzero because c is nonzero. Step 6 uses only surjectivity of the quotient map and the definition of divisibility. Every use has a verbatim statement quote in citations.json.

For the Artin–Schreier helper I read Mathlib/FieldTheory/IsSepClosed.lean:95–120 and selected the more direct theorem at line 117. Its hypotheses p divides n, n≥2, and b≠0 hold with n=p and coefficients (1,-1,-a), so its conclusion is exactly the needed root equation. For the other helper I read lines 129–141: the field exponent is explicitly required to be nonzero, exactly as in the node. Both new nodes remain statement-only Mathlib leaves with no proof steps, and their blueprint via lists include the item's full ancestry. The full-DAG and blueprint searches retained in this work found no equal or more general blueprint statement; the report distinguishes the nearby existing nodes above. All recorded new search queries were run through msearch.py and their actual hits were read. The item search metadata was reconciled with the actual retained log rather than retaining unlogged query wording.

Small cases checked: trivial valuation (only zero class), n=1, characteristic zero, both signs of a nonzero value, characteristic 2 (still p≥2), higher-rank ordered groups, and separably closed fields not assumed perfect. The helper also permits a=0, while the item applies it with a nonzero representative. Neither new helper is a clause of the item's divisibility conclusion. All six steps have fewer than 2000 characters, the union of uses is exactly proof_deps, and no definition is used for a theorem it does not state. No SGA source, compiler, Lake command, Lean edit or shared-project write was used.

## Unfinished

The mathematical split and citation audit are complete. The two protected origin metadata corrections above require maintainer action because the authorized delivery tool preserves the old values. The final dry run and push will validate and submit the split-owned repair.
