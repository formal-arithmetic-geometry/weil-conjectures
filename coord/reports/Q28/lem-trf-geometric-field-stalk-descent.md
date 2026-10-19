# Q28: lem-trf-geometric-field-stalk-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometric-field-stalk-descent.json: statement, split into eight proof steps; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-local-base-change.json: new statement-only general local-ring lemma, unsplit; no exact Mathlib match.
- citations.json: every citation of every proof step, with its verbatim statement.
- report.md and searches.jsonl: review and actual search log. write_split.py is the sandbox-local data-writing script.

## Attachments

None. The item has no recorded Lean audit or declaration. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag and for geometric field/stalk terminology found no declaration giving this commutative-algebra statement. In particular geometric stalks of sheaves and unramified local algebra results do not give all its clauses.

## Literature

No WANTED sources. I read varieties.tex, lemma-geometrically-reduced-at-point (035W), lemma-geometrically-reduced-upstairs (0384), and their proofs; algebra.tex, lemma-characterize-separable-field-extensions (030W), lemma-field-finite-type-over-domain (00FY), and lemma-flat-localization (00HT); and curves.tex, lemma-nodal (0C4D), especially the paragraph beginning “Now assume k is an arbitrary field.” The item is the abstract local algebra behind the geometric singular-point descent in that paragraph. The general new lemma expresses 0384 in the local-ring language justified by 035W; its quantification over ALL extension fields is intentional.

## Findings and corrections

The item is mathematically correct; no statement change and no STATEMENT-DISPUTED issue. It previously had no proof. A field stalk upstairs alone is not enough to assert separability without an argument: the missing argument is geometric reducedness at the chosen point, followed by its descent. I supply that argument rather than replacing it with an unproved claim that all geometric stalks are fields. Finiteness, existence of a prime above the closed point, maximality, the structural residue-field identification, and the identification downstairs via its actual residue map are all proved explicitly.

The unit is sk-i-curve-zero and the chapter is sec-trace-formula. This child realizes the recorded ancestry through lem-trf-nodal-point-local-criterion and its geometric nodal-family prerequisites; it is not the unit's key node, so no unit realization file is changed. The unit's reference to SGA 5 is only the chapter contract; no SGA source is used in this split. The generic field-theory separability criterion from sec-picard-framework is declared in split_report.tool_uses. Other cross-unit facts cited are existing Mathlib leaves or definitions.

## Searches

Before creating the new node, I searched the whole DAG by 0384, 035W, geometric reducedness at a point, and flat-local/localization terminology; ran blueprint_refs.py search for “geometrically reduced”, “geometrically-reduced-upstairs”, “geometric reducedness”, and “035W”; and searched the project Lean tree. No existing node gives the local pointwise base-change equivalence. blueprint_refs.py ancestor identifies lem-trf-local-term-locality; the new node inherits that ancestry with this item prepended to via.

All new Mathlib searches used msearch.py and are preserved exactly in searches.jsonl and in the node records. Two semantic phrasings, Loogle and grep were read. Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:62 is a criterion for an entire algebra, and :78 preserves the base field under injection; neither is the local-base-change theorem. The file's TODO explicitly lacks the arbitrary-field-extension criterion. The new node consequently remains unsplit. For the item, the hits in Unramified/Field.lean:111 and Unramified/LocalRing.lean:134 require unramifiedness, which is not among the item's hypotheses. They are not matches. Historical searches on the repository item are retained.

## Not duplicates

lem-trf-geometric-reducedness-local-base-change vs lem-trf-geometric-field-stalk-descent: the new lemma is the general equivalence of geometric reducedness of localized algebras under any field base change, without finite type or field-stalk assumptions; it proves neither finiteness, existence/maximality of the geometric primes, the residue map isomorphism, nor separability asserted by the item. The item derives its conclusion in eight steps with independent existing tools.

lem-trf-geometric-reducedness-local-base-change vs lem-sbc-field-fraction-ring-geometric-integrality: that node transfers geometric integrality between integral affine schemes having isomorphic function fields; the new lemma compares local rings at a specified prime under scalar extension and requires no integrality or fraction-field identification.

lem-trf-geometric-reducedness-local-base-change vs lem-weil-pbc-separable-tensor-purely-inseparable-field: that node says a tensor product of a separable algebraic field extension with a finite purely inseparable extension is a field of specified degree; the new lemma concerns local geometric reducedness of arbitrary algebras and arbitrary field extensions.

lem-trf-geometric-reducedness-local-base-change vs lem-pur-geometric-reducedness-from-generic-stalks: that node deduces global geometric reducedness from all generic stalks of a reduced scheme; the new lemma is the equivalence at one point after field base change, without global reducedness or a generic-point hypothesis.

## Review by Q28

I checked B through E of delivery-errors.md against the sources and the finished JSON. The single new node introduces every object, defines reducedness inline, cites its three notion nodes, has no proof or proof dependencies, records the searches actually run, and has explicit blueprint ancestry. It is a general prerequisite, not one of the item's clauses moved into a child. All other elementary arguments remain proof steps. There are no proof steps over 2000 characters and no hidden identification left under “transport” or “standard.”

For step 1 I read lem-weil-pbc-zariski-lemma: it assumes a FIELD finitely generated as an algebra and concludes finite dimension, exactly the case of the quotient by the maximal ideal. For step 2 I read lem-weil-pbc-field-extension-base-change-faithfully-flat and lem-weil-pbc-faithfully-flat-surjective-spectrum: the former gives this tensor map faithfully flat and the latter gives a prime above every prime; neither is inferred from a definition alone.

For step 3 I read def-weil-pbc-module-tensor-product and lem-weil-pbc-finite-dimensional-domain-is-field. I wrote the bilinear surjection from F tensor Omega, its finite spanning family, and the domain/nonzero checks from primality before applying the latter lemma. Step 4 uses the actual polynomial factorization statement of lem-weil-alg-closed-linear-factorization: the vanishing product in the FIELD quotient forces every element into the structural Omega image. def-weil-pbc-localization-at-prime supplies the residue construction, and the explicit inversion argument identifies it with the maximal quotient. This checks the structural algebra structure, not merely an abstract field isomorphism.

For step 5 I opened the statements of all seven cited nodes: the localization definition, the definition of faithful flatness (including its flatness implication), localization flatness, composition of flat maps, flatness over a localization, flat-local faithful flatness, and faithful-flat ideal contraction/injectivity. Each statement supplies precisely the indicated operation. The map A to B is local because the contracted prime is p; both A and B are local by the localization definition. I did not assume localization preserves faithful flatness: I reestablished it using the flat LOCAL map. In step 6 I wrote the actual residue map t/s to tbar/sbar, its surjectivity and kernel, and used injectivity and locality of step 5 to kill its kernel.

For step 7 I checked the new lemma against both 0384 and 035W: its condition is geometric reducedness of the local ring as an algebra, not merely reducedness of that ring. The hypothesis B = Omega as an Omega-algebra makes B tensor H equal to H for EVERY H/Omega by the explicit multiplication and unit inverse maps; this is the exact hypothesis of the lemma. Its conclusion gives A tensor Omega reduced. Tensoring the residue isomorphism gives F tensor Omega reduced. Step 8 uses the full statement of lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable with finiteness from step 1; I also opened both separability definitions and wrote why the empty transcendence basis converts the general separability notion into the algebraic one for finite extensions.

I tested small and limiting cases. T = k gives the claimed identity. A finite separable extension has geometric factors Omega and passes the conclusion. For k = F_p(u) and T = k[v]/(v^p-u), the geometric tensor is Omega[epsilon]/(epsilon^p): its local ring is not Omega, so the conditional does not falsely imply separability. T = k[epsilon]/(epsilon^2) likewise fails the field-stalk hypothesis, while retaining a maximal geometric prime with residue Omega. T = k[x], p = (x), has a geometric local ring Omega[x]_(x), also not a field; finite type alone is not being used to force zero dimension of T_p. The general new lemma allows R nonreduced, arbitrary primes and nonalgebraic scalar extensions; 0384 has exactly that generality. With L = k it reduces to an identity. With R = 0 there are no primes q and the assertion is vacuous. The faithful-flat citations have no Noetherian requirement, so no such hypothesis was smuggled in.

I checked that every cited step node exists and that its statement contains the citation quote verbatim. The server dry run passed preflight, including its DAG and split checks. I then corrected the source label of 00HQ to lemma-ff-rings, named 00HR and 05CK explicitly in step 5, and clarified that a finite basis generates F as a field; the final dry run checks that corrected version again. Nothing remains mathematically unfinished in the item's split; the one new lemma is intentionally statement-only for later splitting.
