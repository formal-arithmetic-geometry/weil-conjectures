## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-type-surjective-product-pullback.json — item split, statement and statement dependencies unchanged.
- citations.json — one verbatim statement quotation per step citation.
- searches.jsonl — actual searches logged by the mandated msearch.py commands.
- report.md — this report and direct-delivery self-review.

Attachments: none. Searched WeilConjectures/ for the exact blueprint id and for finite-type ring pullback/fibre-product terminology. The project hits concern geometric base change, tensor pullbacks, or unrelated finite-type assertions; no declaration states the item exactly. There is no lean_audit or Lean declaration in the imported item.

WANTED: none.

The initial node had a correct statement but no proof. Stacks more-algebra.tex Tag 08NI, lemma-formal-consequence (lines 365–394), states precisely the product pullback claim, and reduces it by induction to Tag 00IT, lemma-fibre-product-finite-type (lines 327–362). I retained that induction and expanded the two-surjective-maps case of 00IT using its Artin–Tate argument. The crucial point is that coordinatewise surjectivity does not imply surjectivity onto the product: for Q=D_1=D_2=k and identity maps, Q maps diagonally into k×k. The proof never assumes that stronger assertion.

Nothing unfinished. No statement dispute, source error, or route change. No Lean files or compiler/build tools were used. All writes are in the item sandbox.

## New nodes

None; zero new nodes and zero new Mathlib leaves. The non-elementary finiteness input already exists as lem-sfb-artin-tate-subalgebra-finite-type, in the same unit, with status mathlib and the exact statement needed. Its Mathlib declaration is fg_of_fg_of_fg, Mathlib/RingTheory/Adjoin/Tower.lean:145–154. The definitions of finite type and finite generation are existing nodes too. The finite-generation calculations are written explicitly in the proof rather than made into elementary nodes.

## Searches and blueprint

Read the original item's five recorded Mathlib searches before extending them. Ran msearch.py with LeanFinder, Loogle, grep and LeanSearch, then a second LeanFinder phrasing about subdirect products and Artin–Tate. All services answered; no unavailable search is disguised as a negative result. Read the actual hit lists. The first LeanFinder query returns Algebra.FiniteType.prod, quotient lemmas and finite-presentation products, not the pullback claim. The second returns fg_of_fg_of_fg, Algebra.fg_trans', product finite type and related results; fg_of_fg_of_fg is the cited input, not a one-line proof of the whole item. Loogle has no pullback hit. The source grep returns scheme pullback finite-type results, whose affine meaning is a tensor product rather than this ring pullback. LeanSearch returns definitions, quotient finiteness and Noetherianity. Read the Artin–Tate theorem's complete source at Tower.lean:139–154 to verify its injectivity and scalar-tower requirements.

Searched the whole DAG by 08NI, 00IT, lemma-formal-consequence, lemma-fibre-product-finite-type, finite-type product terminology, and coordinatewise/subdirect-product terminology. Tag hits are this item, ancestors, and scheme-pinching results, not an alternative existing statement of this algebraic assertion. Used blueprint_refs.py search for 'fibre product', 'Artin Tate', 'finite type product', 'finite type pullback', '08NI' and '00IT'; none gives a duplicate imported blueprint statement. Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json, and the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images statement/proof. This is a subordinate algebra lemma on the existing ancestry of direct-images proof (3); no chapter or unit route is changed. blueprint_refs.py ancestor returns None; retained that value and the recorded via chain, and filled split_report.blueprint with the precise source steps implemented. The latest blueprint has renamed the direct-images file, but its id remains det-thm-sf-ctf-stability-direct-images, as recorded in from.place. No new node needs a blueprint ancestry field.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by NC

I read Stacks more-algebra.tex lemma-formal-consequence (08NI) and lemma-fibre-product-finite-type (00IT), and algebra.tex lemma-Artin-Tate (00IS, lines 12297–12328), with the item and each cited node open. The item's R is commutative Noetherian, its index is finite, all algebras are finite type and both coordinate maps are surjective: these are exactly the 08NI hypotheses after renaming A_i to C_i and B_i to D_i. No statement correction was needed. There are no new statements to compare with sources.

Step 1 uses def-weil-pbc-finite-type-algebra's polynomial-generator formulation. The empty product has its unique element and T_empty is explicitly Q; finite generators transfer under the displayed inverse maps. The projection T_J→Q is surjective by choosing one lift for each of finitely many j using phi_j, so it does not require any simultaneous lifting along psi. This is a direct calculation from the equations defining T_J.

Step 2 sets up cardinality induction for all data, not just a fixed diagram, so the restricted J diagram meets exactly the induction hypothesis. Its map alpha is psi_i composed with the surjective projection just proved. The displayed coordinate rearrangement and its inverse preserve equations, operations and the R-action. This is a direct check of the subsets, with no appeal to an unstated fibre-product comparison theorem. No node citation is needed for the induction hypothesis or for this rearrangement.

Step 3 again uses precisely the polynomial-generator clause of def-weil-pbc-finite-type-algebra. Both idempotents are included in the generators. Evaluating f and g with the diagonal scalar map and multiplying by the corresponding idempotent projects out the unwanted constant terms, so the displayed expression produces every pair. This establishes product finite type explicitly and does not hide a product-finiteness lemma.

Step 4 uses the actual finite-span definition in def-weil-finitely-generated-module, whose statement I opened. Each projection of P is surjective for the indicated, separate lifting reason. Multiplication by (1,0) and (0,1) here is the action on the ambient product B; these two elements are not asserted to belong to P. The displayed identity gives a two-element P-module generating set for all of B. This is an elementary two-term span calculation, rather than an uncited exact-sequence or module-finiteness theorem.

Step 5 uses the full statement of lem-sfb-artin-tate-subalgebra-finite-type, not its proof. I opened that node: it says a subalgebra of a finite type algebra over a Noetherian ring is finite type when the ambient algebra is finite as a module over it. The base is still the original R, the ambient algebra is B, and P is literally an R-subalgebra of B with its injective inclusion. Steps 3 and 4 verify the two finiteness hypotheses. Componentwise scalar operations give the canonical scalar tower required by its Mathlib realization. Its conclusion therefore applies exactly. Polynomial expressions then transfer along the explicit Step 2 maps, completing the induction. This is the only non-elementary step and its citation is recorded verbatim in citations.json.

I checked B1–B10: no new unsupported statement or definition, no bare-tag meaning, exact TeX escaping, actual logged searches, and no missed project attachment. C1–C8: every non-elementary inference is the Artin–Tate citation; all three cited nodes' statements were read and copied exactly for the portions used; no proof internals, missing hypotheses, cycle, or off-unit non-leaf tool is used. D1–D5: the argument stays in the item and no clause is moved into a new node. E1–E7: source induction and map directions agree, and all identifications and generator formulas are written explicitly. Every step is under 500 characters; there is no step exceeding 2000 characters and no hidden lemma behind a long paragraph.

Small-case checks: I empty yields Q and the stipulated one-element empty product; a singleton is the two-surjection case; two identity maps Q=C_i=D_i=k give T=k despite the non-surjective diagonal map to the product. With all D_i zero, T is Q×product C_i, and the calculation still works. Zero rings and empty algebra generating sets cause no failure: idempotents may be zero and the finite lists may repeat elements. No nontriviality, domain or field hypothesis is used, and R→B need not be injective (Artin–Tate requires only P→B injective). I corrected no mathematical statement; I supplied the previously missing induction, both lifts, the product algebra generators and the ambient module action explicitly. No second worker is claimed: this is the requested direct-delivery review by NC, for the maintainer's independent review.
