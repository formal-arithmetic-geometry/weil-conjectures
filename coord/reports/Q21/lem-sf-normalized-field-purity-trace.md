# Stage-1 report: lem-sf-normalized-field-purity-trace

## Files written

- dag/nodes/sec-six-functors/lem-sf-normalized-field-purity-trace.json: statement, split; no Mathlib match for the full coefficient-stage assertion.
- citations.json: exact statement excerpts for all 15 step/node citation pairs.
- report.md: this report.

There are 0 new nodes and 0 Mathlib leaves. searches.jsonl records the searches executed for this item. write_split.py is sandbox-only preparation material.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and id, normalized field purity, purity/scalar and trace/purity language. Smooth/Trace.lean defines the finite-coefficient composite and proves formal properties for a supplied purity isomorphism. Smooth/Adic.lean and Smooth/Rational.lean explicitly prove only packaging statements for supplied normalized systems and compatibility hypotheses. I read their declarations and explanatory docstrings: none states the simultaneous natural field family, its actual operation identifications and all three coefficient equations of this item. They are not attachments.

## WANTED

None. This is an agent assembly of the existing source-backed DAG interfaces, not a claim that a new external theorem proves all the displayed coefficient equations.

## Audit of the imported item

The item was unsplit, with no proof. Its statement is unchanged. In particular, the argument remains about specified lattice presentations in the raw rational category and the common-stage category; it asserts no functor from a coefficient field to a torsion quotient. No new node restates a clause. The nearest blueprint ancestor is prop-functor-package through lem-sf-package-normalized-orientation-perfect-duality. I read the current package statement and proof, especially clause (6) and the final exceptional-adjunction identification paragraph. The chapter and unit records were read and retained; this auxiliary node is not the unit key node.

I searched the whole blueprint with blueprint_refs.py for purity, rationalization.*purity, normalized field and scalar-naturality, and searched dag/nodes and the project Lean source by the corresponding concepts. The relevant precise interfaces already exist: the lattice-domain lemma, rational scalar-comparison identification, common-stage smooth-operation identification and rational compact-support coefficient coherence. The broad rational purity/trace coherence proposition was also read; its statement does not spell out the coefficient equations needed here, so it is not substituted for the argument.

## Mathlib searches

The pre-existing item searches were preserved. For this item I executed the required logged leanfinder, loogle, grep and leansearch searches, then a second leanfinder phrasing about descending the natural isomorphism. All services answered. The first semantic results concern scheme normalization; the second concern ordinary module pullback pseudofunctors and sheaf-module conjugacy. LeanSearch returns ordinary module change-of-rings counits, smooth algebras and smooth sections. Loogle returns comma-category counit formulas. None states smooth purity on completed integral, rational and common finite-field coefficient categories; the category-theory grep has no purity or smooth-trace hit. These are not one-line specializations of the item, whose geometric purity and normalization data remain essential. The exact queries and returned summaries are appended to mathlib_searches and retained in searches.jsonl.

## Unfinished work

No part of this one-level split remains unwritten. Existing dependencies remain independent DAG items; their proofs are not imported as assertions beyond their statements.

## Not duplicates

No new node was created. Existing stronger or more general tools are cited directly.

## Review by Q21

I read coord/delivery-errors.md sections B through E in full, the standing stage-1 brief, the three blueprint levels in SETUP.md, GOAL.md, the worker/stage-1 rules, and the chapter/unit records. For the item I read the current prop-functor-package statement/proof, thm-pur-rational-and-qbar-purity proof Steps 1 and 2, the rational-transport and common-stage descent proofs, and the rational-operation identification proof. These are the sources named on the steps. No new-node source needs checking, since there are no new nodes. The proof_origin is agent: these sources supply the route and the existing nodes supply the precise interfaces, while the trace and inverse calculations are written here.

Step 1 uses lem-pur-rational-lattice-adic-domain for exactly its conclusion that every integral representative belongs to the uniform finite-Tor category. The assumptions hold because X and Y are separated finite-type schemes over the specified algebraically closed field and ell differs from its characteristic. I checked the statement of lem-pur-adic-purity-scalar-naturality: it supplies a simultaneous natural family on precisely that domain, not arbitrary unrelated lifts. Its finite-reduction normalization and the presentation clause of thm-pur-rational-and-qbar-purity select the component used here. This closes the otherwise missing integral finite-Tor domain check.

Step 2 reads prop-weil-pbc-rational-transport only as transport of supplied exact linear functors and transformations. It is not used to assert preservation of constructibility for arbitrary operations. The rational scalar-comparison identification expressly identifies H,G, their map actions and the counit-preserving exceptional mate; its symbol eta names the forward purity map, whereas this item uses gamma for that direction. The compact-support definition specifies the localized functor. lem-coef-rational-operations expressly preserves units and counits under rationalization and finite scalar extension. The integral scalar-naturality statement defines b as the adjoint transpose of c inverse followed by the transported counit, so the displayed counit identity is justified by that statement, not by its proof or by a definition that merely names adjoints. The scalar square is checked for actual maps, not just isomorphic source and target objects.

Steps 3 and 4 cite no further facts: they are elementary cancellation, functoriality and naturality calculations from Step 2. I checked both types in the inverse equation: both arrows run from C_X G L to H' C_Y L. In the trace calculation, c is evaluated first at H L, while naturality at gamma changes it to the component at G L; P'(a_L) therefore has the correct source. This correct typing is why the counit formula uses c at G L. The displayed calculation gives exactly the requested right-to-left composition order.

Step 5 uses only the identity/composite assertions in the rational scalar-comparison identification and the compact-support part of lem-cbc-rational-compact-support-coefficient-coherence. I read that entire statement: it gives a cocycle for the actual compact-support comparison, for an arbitrary Cartesian square, without asserting invertibility of the exchange. Specializing to the identity square of f supplies the needed c cocycle. X,Y and their repeats in that square are noetherian, finite-dimensional and have ell invertible by Step 1; f is separated of finite type and the operation datum uses a compactification. Thus no finite-level reduction-only theorem is misapplied to a field extension. The substitution argument explicitly accounts for naturality and the a,c cocycles when composing trace equations.

Step 6 uses the full statement of prop-weil-pbc-descent-functors, including its representative formula and descent of compatible transformations and equations. The common-stage smooth-operation identification expressly includes the map actions of H and G and component representatives, so it closes the possible gap between an abstract descended functor and the actual operation datum. For P the representative formula is written out and its object prescription is the compact-support definition. The counits are the finite-stage actual counits identified in Step 2; compatibility makes their Hom-adjunction bijections well-defined on the filtered-colimit Hom groups, and their inverse bijections descend too. Thus the operation datum's exceptional counit, rather than a newly chosen trace normalization, is the one in the final composite.

Step 7 uses the actual common-stage coefficient definition: arrows are represented over finite coefficient fields and equality means eventual equality. I read its full statement, including composition over a common overfield. There are only finitely many arrows in each displayed equation and comparison diagram, so one finite compositum suffices; equivalent representatives agree at a further stage. The conclusion does not incorrectly assert that a transition functor is faithful or that equality at an arbitrary initially chosen stage is necessary.

Small cases checked: L=0 makes all equations zero; identity coefficient extension gives identity comparisons; r=0 removes twist and shift without changing any argument; a torsion integral representative becomes the zero rational object and all rationalized components are the unique maps there; empty schemes have the same zero-object conclusion. Nontrivial ramification is covered by the specified scalar comparison interfaces, never by a claimed reduction from E to A_n. These cases introduce no extra hypothesis.

For B, all fields and source metadata are retained, there are no statement-only nodes with hidden proofs, and the searches are actual logged calls. For C, every non-elementary input is a cited statement, every cited statement was opened, the proof-dependency list is exactly the union of uses, and the local dependency traversal found no path back from any cited node to this item. For D, the inverse and trace clauses carry their actual arguments instead of being moved into new nodes. For E, I checked the coefficient domains, smooth/separated/finite-type assumptions, both comparison directions and all trace component types above. Every step is below 2000 characters; the common-stage paragraph is one representative calculation using the cited descent theorem, not an unnamed comparison theorem. Off-unit generic tools are declared in split_report.tool_uses with their purpose; the package unit's purity-transport route is retained. The citations.json entries are exact substrings of the cited statements and were checked locally before the server dry run.
