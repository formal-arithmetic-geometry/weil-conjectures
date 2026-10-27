# Stage-1 delivery: lem-sfb-section-marked-finite-parts-scheme

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-section-marked-finite-parts-scheme.json: complete six-step split, unchanged mathematical statement and statement dependencies; existing searches and ancestry retained, actual Q101 searches appended.
- dag/nodes/sec-six-functors-basics/lem-sfb-unmarked-finite-open-parts-space.json: one new statement-only node, unsplit, no Mathlib match. This is the unmarked algebraic-space functor for an arbitrary separated locally finite type map, without flatness or a section. It does not assert the marked scheme or separatedness.
- citations.json: every cited node at every item step, with its verbatim statement as quote.
- searches.jsonl: actual search-command log, retained unchanged.

One new node; zero Mathlib leaves. No Lean written and no compiler or git command run in the read repository.

## Attachments

None. Searches for the exact blueprint tag, section-marked/finite-parts terminology, finite-part identifiers, 04RI, 04RR and 04QH in lean/WeilConjectures found no declaration giving this item. The unrelated semidirect-product finitePart and finite-partition declarations do not concern the parameter functor. The source library's finite-open-piece lemmas are supporting facts, not proofs of the item.

## WANTED

None. All used source texts are present locally.

## Sources and route

Read GOAL.md, the worker brief, stage-1 rules, delivery-errors B--E in full, the three-level and generic-tool rules of SETUP.md, the item unit and chapter records, and the current blueprint at literature/blueprint/latest (COMMITS.txt points to main-20261023-1620). Read latest sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This supporting scheme construction remains below the already recorded alteration/groupoid-bootstrap prerequisite of that direct-image reduction. No chapter or unit route is replaced.

The item proof follows spaces-more-groupoids.tex, Tags 04RI (lemma-finite-separated-flat-locally-finite-presentation), 04RR (lemma-finite-plus-section), 04PH (lemma-finite-separated) and the finite-fibre-part paragraph of 04RW (lemma-quasi-splitting). I read the preceding definition equation-finite, Tag 04QH (proposition-finite-algebraic-space), and the equality-locus proof lemma-finite-diagonal. The one new node is exactly the unmarked algebraic-space input of 04QH, specialized to scheme source and target, with chartwise etaleness stated explicitly. The atlas-size clause uses the same universe convention as the item. I did not use an SGA source.

For the rational point, I also read more-morphisms.tex Tag 02LK (lemma-etale-makes-quasi-finite-finite-at-point). This supplies a finite open near a point over an elementary etale neighbourhood; pulling that open back to the residue field constructs the finite open of the fibre needed in 04RW. This avoids adding a second node merely restating the rational-point clause of the item.

## Searches

Before creating the new node I searched the whole DAG for 04QH, 04PH, 04RI, 04RR, finite-open and finite-part terminology; read the existing section-marked, universal-finite-parts-groupoid and scheme-groupoid-universal-finite-part nodes; and ran tools/blueprint_refs.py search for finite open, finite part, finite-algebraic-space, finite subschemes and 04QH. None of the blueprint hits states the new input. The ancestor command returns blueprint.from.node = None, as it already does for the live item; the complete existing place and via ancestry are retained and extended rather than inventing a blueprint ancestor.

All Mathlib searches used the required msearch.py command. The item has leanfinder, leansearch, loogle and grep searches. The new node has leansearch, loogle, grep, and two distinct leanfinder phrasings (finite open subschemes and finite clopen subspaces without flatness). The exact queries and returned summaries are copied from searches.jsonl. All services answered. No unavailable service is called no-match. Hits were scheme Etale infrastructure, finiteness definitions, unrelated sheaf-module finiteness, topology, and LocalRepresentability. I read Mathlib/AlgebraicGeometry/Sites/Representability.lean:18--29,51--57: it requires a locally surjective family of already representable open charts, which does not construct our functor. Morphisms/Etale.lean:41--44,69--75 defines the scheme morphism property and its permanence, not this algebraic-space parameter object. No hit is an exact match or a one-line specialization.

## Not duplicates

lem-sfb-unmarked-finite-open-parts-space vs lem-sfb-section-marked-finite-parts-scheme: the former concerns all finite opens of any separated locally finite type map and only gives an algebraic space with chartwise etaleness. The item imposes a section and flat local finite presentation and proves a separated representing scheme, universal closedness and a rational-point clause. The item carries the marked-locus and separatedness arguments explicitly.

lem-sfb-unmarked-finite-open-parts-space vs lem-sfb-scheme-groupoid-universal-finite-part: the existing node assumes a groupoid and flat lfp projections and constructs a groupoid on a marked scheme; the new node requires neither groupoid nor section nor flatness and constructs only the unmarked algebraic space. The existing node cannot be applied to an arbitrary map f with a section, and is not cited to introduce a cycle.

lem-sfb-unmarked-finite-open-parts-space vs lem-sfb-universal-finite-parts-groupoid: the existing node assumes scheme representability and etaleness of the marked functor as hypotheses and constructs its operations. It does not prove representability, even for an arbitrary groupoid, and cannot supply the input used here.

## What was wrong and what changed

The item was an unsplit statement-only prerequisite, not a completed proof. Its mathematical statement is correct, and is preserved. The source has a harmless T/T-prime typo in the equality-locus proof of 04RI: the test base throughout this delivery is T. No source assertion is weakened. I expanded the omitted inverse-image proof of 04RR directly, rather than citing a definition as a theorem or creating a new marked-representability node. The rational-point clause is proved from a genuine finite fibre piece and the two residue-field maps; a k-valued point is not simply declared to have residue field k.

The new node retains no proof or proof dependencies and is self-contained: it introduces S, X, Y, f, the functor, all its test pairs and restrictions, the chartwise meaning of etale, and the universe bound. Every geometric notion has its definition node. It is a genuinely broader unmarked input under weaker hypotheses, not the item relabelled as a child.

## Review by Q101

I read every statement cited by every step and compared the exact clause taken from it; citations.json contains those statements verbatim. The key hypothesis checks and actual arguments are as follows.

Step 1 uses the affine polynomial-quotient meaning of local finite presentation to get local finite type and then the new 04QH input. The input only gives an algebraic space and chartwise etaleness; I do not evaluate a universal pair on a hypothetical scheme before proving schemehood.

Step 2 uses only clause (1) of separated-lqf-base-change, so it does not require f to be locally quasi-finite everywhere. Finite-closed-map-finite-fibres gives properness of Z over T, and lemma-nagata-proper-to-separated-target has exactly the proper-composite and separated-target hypotheses for Z -> X_T -> T. Its closed image makes the already open subscheme closed. This is a two-line application of cited statements, kept elementary and not made into a node. I read the graph proof at morphisms.tex Tag 01W6(2) as well as 04PH.

Step 3 uses finite closedness for the images of the two closed differences; flat-morphism-base-change and the unchanged local rings on an open give flatness; qcqs-morphism-permanence clause (3) gives the lfp base change. Local finite presentation restricts to an open, as checked on affine principal localizations. The exact flat-lfp-open statement then makes those images open. Base-change-image, which I read, states the equality of images after arbitrary base change even for a subset, so this step is not assuming that points of a fibre product are simply pairs. The complement V represents equality on every scheme test. Its inclusion is closed, which is exactly the relative separatedness hypothesis required by the chartwise-etale-space-scheme node. That node requires no quasi-compactness; none is available or assumed here.

Step 4 expands the hint of 04RR: M is the inverse image of C along the actual section of X_E. The universal property of an open restriction proves the bijection with marked pairs and its naturality. The diagonal of the restricted map is the pullback of the already closed diagonal, and the cited closed-immersion-base-change node states precisely its permanence. Open-immersion-base-change, finite-morphism-permanence(a), and etale-composition-cancellation(1),(2) give the universal open, finite projection and etaleness. Closedness here is the closedness proved in step 2, not an unsupported assertion about arbitrary finite opens without separatedness.

Step 5 uses quasi-finite-at-point-isolated with the local finite type from step 1. The precise statement of the elementary-etale finite-at-point node gives U,u,V and both residue-field isomorphisms; pulling V back along Spec(kappa(u)) gives a finite open containing the section point of X_y. Finiteness and openness survive this pullback by the cited permanence nodes. The unique fibre point over sigma(y) is part of quasi-finite-at-point-isolated's statement. Thus the section factors through that open and produces a kappa(y)-valued point of M over the canonical point of Y. I checked morphism-from-spec-field and residue-field-point-naturality: they give the maps k -> kappa(m) -> k and their composite 1. The injectivity argument written in the step proves these maps inverse, with no assumption that k is algebraically closed.

Step 6 uses the atlas-size clause of the new input and the universe convention. Gluing that set of charts and taking open subschemes and fibre products preserve membership of a Grothendieck universe. It does not assert smallness merely because E is a sheaf on a small skeleton.

I checked empty bases and tests; the identity f, where only the full finite part can contain the section; a finite flat lfp map, where finite parts correspond to clopen subfamilies; and a positive-dimensional connected affine-line fibre, where there is no finite open containing its zero section and the rational-point hypothesis is absent. The rational-point argument also allows nilpotents: it uses the induced finite open scheme structure, not the reduced point. Dropping flatness would invalidate openness of the differences' images and may give a nonschematic finite-part space (the source's real/complex example); that hypothesis is retained precisely where used.

B1--B10: statement-only child, complete hypotheses, real notion references, normal TeX, source tags with labels, actual search records, no spurious Mathlib leaf, complete blueprint fields and no Lean attachment. C1--C8: all non-elementary inputs are cited statements; elementary inverse-image and proper-inclusion arguments are written; no proof of a cited node is mined; all hypotheses above are checked; the groupoid nodes are not cited cyclically; generic tools outside the unit are declared in split_report.tool_uses for the maintainer's route review. D1--D5: the item carries separatedness, marked representability and the point construction; the child is the independent unmarked algebraic-space theorem; omitted source hints are expanded. E1--E7: no added noetherian, qcqs, globally quasi-finite or algebraically closed hypotheses; no altered fibre products; all base changes and residue maps displayed. Every step is below 2000 characters, with no long-step lemma hidden inline.

## Unfinished work

The new unmarked finite-open-part algebraic-space theorem is deliberately unsplit and joins the queue. The item split itself is complete. Server dry-run results and delivery commit are reported by the delivery command.
