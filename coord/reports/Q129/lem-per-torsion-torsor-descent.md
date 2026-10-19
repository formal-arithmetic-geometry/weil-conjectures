## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-torsion-torsor-descent.json`: split statement with five proof steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-torsion-finite-subsystem.json`: new unsplit statement, no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-set-local-system-calculus.json`: new unsplit statement, no Mathlib match.
- `citations.json`: verbatim quotations for every node used by each step.

Attachments: none. Searching the project Lean source by item tag and torsion/torsor terminology found no declaration stating the item.

WANTED: none.

The source is Illusie–Laszlo–Orgogozo, Exposé XVII, Definition 7.2.1, Propositions 7.2.2–7.2.4 and Lemma 7.2.6, pp. 301–303 (PDF pp. 307–309). The split retains the Noetherian hypothesis, the free action, the local-system quotient, and elementwise torsion without imposing a uniform exponent. The statement's old Noetherian-ring citation was replaced by locally-Noetherian and quasi-compact scheme definitions, and the existing ind-finite local-system definition was cited. These are citation repairs; the mathematical statement is unchanged.

The saved report described a discarded finite-stage node. That node is absent from the final delivery: Step 3 now proves finite-stage torsor descent directly from the existing cohomology continuity, torsor classification and coefficient-functoriality nodes. The two actual new statements supply the set-valued local-system calculus and the finite subgroup exhaustion. Neither states the torsor conclusion of the item. No work remains unfinished within this one-level split; the new nodes intentionally remain statement-only.

## Review by Q129

I reopened ILO XVII pp. 301–303 and the final node files. Lemma 7.2.6 says exactly that a free action by a torsion abelian local system with local-system quotient has local-system total space. Its proof explicitly uses finite quotient subsystems, the total-space functor for a finite etale map, H¹ continuity, and extension of structure group. The new set-calculus statement isolates the earlier set-valued facts of 7.2.2–7.2.4 and the slice/total-space identification explicitly used in 7.2.6. The new finite-subsystem statement isolates the finite subgroup exhaustion used on p. 303; it asserts both the underlying-set and abelian-sheaf colimits, so Step 3 does not confuse these categories. Its torsion assumption is elementwise, with no common exponent.

Step 1 uses `lem-per-set-local-system-calculus` for the filtered union of finite quotient subsheaves and closure under ambient colimits. The inverse images have the asserted free action and quotient by local lifting along the quotient map; the union and empty-quotient case are spelled out. This is a short elementary reduction from the cited theorem.

Step 2 uses the same calculus node for finite representability, the slice equivalence, transport of group actions, pullback preservation, and the total-space conclusion. I checked its statement actually includes each of these clauses. `def-weil-finite-integral-morphism` defines finite by finite affine algebras, and `def-weil-finite-type-morphism` supplies the finite-type condition: a finite module generating list also generates as an algebra. `lem-weil-pbc-finite-type-over-noetherian` then makes Y Noetherian, as the calculus node requires. `def-sc-gm-torsor` explicitly includes general abelian G-torsors. Terminal quotient gives local sections and freeness gives unique local differences, hence the torsor condition. The pointed-neighbourhood definition in `def-weil-pbc-geometric-stalks` verifies that restriction along an etale map preserves the relevant stalks and therefore elementwise torsion.

Step 3 uses `lem-per-torsion-finite-subsystem` for a small filtered system of finite subgroup sheaves and its abelian-sheaf colimit. Noetherianity supplies quasi-compactness, and `lem-weil-pbc-locally-noetherian-quasi-separated` supplies quasi-separatedness, exactly the hypotheses in `lem-weil-pbc-cohomology-filtered-colimit`. Its statement allows all abelian etale sheaves and degree one, without requiring a uniform torsion bound. `lem-sc-torsor-h1` gives both existence of a torsor representing a stage class and injectivity on isomorphism classes. Clause (2) of `lem-sc-etale-torsor-h1-functoriality` identifies the image class with extension of structure group; `lem-sc-etale-contracted-product-exists` supplies the resulting torsor. Thus the isomorphism with T follows from these statements, rather than a new node repeating this part of the proof.

Step 4 uses the contracted-product existence statement to obtain an H-torsor. The general torsor definition makes it locally isomorphic to H. Refining by a finite-constant trivialization of H proves finite local constancy in a few lines. Clause (2) of `lem-galois-flc-representable` then gives precisely finite etale representability; no stronger finite torsor theorem is presumed.

Step 5 uses the filtered-poset and set-colimit clauses of the finite-subsystem statement and the universal property against all set sheaves in the contracted-product statement. Cofinality of subgroups containing G′ follows by choosing a common upper bound. Compatible invariant maps on T′ × H glue locally and uniquely on T′ × G, with independence checked at a common upper bound; the same universal property identifies the colimit with the desired contracted product. This elementary argument proves the colimit compatibility explicitly rather than citing an unstated transport theorem. All five steps are below 2000 characters, and no comparison lemma is hidden in a long step.

I checked every cited node's current statement and every entry of `citations.json`; all quotes are verbatim and cover the clauses used. The new files have self-contained statements, definition dependencies, no proof or proof sketch, and complete blueprint provenance. The final split avoids citing the module-monodromy parent, which depends on this item and would create a cycle. Its off-unit black-box uses are explained in `split_report.tool_uses`; they implement the ILO proof rather than replacing the unit route.

I read and reused the saved Mathlib search results in `searches.jsonl`. LeanFinder, Loogle, source grep and LeanSearch were run for both new notions, with alternate phrasings. The finite Galois-category equivalence concerns finite actions; condensed locally constant presheaves concern a different site; ordinary finite-subgroup facts do not assert the etale subgroup-sheaf exhaustion. None supplies either complete new statement. The DAG/blueprint and Lean searches found no duplicate supplying these assertions. Sources are ILO and the existing Stacks-based nodes; no SGA source is cited.

Small cases checked: G = 0 gives T = T/G; the empty quotient forces T empty; a finite constant group reduces to an ordinary finite etale torsor. For the finite-subsystem statement, zero and finite constant groups give terminal finite stages, while an infinite torsion constant group is exhausted by its finitely generated finite subgroups. Disconnected Noetherian schemes have finitely many components, so their finite subsystems combine without requiring a global torsion exponent. The calculus statement includes empty finite covers and empty colimits; its slice statement and total-space conclusion also hold over the empty base. These checks preserve every source hypothesis.

During resumption I corrected the stale report to match the final proof and actual two new nodes. The earlier finite-stage-node description is not part of the delivery. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

- lem-per-set-local-system-calculus vs lem-per-torsion-local-system-monodromy: the new node concerns arbitrary set local systems and finite-etale slice/total-space operations; the parent concerns modules over a ring killed by one integer, and its extension-closure proof depends on the delivered item. Citing that parent here would be circular.
- lem-per-torsion-finite-subsystem vs lem-per-torsion-local-system-monodromy: the new node asserts finite subgroup-sheaf exhaustion for elementwise torsion, without a fixed coefficient ring or uniform exponent; the parent does not state that exhaustion and depends on this item.
- lem-per-set-local-system-calculus vs def-per-ind-finite-etale-local-system: the existing node defines the notion but does not assert ambient colimit closure, finite-subobject exhaustion or the total-space theorem.
- lem-per-torsion-finite-subsystem vs lem-per-set-local-system-calculus: finite subsheaves of a set local system need not be subgroup sheaves. The torsion subgroup-exhaustion assertion includes group closure and both colimits, which the set-calculus statement does not supply.
