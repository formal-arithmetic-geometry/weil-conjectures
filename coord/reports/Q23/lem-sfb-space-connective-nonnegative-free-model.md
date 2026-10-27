# Q23 stage-1 report: lem-sfb-space-connective-nonnegative-free-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-connective-nonnegative-free-model.json: statement, split; existing statement and statement dependencies retained; seven proof steps, using existing nodes only. Not a Mathlib leaf.
- citations.json: verbatim statement excerpts for every node cited by every step, with additional excerpts for the cohomology and composition clauses.
- searches.jsonl: actual searches executed through the prescribed msearch command. prepare.py is a sandbox-only artifact generator, not part of the delivery.

There are zero new nodes and zero new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and for connective/perfect and nonnegative/free terminology, and inspected the relevant algebraic-geometry matches. No project declaration states this complete algebraic-space assertion. The live item has no finished Lean attachment.

## WANTED

None. All proof sources used are available in literature/stacks-project. No SGA source is used.

## Problems found and changes

The unsplit item already states the needed perfect-complex specialization correctly. I retained its statement and every statement dependency. The quoted Stacks proof begins from pseudo-coherence and first proves perfectness; that preliminary argument is unnecessary because this item already assumes perfectness. I kept the final cokernel argument, rather than citing the whole 08JX representability result (which would also be circular through the parent).

The conversion from scheme-algebra tests to arbitrary module tests is not automatic. I supplied its elementary square-zero algebra argument explicitly: D=A direct-sum N as an A-module, with multiplication (a,n)(a',n')=(aa',an'+a'n), makes the ordinary tensor complex split into M and M tensor N. Thus universal vanishing for affine scheme tests implies the degree-minus-one module-tensor hypothesis of the existing flat-opcycle lemma.

I searched the whole DAG by 08JX, the last-one-flat and finite-projective labels, cokernel/flatness, affine perfect models and topology comparisons, and ran blueprint_refs searches for perfect complexes, opcycles, and finite projectives. Those searches found the needed existing nodes; none of these facts is made into a new node. The original blueprint.from.node is null in the live node and blueprint_refs ancestor also returns None. I preserved that inherited ancestry and its complete from.place and via chain; same_as stays empty. I read the current latest blueprint direct-image proof and the chapter and unit records: this remains the existing supporting algebraic-space Hom branch of the direct-image route, with no chapter/unit edit.

## Not duplicates

No new nodes were created. Existing generic tools are reused: the flat opcycle assertion is lem-pc-module-flat-opcycles-tor-criterion; projectivity and principal trivialization are lem-weil-pbc-finitely-presented-flat-module-projective and lem-weil-pbc-finite-projective-standard-free-cover. The affine/topology comparisons are likewise cited rather than copied or restated as new nodes.

## Mathlib searches

I ran the five queries recorded on the item through msearch for Q23: LeanFinder on universal connectivity and on Tor-amplitude truncation, Loogle on CochainComplex/Projective, grep on perfect/connective/nonnegative and Tor amplitude, and LeanSearch on universally nonnegative base changes of finite projective complexes. All services returned results. I read the returned signatures. I also read TStructure.lean:175-186 for DerivedCategory.exists_iso_Q_obj_of_isGE and exists_iso_Q_obj_of_isGE_of_isLE: those give arbitrary complexes with restricted support, with no finite free terms or algebraic-space/geometric pullback clause. K-projectivity results likewise do not give that finiteness. There is no exact match or one-line specialization. The second LeanFinder phrasing specifically checked truncation of perfect complexes, not only the original geometric wording.

## Review by Q23

I read coord/delivery-errors.md B through E whole, including the repeated version, and checked the actual statements of every cited node against each use. My source for the item is quot.tex, Tag 08JX, label lemma-cohomology-perfect-complex: the affine reduction and final paragraphs explicitly replace the degree-zero term by a flat cokernel, use 00NX for finite local freeness, and trivialize on affine opens. I also read more-algebra.tex Tag 0653, lemma-last-one-flat, including its universal tensor exactness argument; algebra.tex Tag 00NX, lemma-finite-projective, including the list of equivalences and local freeness proof; and spaces-perfect.tex Tags 08H8 and 071Q for exact faithful topology change and its derived equivalence. No new-node sources require checking because there are no new nodes.

For step 1 I read the algebraic-space definition, local strict-perfect package, affine-open basis, etale composition statement, universe convention and derived chart calculus. These give the atlas, affine refinements, termwise split representatives, small family, and the exact restriction/composite-pullback comparisons actually used. The etale composition lemma is a scheme statement; the proof explicitly applies it to each scheme base change of the representable chart. The bound belongs to each chart individually, so no quasi-compactness assumption on B enters.

For step 2 the strict-perfect package supplies the degreewise idempotents, not a chain splitting. I wrote the differential as i_(j+1) d p_j and checked its square using p_j i_j=1; no chain splitting is asserted. The affine etale realization says it is exact and gives the associated sheaf, so split images are indeed the original terms. Each module is a direct summand of a finite free module, exactly the hypothesis of the principal free-cover lemma. There are only finitely many terms to trivialize simultaneously. I added the existing affine derived equivalence explicitly to ensure that the Zariski complex has quasi-coherent cohomology before invoking the topology comparison; this avoids an implicit domain assumption.

For step 3 I checked the precise pullback and composition clauses of the chart and topology-equivalence statements. The comparison holds for every scheme morphism, with no qcqs hypothesis on pullback (qcqs is only in the pushforward clause and is not used). The bounded finite free Zariski model satisfies the flat-complex pullback lemma. The affine pullback-sections statement includes naturality, so its termwise isomorphism respects the differential. The affine etale realization is exact and faithful and identifies cohomology, which is precisely the input that detects vanishing of the ordinary D-module tensor complex. This is not an assertion that all etale sections of a general sheaf preserve exactness.

Step 4 uses only explicit ring and direct-sum formulas and the preceding vanishing. I checked the square-zero multiplication, the A-algebra inclusion, block-diagonal differentials, and kernel/image decomposition; arbitrary N need not be finite or flat. The universal hypothesis allows this scheme test. Step 5 applies the module flat-opcycle criterion at a=0; all terms are flat and every module tensor has vanishing degree -1 cohomology, exactly its stated hypotheses. The zero-degree cokernel has a two-term finite free presentation, so the finite-presentation-plus-flatness lemma applies without a Noetherian assumption.

For step 6 I checked the canonical quotient map and the explicit H^0 computation; the unchanged positive cohomology and vanishing negative cohomology prove a quasi-isomorphism, not a degreewise claim about the terms. Exact affine realization preserves it, and the derived-category localization inverts it. Step 7 again uses the existing principal free-cover lemma, now for the finite projective cokernel, and the exact restriction/composition clauses of chart calculus. Choosing actual bases converts isomorphic free terms to the displayed standard free terms and gives matrices. The derived isomorphism persists under those chain isomorphisms and etale restriction.

I tested the empty space, the zero ring and zero complex, zero ranks, complexes supported only in negative degrees (then the truncated object is acyclic), a two-term identity map crossing degree zero, and a single positive-degree free module. I also checked why mere connectivity is insufficient: over Z the complex Z --2--> Z in degrees -1,0 is connective but its tensor with Z/2 has negative cohomology, so it fails the universal hypothesis; the proof does not wrongly conclude its cokernel flat. All seven steps are below 2000 characters and none hides a source-standard auxiliary lemma. The elementary steps are only the square-zero direct-sum calculation and the explicit truncation/quasi-isomorphism calculation. All invoked non-elementary tools are cited nodes, with off-unit generic tool uses declared in split_report. No cyclic dependency or new-node relabeling is intended.

## Unfinished

Nothing mathematical remains for this one-level split. Server dry-run and delivery results are recorded by the delivery tool; no Lean files were written and no compiler or Lake command was run.
