# Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-conormal-torsion-algebraization.json`: item split into nine proof steps; Mathlib searches found no matching theorem.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-punctured-idempotent-complement.json`: statement-only supporting node; Mathlib searches found no matching theorem.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-formal-glueing-finite-algebras.json`: statement-only supporting node; Mathlib searches found no matching theorem.
- `citations.json`: 23 verbatim step-to-node citations.

Attachments: none.

WANTED: none.

The imported item statement agrees with More on Algebra, Tag 0ALR, `lemma-quotient-by-idempotent`, including the Noetherian hypothesis, finite type algebra, completion quotient, kernel (J), and the condition that (I^c(J/J^2)=0). I retained the three imported statement dependencies. The source proof's two omitted ingredients are the new complementary-quotient node (Tag 0C2A) and finite-algebra formal gluing node (Tags 05ER and 05EU); neither is a restatement of the item's conclusion.

## Not duplicates

- `lem-per-punctured-idempotent-complement` vs existing idempotent-localization nodes: the new statement glues idempotents that exist separately after every localization at an element of one finitely generated ideal and produces one complementary quotient globally; existing nodes only split a ring at an already global idempotent.
- `lem-per-formal-glueing-finite-algebras` vs `prop-weil-pbc-formal-glueing-equivalence`: the existing proposition concerns modules and the equivalence of module categories; the new statement specializes the algebra-category consequence and asserts compatible finite commutative algebra structures and finite generation.

- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-H0-chart-power-lift`: the existing node lifts individual module chart sections after powers; it does not descend a finite algebra or produce algebra isomorphisms.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-H0-localization`: the existing node identifies the module (H^0) after localization; it does not assert finite algebra descent.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-essential-surjectivity`: the existing node gives essential surjectivity for a pre-existing module functor; it does not state the algebra-category consequence or finite algebra hypotheses.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-extension-transport`: the existing node transports module glueing morphisms; it does not construct a descended finite algebra.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-injective-approximation`: the existing node concerns injective module approximations and torsion cokernels, with no algebra structure.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-isogeny`: the existing node concerns module maps with torsion kernel and cokernel, not descent of an algebra object.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-localized-chart-tuple`: the existing node checks compatibility of one localized module chart tuple; it does not give global algebraization.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-map-from-algebraization`: the existing node algebraizes a module map with torsion kernel and cokernel; it does not descend a finite algebra datum.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-map-to-algebraization`: the existing node algebraizes a module map in the opposite direction; it does not descend a finite algebra datum.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-formal-glueing-morphism-lifting`: the existing node lifts morphisms between canonical module glueing objects; it does not assert existence of a finite descended algebra.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-ideal-power-torsion-localization-criterion`: the existing node detects torsion from localization bijectivity for module maps; it does not perform formal algebra gluing.
- `lem-per-formal-glueing-finite-algebras` vs `lem-weil-pbc-torsion-extension-flat-descent`: the existing node descends module extensions by torsion; it does not produce the finite algebra and compatible algebra isomorphisms in this node.

## Review by Q117

I read the item against More on Algebra, Tag 0ALR, `lemma-quotient-by-idempotent` and its proof at `literature/stacks-project/more-algebra.tex:32037`, and read the cited imported nodes in the live DAG. I also read the source passages for Tags 0C2A, 05ER, 05EU, 07M4, 09XI, 0ALJ, 00EH, 00FN, 0316, 05GG, 00MB and 00MA. The two new statements are self-contained: the first introduces the finitely generated ideal, all localizations and the quotient map; the second introduces the flat map, charts, overlap maps and finite algebra hypotheses. I searched the whole DAG and blueprint for these statements and for their tags before creating them.

Step 1 uses the finite-type-to-Noetherian node, completion-Noetherian node, completion modulo the ideal node, and the Noetherian definition. Those statements provide exactly the Noetherianity, completeness, and finite-generation facts used. Step 2 uses the existing finitely-generated idempotent-ideal node; its two clauses give both the idempotent generator of (J_f) and the localization description of (C_f). Step 3 uses the new complementary-quotient statement, completion flatness, and completion modulo the ideal. These give the quotient (C'), the product isomorphism away from (I), flatness of (B\to B^\wedge), and the residue isomorphism. Step 4 uses the existing formal-glueing-data definition and the new algebra-gluing statement; I wrote out the two overlap compatibilities and the cocycle before invoking the algebra-category consequence. Step 5 uses finite-type algebra, finite-algebra integrality, and the existing idempotent-lifting node; these state respectively finite type, integrality, and the étale base change plus lifted idempotent. Step 6 uses the étale definition, affine flatness criterion, affine étale characterization, and finite-type-to-Noetherian node to verify the replacement algebra has all required hypotheses. Step 7 uses the flat-power quotient comparison and finite-module completion-tensor comparison; I explicitly describe the coordinatewise completion isomorphism and the tensor maps. Step 8 uses finite-module completeness over a complete Noetherian ring, complete-pair henselianity, and the henselian definition; these give uniqueness of the idempotent lift and identify it with ((1,0)). Step 9 is elementary from the idempotent identities and finite-type definition: it constructs the inverse (ex+(1-e)y), checks the product decomposition, and takes inverse limits coordinatewise.

I checked edge cases (c=0) (then (J=J^2) directly), a zero-generator ideal, and the case where one factor of the complementary quotient is zero. The Mathlib searches used LeanFinder, LeanSearch, Loogle, and Mathlib grep for both new nodes and the item; all returned only general completion or already-global idempotent facts, so the three nodes remain unsplit. The server-side `check_dag` preflight passed before this report was written.

Nothing could be attached to a sorry-free project declaration, and no source error was found.
