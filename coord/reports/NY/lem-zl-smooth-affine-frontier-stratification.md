# Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-general/lem-zl-smooth-affine-frontier-stratification.json` — item, statement node, no new nodes, no Mathlib leaf created.
- `citations.json` — 26 verbatim step/node citation entries.

Attachments:

- No new attachment was claimed for the item. Existing reusable statements are cited directly, including `lem-pur-geometrically-reduced-dense-smooth-open`, `lem-zl-bertini-finite-field-descent`, and `lem-zl-affine-geometric-components-finite-extension`.

WANTED:

- None.

What I checked and corrected:

- The imported statement is unchanged. I checked the empty scheme case, the zero-dimensional case, and the case of a nontrivial finite partition. The proof now explicitly starts on the reduced geometric scheme, uses a finite good Noetherian refinement, removes a dense finite union of smooth affine opens by strong induction, and records the frontier ordering.
- No new node was needed. The dense smooth locus is exactly the statement of `lem-pur-geometrically-reduced-dense-smooth-open`; finite irreducible components, a nonempty open in each component, geometric reducedness over the perfect field, local constancy of smooth relative dimension, and reduced induced closed subschemes are all taken from existing nodes whose statements I read.
- The finite-field step is written as descent of one finite diagram of finitely presented schemes, morphisms, open immersions, and containment equations. It cites the existing finite-presentation spreading-out theorem and the existing closed-subscheme finite-field descent lemma. Smoothness and open immersions at a common finite stage use the existing qcqs limit descent nodes; geometric connected components use the existing affine finite-field component lemma. The report does not assume that a geometric open or component is automatically defined over the original field.
- `proof_deps` is the union of all step uses. Every citation in `citations.json` is a verbatim prefix of the cited node's statement. The only off-unit generic tools are declared in `split_report.tool_uses`.
- I ran the required Mathlib searches through `msearch.py` for both the item and the candidate generic-smooth-open split, including LeanFinder, Loogle, grep, and LeanSearch. They returned no exact Mathlib theorem for either statement; the item retains its existing search records and no Mathlib leaf was added.

## Review by NY

I read the item node, the unit `sk-i-dl-general-real`, and the main-20261015 proof paragraphs 6–7. For the induction step I checked the statements of the good Noetherian refinement, finite irreducible-component, component-open, perfect-field geometric-reducedness, dense-smooth-locus, and reduced-induced-closed-subscheme nodes. Those statements provide exactly the topological and scheme structures used in Steps 2–4; no step relies on an implementation detail from a cited proof. I checked that each chosen affine open lies inside the selected original partition part, that removing the other components makes the chosen pieces disjoint, and that the complement is a proper reduced closed subset. I checked the smooth relative dimension node before asserting a single integer on each connected piece.

For descent I read `thm-pd-spreading-out`, `lem-zl-bertini-finite-field-descent`, `lem-weil-pbc-descend-smooth-qcqs`, `lem-weil-pbc-descend-open-immersion-qcqs`, and `lem-zl-affine-geometric-components-finite-extension`. Their statements respectively supply finite diagram descent, closed-subscheme descent over a finite field, eventual smoothness, eventual open immersions, and geometrically connected affine component models. I verified that the finite collection of chain maps, component inclusions, affine presentations, and containment equations can be put at one common stage, and that enlarging the finite field by a common multiple preserves all prior data. The zero-dimensional conclusion was checked against Tag 06LH: a smooth geometrically connected zero-dimensional finite-type scheme over `k_m` is `Spec k_m`.

I also checked small cases: empty `X_0`, a point, a disconnected finite union, a singular reduced scheme (where the induction removes the singular complement), and a partition whose pieces are not Frobenius-stable. No statement or hypothesis was weakened, no duplicate node was created, and no cycle was introduced.

What I could not finish:

- Nothing remained unfinished in the split; the required dry run and delivery are the remaining execution steps.
