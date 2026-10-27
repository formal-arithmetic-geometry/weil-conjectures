# Stage-1 delivery: lem-sfb-smooth-section-regular-immersion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-section-regular-immersion.json`: statement node, now split. The statement and its four statement dependencies are unchanged. The proof has five steps and cites only existing nodes. The item is not a Mathlib leaf: Mathlib's immersion cancellation supplies the immersion clause but not regular equations for an arbitrary smooth section.
- `citations.json`: an exact statement quotation for every cited node in each of the five steps.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Existing searches and the full original blueprint ancestry were retained; new searches actually run through msearch.py were appended. `searches.jsonl` is the command's own unmodified log.

## Attachments

None for the item. Searches of `lean/WeilConjectures/` by its blueprint tag and by section/regular-immersion terminology found no declaration stating all its clauses. The smooth-diagonal generator theorem in `WeilConjectures/AlgebraicGeometry/SmoothDiagonalRegularGenerators.lean` requires constant relative dimension and a closed diagonal, and concerns the diagonal, not arbitrary sections. It is not an attachment. Mathlib's `AlgebraicGeometry.IsImmersion.of_comp`, read at `Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:218`, already belongs to `lem-zl-immersion-cancellation` and is cited there rather than duplicated.

## Literature

WANTED: none. Read `literature/stacks-project/divisors.tex`, Tag 067R (`lemma-section-smooth-regular-immersion`), including its proof, and its fibre criterion Tag 063W (`lemma-fibre-quasi-regular`). Also read Tags 067T and 067U (`lemma-immersion-lci-into-smooth-regular-immersion`, `lemma-immersion-smooth-into-smooth-regular-immersion`), and `schemes.tex`, Tags 01KS/01KT, for the immersion/closed-neighbourhood reduction. For affine smoothness read `morphisms.tex`, Tag 01V6 (`lemma-smooth-characterize`) and the smooth-morphism definition immediately before it. The existing affine equivalence node records the formal-smoothness comparison Tag 02H6.

The proof is marked agent-origin: it assembles the actual affine section quotient and reuses the existing smooth-quotient regular-sequence node instead of reproducing the fibre-regularity proof of 067R. The latter node already encapsulates the 063W argument. This is a choice below the unit's proof, with no replacement of its scheme-theoretic or alteration route. The latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` was read along with the unit/chapter records. The existing long `blueprint.from.place` identifies 067R as the supporting input for 067S; it is preserved. The ancestor command returned `None`, agreeing with the item's original `from.node = null`; no ancestor was invented.

## Faults and changes

The imported item was statement-only, and its statement is true as written. There is no statement dispute or correction. The tempting separated-section lemma alone would add an unauthorized separation hypothesis. Instead immersion cancellation applies to the identity composite, so the proof first obtains the open neighbourhood on which the section is closed. Another tempting shortcut would apply a fixed-dimension smooth-section coordinate theorem, which does not directly cover the stated generality. Neither shortcut is used.

The affine neighbourhood of the section's inverse image is not assumed affine merely because it is open: it is affine because it is a closed subscheme of the chosen affine ambient open. Intersections of affine opens are never assumed affine. The smooth-kernel theorem is applied over the separate affine base ring R, with both A and C smooth over R; C is not silently identified with R. This is why it handles an arbitrary section and arbitrary ambient neighbourhood.

## Not duplicates

No nodes were created. The whole-DAG title/source searches and whole-blueprint searches for smooth sections, immersions and smooth-ring comparisons identified reusable nodes, especially `lem-zl-immersion-cancellation`, `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`, and `lem-pur-smooth-quotient-regular-sequence`. The latter is more general commutative algebra, not a clause copied out of this item. The fixed-dimension `lem-sc-smooth-section-affine-coordinates` and `lem-sc-smooth-section-ring-coordinates` are unnecessary here.

## Review by N5

I checked the split against delivery-errors B through E with the item, all cited statements and the Stacks source open. There are no new statement-only nodes to audit or sources to obtain. The statement retains arbitrary schemes, including non-Noetherian and nonseparated schemes, and does not fix a rank. Each quotation in citations.json is a literal part of the corresponding node statement.

Step 1 uses exactly the no-separation immersion cancellation in `lem-zl-immersion-cancellation`, with first arrow s, second arrow f, and composite the identity. The identity is a quotient by the zero ideal. The definition of immersion in `def-weil-closed-immersion` actually gives the closed-into-open factorization used, not just a locally closed set-theoretic image.

Step 2 uses the same node's affine closed-immersion characterization, plus the scheme and spectrum definitions. Given t, choose an affine base neighbourhood T and then an affine ambient neighbourhood V inside the open intersection W with the inverse image of T. Restrict the already closed immersion to V. Its inverse image Z is therefore affine and its section map A to C is surjective. The equality fs = 1 makes Z an open subscheme of T and makes this surjection R-linear. The point s(t) lies on that closed subscheme, giving the required prime Q containing the kernel. All these identifications are written in the step rather than outsourced to an invented affine-chart node.

Step 3 spells out why the open restrictions of f are smooth: finite presentation is local and infinitesimal lifts remain in the source open because nilpotent thickenings have the same points. The definition node supplies precisely those two conditions. `lem-pc-open-immersion-smooth-composition` applied to Z into T followed by the identity supplies smoothness of Z over T. The statement of `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` then translates both actual affine morphisms, V to T and Z to T, to smooth ring maps. This checks both hypotheses of the next node, rather than treating smoothness of the source algebra as enough.

Step 4 reads only the statement of `lem-pur-smooth-quotient-regular-sequence`: its hypotheses are the two smooth maps, the surjective R-algebra map, and the prime containing the kernel. All were established in Steps 2 and 3. Its conclusion gives a principal localization outside Q and a finite regular list generating the extended kernel. It does not assume a Noetherian base, flatness of the section, separatedness of f, or constant dimension. Its underlying 063W source was checked to allow arbitrary flat locally finitely presented ambient schemes; no Noetherian-only fibre lifting lemma is substituted. This existing node is a generic algebra tool, declared as such in split_report.tool_uses, as are the other two off-unit scheme/ring tools.

Step 5 checks the quotient after localization explicitly: lift numerators for surjectivity and multiply by a power of g to identify the kernel. The affine-spectrum and closed-immersion definitions then identify the actual restricted section with the displayed quotient scheme. The regular-sequence definition gives exactly the requested injective multiplications and nonzero quotient. There is a point t in the inverse image, so no empty quotient is accidentally admitted. All steps are under 2000 characters; the localization calculation is a direct elementary calculation, not a hidden regularity theorem.

I tested the empty scheme (all pointwise clauses vacuous), the identity section (zero kernel and empty regular sequence on a nonempty affine), arbitrary-base affine space (coordinate regularity does not require a domain), and varying dimensions on disjoint components (each point chooses its own finite list). For the line with doubled origin over a field, inclusion of one affine-line chart is a smooth section which need not be globally closed; Step 1's open neighbourhood reduction handles it and never asserts global closedness. No dependent node was modified. Every non-elementary step cites an existing statement, and the elementary steps only perform the displayed affine and quotient calculations.

## Unfinished work

None in the stage-1 split. Direct delivery will run the required server preflight, DAG and split checks; no Lean is written or compiled on this machine.
