# Stage-1 split: lem-weil-pbc-etale-sections-flat-qc-connected-fibres

## Files written

- Item: dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-sections-flat-qc-connected-fibres.json, split in three steps.
- New: lem-weil-pbc-etale-sections-fpqc-descent, statement, unsplit, no Mathlib match.
- New: lem-weil-pbc-etale-geometric-fibre-constant-sections, statement, unsplit, no Mathlib match.
- citations.json: verbatim excerpts from every cited statement, by step.

## Attachments

None. AlgebraicGeometry.Etale.isIso_upperStarSectionsMap at WeilConjectures/SixFunctors/Etale/SmoothBaseChange/DegreeZero.lean:229 has sorry and states only the module-sheaf chart version, not the arbitrary sheaf-of-sets assertion of this item. No other matching Lean declaration was found by ID or concept.

## Sources and changes

I read the local Stacks copy /home/ubuntu/c1-stacks-review/etale-cohomology.tex, Lemma 59.39.3, label lemma-sections-upstairs, Tag 0A3H, lines 5028-5070, and Lemma 59.39.2, label lemma-describe-pullback, Tag 09XN, lines 4958-5027. The canonical literature path is literature/stacks-project/etale-cohomology.tex; this clone does not have its generated literature directory. Tag identities were checked in /home/ubuntu/c1-stacks-review/tags/tags. The item is precisely 0A3H for arbitrary sheaves of sets, with no extra hypotheses. The existing node had no proof. I corrected its quasi-compactness citation: def-weil-scheme-morphism-properties merely points to def-weil-finite-type-morphism, which actually defines quasi-compactness.

The Stacks proof says the connected geometric fibres make f surjective, flat and quasi-compact make it an fpqc cover, the pulled-back sheaf restricts on a geometric fibre to a constant sheaf of stalk values, and Tag 09XN descends a section whose two projection pullbacks agree. The two new nodes state exactly the last two non-elementary inputs; neither restates the item. Search of all dag/nodes for Tags 09XN and 0A3H and the relevant concepts found no node with either new statement. Blueprint searches for 09XN, 0A3H, sections upstairs, and constant on connected geometric fibres found no duplicate. LeanSearch returned HTTP 500; LeanFinder and Mathlib source grep yielded no matching declaration. The new nodes record all three searches, including the failed service.

## Review by J1

The item statement matches Tag 0A3H hypothesis by hypothesis: f is flat and quasi-compact, each geometric fibre is connected, F is an arbitrary small-etale sheaf of sets, and the result is the canonical global-section bijection. The Tag 09XN node includes the sheaf-of-sets and fpqc-family hypotheses and states the equalizer of sections, including the singleton case actually used. Its source says this explicitly. The geometric-fibre node extracts the final paragraph of Tag 0A3H: inverse image from an algebraically closed point is the constant sheaf of the geometric stalk, sections on a connected nonempty fibre have one stalk value, and projection pullbacks preserve that value. These statements remain valid for a point; for a nonempty disconnected scheme only the constant-sheaf assertion is used, and for an empty scheme the connected conclusion is not asserted. For Tag 09XN, the identity fpqc cover reduces the equalizer to the ordinary sheaf section, and a two-element fpqc cover has the usual matching-family equalizer.

Step 1 uses the nonempty clause of def-weil-connected-scheme to prove surjectivity, the fibre-product description in def-weil-geometric-fibre to pass from a geometric-fibre point to a point of T, the flat definition, and the quasi-compact preimage clause of def-weil-finite-type-morphism. For every affine V in S, the inverse image has a finite affine cover; because f is surjective its images cover V. This checks the exact finite-affine condition in def-weil-pbc-fpqc-covering. I replaced the earlier generic property-node citation after opening it and finding that it did not state this clause.

Step 2 chooses an algebraic closure of each residue field as required by def-weil-geometric-fibre. It uses both cited clauses of lem-weil-pbc-etale-geometric-fibre-constant-sections: unique stalk value on the connected nonempty fibre and naturality under both projections from its self-product. The fibre-product identity is the associative rearrangement of the defining fibre product. No connectedness of the self-product is assumed.

Step 3 checks equality at every geometric point of the fibre product of T with itself over S: its algebraically closed field contains an embedding of the algebraic closure chosen in Step 2, so the point factors through that geometric fibre. Equality of germs yields equality locally by the definition of geometric stalks; the equalizer/sheaf axiom in def-weil-pbc-etale-sheaf-of-sets then gives global equality. The singleton descent clause of lem-weil-pbc-etale-sections-fpqc-descent says exactly that this equalizer condition gives a unique downstairs section. The cited definitions and the two new statements cover each non-elementary fact used, and the citations file uses verbatim portions of those statements. The hypotheses of both new nodes are verified where applied. The case S = Spec(k), T = Spec(k) gives the identity map; the case T = Spec(K) over separably closed k agrees with the already split field-extension item; a disconnected fibre is excluded, since a constant sheaf can then have distinct component values.

The blueprint ancestor is lemma-weil-pbc-proper-underived-exchange, whose strict-henselian-to-geometric-fibre paragraph is the place this supporting comparison serves. The item and new nodes record that place and the via chain; no blueprint node states either new result. Nothing remains unfinished in this one-level split. The two new dependencies are intentionally statement-only items for later workers.
