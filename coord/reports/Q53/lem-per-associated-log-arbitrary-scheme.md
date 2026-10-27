## Worker report

Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-associated-log-arbitrary-scheme.json` (statement, split, no Mathlib match), `citations.json`, and this report. The search command wrote `searches.jsonl`. No Lean or repository file was written, and no compiler/build tool was run.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. The five proof steps use existing nodes throughout.

Attachments: none. Searching `lean/WeilConjectures/` for the item tag and LogStructure, logification, and saturated-monoid concepts returned no matching declaration; the upstream sorry declarations are not treated as finished proofs.

WANTED: Kato (1988), Logarithmic structures of Fontaine--Illusie, section 1, for the original associated-log conventions. The item is proved here by an explicit agent argument from existing arbitrary-scheme logification and pushout statements, rather than attributing that generalization to ILO.

The statement is unchanged. ILO VI 1.1 explicitly defaults to locally Noetherian schemes. The item's deliberate arbitrary-scheme convention is instead supplied by its inline definition and the existing arbitrary-scheme logification theorem. Its reference to def-trf-fs-log-blowup supplies the fs monoid terminology, not that definition's Noetherian assumption. The imported proof was empty. The essential repair is to supply both the stalk quotient calculation and the section fraction/gluing argument. No fact is taken from an existing node's proof.

Unfinished work: none for this one-level stage-1 split. Formal Lean proofs are outside this delivery's scope.

## Not duplicates

No new nodes exist, so there are no new/existing pairs. I read `lem-per-fs-log-sections-saturated`: it assumes locally Noetherian X and proves only the section conclusion. It cannot justify the present arbitrary-scheme assertion. I reused `lem-per-integral-chart-logification-thickening` and `lem-per-integral-monoid-unit-pushout`, rather than making another construction or pushout node. Whole-DAG searches for saturation, geometric stalks, logification, and filtered-colimit equality located those nodes and the exact section-germ and colimit nodes. `tools/blueprint_refs.py search 'saturated monoid'` and `search 'log structure'` each returned zero blueprint nodes. The ancestor command confirms `lem-per-artin-gabber-affine-curve`. No blueprint-equivalent assertion was found.

## Mathlib searches

The item's inherited searches are retained. Five additional queries were actually run using msearch.py and are recorded verbatim in both the node and searches.jsonl: grep on AlgebraicGeometry, Loogle on LogStructure, LeanSearch on section saturation, and two distinct LeanFinder phrasings. All services answered. I read every returned signature: integral schemes and their ring stalks concern integral domains, the submonoid-presheaf construction does not assert saturation, topological sheaf mono criteria do not address small-etale logarithmic structures, and unit tests do not assert closure under positive roots in group completion. None gives the item or a one-line specialization of it.

## Review by Q53

I read ILO VI 1.1 (printed p.69; PDF p.75), VIII 3.1.1--3.1.5 (pp.98--99), 3.1.17 (p.101), and 3.3.2--3.3.6 (pp.106--107). These specify the etale chart convention, localization, sharpening and positive-root saturation, but do not themselves state the arbitrary-scheme section assertion. I read the latest blueprint ancestor's proof, especially Step 3, together with the chapter and unit records, and kept the inherited regular-pair/Kummer ancestry. The new proof is marked agent-written. There are no new nodes needing independent source attribution.

Step 1 uses exactly the canonical stalk pushout formula in the statement of `lem-per-integral-chart-logification-thickening`, whose first paragraph allows every scheme. The chart monoid is finitely generated integral, as required there. The statement of `lem-per-integral-monoid-unit-pushout` embeds the mixed pushout into its displayed abelian-group quotient; it permits a noninjective map from E to the units. I checked both statements in full. The group-completion identification is written out by extending a homomorphism on P; it is the defining universal property, not an additional logarithmic theorem.

Step 2 is the explicit elementary calculation from Step 1. Writing nz-p=e1-e2 with e1,e2 in E is allowed because P is integral and E is a submonoid. The identity n(z+e2)=p+e1+(n-1)e2 has nonnegative coefficients because n>0; saturation of P therefore applies in P's own group completion. The adjustment by -f(e2) is exactly a relation in H. This avoids an unnecessary face-localization lemma and assumes neither injectivity of f nor divisibility of the units. It proves a step of this item directly, without a new node restating a clause.

Step 3 uses `lem-weil-pbc-sets-sections-geometric-germ-ext`. I checked that its statement tests every geometric point AND every lift to the etale object, which is exactly what the cancellation argument supplies. It is a set-sheaf result, so no abelian-group hypothesis is imposed on M. I read its source, Stacks Tag 03PU, label theorem-exactness-stalks, in etale-cohomology.tex. The final cancellation-to-group-completion assertion follows from the explicit difference equivalence and is written in the step.

Step 4 uses the definition of geometric stalk as the pointed-neighbourhood colimit, the full cofiltered-neighbourhood statement (no Noetherian assumption), and the Mathlib leaf `lem-weil-pbc-filtered-colimit-sets-elementwise`. I read that leaf's statement: clauses (1) and (3) give representatives and eventual equality, precisely what is used. `def-weil-size-convention` supplies a small skeleton in the larger universe, as required by the colimit leaf. Starting from a point of U keeps the refinements over U. Choosing one geometric lift for each ordinary point makes the etale family jointly surjective; there is no quasi-compactness or finite-subcover argument. The proof uses equality a=d+b in the integral stalk, not uniqueness of n-th roots, which could fail in torsion groups. The quotation in citations.json names the eventual-equality clause, and the full representative clause was also checked.

Step 5 uses only the already proved cancellation on the overlap objects and the actual equalizer/gluing statement of `def-weil-pbc-etale-sheaf-of-sets`. I checked the source definition, Stacks 00VM (definition-sheaf-sets), with etale coverings as in 0215. Agreement on each fibre product is justified by dV+b=a=dW+b, rather than asserted as an unexplained transport. Both d and the equality d+b=a glue. Thus the original fraction a-b is the global section d. The empty-cover case is included explicitly.

Small cases checked: the empty scheme has the one-element section monoid; a trivial log structure has a group of units, which is saturated even with torsion; P=0 and E=P give the same case. The algebra calculation also permits noninjective E-to-G maps, n=1, and torsion in H. No finite generation of sections is used or concluded, and X need not be locally Noetherian. Every non-elementary input is an existing cited statement; all citations.json quotes were checked as literal substrings of those statements. Each step is below 2000 characters. There is no new-node relabelling, definition-only disguised proof, statement correction, or SGA citation. The generic geometric-germ equality theorem is declared as a tool use in split_report for the maintainer's judgment; no maintainer-owned tool_uses field was added.

The first full dry run requested longer citation excerpts for Steps 3--5 (the original literal excerpts were under its 40-character minimum). I replaced those excerpts with the full cited statements. No mathematical or statement change was necessary.
The second attempt still considered the short stalk formula insufficient after its quote-length normalization. Every citation now contains the full statement, including the stalk definition and all hypotheses.
