## What changed

Corrected and proved the bounded-below version of
`AlgebraicGeometry.Scheme.exists_etale_iso_cover_of_proetale_local_iso_section`
in `Sheaf.Paper.EtaleLocalIsoCoverFromProEtaleSection`. The proof uses the existing
fixed-module derived comparison Hom bijection, exactness and conservativity,
together with the canonical localization and comparison/pullback isomorphisms.
It produces an isomorphism on the original etale object, and uses its identity cover.
The private helpers construct the slice equivalence and transport isomorphisms;
they are fully proved and introduce no new public declarations.

Added the required hypothesis `DerivedCategory.TStructure.t.plus D` to this
intermediate theorem and to its immediate generic caller,
`exists_etale_local_representative_of_proetale_local_iso_sections`, in
`Sheaf.Paper.LisseFiniteLevelEtaleLocalRepresentative`. Adapted
`Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms` by extracting this lower bound
from its existing `hDbounded`. Its signature, the unit route, all definitions and
all five Challenge targets stay unchanged. Both adapted modules were unclaimed
when checked on the server.

Updated the three matching DAG records to describe this route, and the two generic
records with explicit statement-change/citer audits. In particular,
`new-lem-weil-pbc-lisse-finite-level-etale-local-representative` also needs correction,
while `lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms` retains its statement.
The change records are:

- `coord/changes/exists_etale_iso_cover_of_proetale_local_iso_section.md`
- `coord/changes/exists_etale_local_representative_of_proetale_local_iso_sections.md`

## Proved and sorry left

The item initially had one hole, in
`AlgebraicGeometry.Scheme.exists_etale_iso_cover_of_proetale_local_iso_section`.
The corrected bounded-below theorem is proved with no local `sorry`. This delivery
is a statement repair; it does not claim a proof of the former unrestricted theorem.
There are zero remaining holes in the item, zero holes added, and zero split-off
statements. Both adapted modules also contain zero holes. The two former generic
statements now have their required lower-bound hypothesis recorded explicitly.
The proof uses existing named dependencies; their independent outstanding proofs
are not moved or replaced by this delivery.

The direct importer chain compiled with `lcompile.py --all`: the item in 7.1 s,
the generic caller in 3.3 s, and the unchanged-signature finite-level theorem in
3.7 s, with no warnings or errors. Final validation and axiom probes are run by
`deliver3.py`.

## No longer needed

Removed the item's public imports of `Sheaf.Paper.LisseTowerEtaleDescentData` and
`Sheaf.Paper.DerivedIsomSheafComparisonFromHom`; the statements instead directly
import `Sheaf.Paper.DerivedLocalIsomorphismSheaf` and
`Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison`. The latter was previously
a private proof import and is now public because the statement uses its definition.

This route does not use Isom sheafification or inverse-pair sheaf comparison, so
`lem-weil-pbc-derived-isom-comparison-from-hom` and its module
`Sheaf.Paper.DerivedIsomSheafComparisonFromHom` are unnecessary for this item's proof.
The two original definition dependencies remain necessary for its statement.
No module is withdrawn, and no claim is made that the removed imports are globally
unreachable: other declarations still use them. No new nodes are needed.

## Where the brief, the DAG or earlier work was wrong

The original generic nodes omitted the lower bound needed by the available derived
comparison theorem. Their proposed passage from pro-etale local surjectivity of
sheafification to a common etale cover is not justified: a pro-etale covering need
not admit an etale refinement. Moreover, the Lean input is already a derived Isom
presheaf section, not merely a section of its sheafification. The direct bounded-below
comparison on V avoids that passage entirely. The consumer's existing boundedness
is exactly what permits the correction without changing the finite-level theorem.
No counterexample to the unrestricted generic statement is asserted here, and its
former generality is not counted as proved.

The old source citation Tag 09BV is `lemma-weird`, not bounded derived comparison.
The applicable source is Stacks Project, proetale.tex, Tag 09B1,
`lemma-compare-derived`, with the relative comparison of Tag 099V. The corrected
proof origin, theorem docstrings and statement-change sources record this.

Edge cases: no finite coefficient ring or lisse hypothesis is added to the generic
comparison result, A remains arbitrary, and only D is required bounded below.
Restriction preserves its lower bound by exactness. Reflection of isomorphisms is
proved on all cohomology maps, so no lower bound on A is used. The singleton identity
cover works for the empty scheme and zero complexes. Geometric-point lifting remains
the existing argument in the generic caller.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleLocalIsoCoverFromProEtaleSection": "28410e2b5db41e7b6f23e398c4aca67200c70635", "Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms": "55615cd82f5b9563698750741d7b35d7a69be881", "Sheaf.Paper.LisseFiniteLevelEtaleLocalRepresentative": "4fdd2d7a45d3f9a0ea5d84742aa35e8a731a1b42"}, "results": {}, "time": "2026-10-28T12:10:14+0800", "transitive": 0, "version": 1}
```

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
