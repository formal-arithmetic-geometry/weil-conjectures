# Stage-1 report: lem-trf-reduced-scheme-image

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-reduced-scheme-image.json`: item, statement split; no new nodes.
- `citations.json`: citations for steps 1 and 2.
- `report.md`: this report.

## Attachments

None. No exact sorry-free project declaration states the item in `WeilConjectures/`.

## WANTED

None.

## What was checked and corrected

The imported item statement agrees with Stacks Project Tag 056B: for a morphism from a reduced scheme, the scheme-theoretic image is the reduced induced structure on the closure of the topological image. The existing DAG node `lem-weil-pbc-reduced-induced-closed-subscheme` already states the construction, reducedness, and underlying closed subset of that reduced induced subscheme, so I created no duplicate node. The Mathlib searches recorded for this item found only the generic `Scheme.Hom.image` construction and reducedness building blocks; none states the Tag 056B result.

## Review by Q25

I read the item source in `literature/stacks-project/morphisms.tex`, Tag 056B, especially the proof at lines 983–987, and read the complete statement of `lem-weil-pbc-reduced-induced-closed-subscheme` before citing it. Step 1 uses that node to form the reduced induced closed subscheme on `T = closure(f(|U|))`; the affine argument checks that a section of its vanishing ideal pulls back to a section vanishing at every point of the reduced source, hence to a nilpotent section and then to zero. Step 2 checks the minimality direction: the ideal of any closed subscheme through which `f` factors is contained in the vanishing ideal of `T`, so the reduced induced subscheme is contained in every such factor. The hypotheses used are exactly that `U` is reduced and that `T` is the closure of the image. Step 3 is the one-line specialization to the open immersion defining scheme-theoretic closure. I checked edge cases `U=∅` (empty closure and empty reduced induced subscheme), `f` an isomorphism (image is `X`, reducedness forces the image to be `X`), and a constant map from a reduced scheme (image is the reduced closed point/subscheme on its closure). The proof has no hidden new lemma and no statement change.

## What could not be finished

Nothing.
