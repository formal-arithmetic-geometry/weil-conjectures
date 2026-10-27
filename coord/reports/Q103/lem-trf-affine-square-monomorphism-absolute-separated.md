# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-affine-square-monomorphism-absolute-separated.json`: split item.
- `dag/nodes/sec-trace-formula/lem-trf-scheme-monomorphism-separated.json`: Mathlib leaf, exact match.
- `citations.json`: verbatim statement quotes for every proof-step citation.

Attachments: none.

WANTED: none.

The item follows the first proof paragraph of Stacks Tag 0265. I read the source
paragraph in `literature/stacks-project/spaces.tex`, the affine fibre-product lemma
(Tag 01I4) and the monomorphism-separated lemma (Tag 01L4). The existing DAG nodes
`lem-weil-pbc-fibre-product-affine-spectra`, `def-pc-fibre-product`, and
`lem-sc-separated-over-affine-scheme-separated` were opened and used only for the
statements they actually contain. The new node records Mathlib's
`AlgebraicGeometry.IsSeparated.isSeparated_of_mono` at
`Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:61`; its class statement is
exactly the scheme monomorphism separatedness assertion.

## Review by Q103

For step 1 I checked the hypotheses of the existing affine-spectrum fibre-product
node: both factors are `Spec A`, the base is `Spec ℤ`, and the projections are the
maps `a ↦ a ⊗ 1` and `a ↦ 1 ⊗ a`. The fibre-product definition supplies the
transport along the chosen affine isomorphism and makes `P` affine. For step 2 I
checked both projection equations from the fibre-product universal property. If two
maps into `V` have equal composites with `k`, equality after the two projections
forces equality by the universal property; cancelling `k` and then the assumed
monomorphism `j` proves that `q` is monic. This step is marked elementary because it
is a direct two-line use of the cited universal property.

For step 3 the new Mathlib leaf says exactly that a scheme monomorphism has a closed
immersion diagonal, hence is separated, with no finite-type or quasi-compactness
hypothesis. For step 4 I checked that the target of `q` is the affine scheme `P`
from step 1, so the existing separated-over-affine node applies and gives the
absolute structure morphism `R → Spec ℤ` separated. Thus neither separatedness of
`S` nor finite type of `j` is used. I copied each cited node's full statement into
`citations.json` and verified every quote is verbatim.

I searched the DAG and blueprint for an existing monomorphism-separated node and
found no existing node stating this fact for arbitrary scheme monomorphisms; some larger statements cite Tag 01L4 in their sources. The Mathlib searches were run with
`msearch.py` for LeanSearch, LeanFinder, Loogle, and Mathlib grep; the combined
statement had no match, while the new node's exact Mathlib leaf was verified from
its source line.

I checked the new statement on the empty scheme, identity morphisms, and the
monomorphism Spec ℚ → Spec ℤ. The last map need not be a closed immersion or
locally of finite type; the conclusion concerns its diagonal, which is an
isomorphism. For the item, A equal to the zero ring forces U, V, P and R empty,
and all assertions remain valid. A nonseparated S causes no problem because the
comparison uses cancellation on projections rather than closedness of its image.
No statement correction was needed. No new unsplit proof is hidden in the new
node: it is an exact Mathlib leaf. Each proof step has fewer than 2000 characters.
Nothing remains unfinished. No Lean source or repository file was written, and
no compiler or build tool was run.

## Not duplicates

lem-trf-scheme-monomorphism-separated vs lem-fd-finite-ring-compact-support-finiteness: the existing statement concerns constructibility and boundedness of compact-support derived direct image with a supplied compactification; it does not assert separatedness of every monomorphism.

lem-trf-scheme-monomorphism-separated vs lem-trf-monomorphism-finite-type-composite-lqf: the existing statement assumes a locally finite type composite and asserts unramifiedness and local quasi-finiteness as well; the new leaf assumes only monicity, which is needed here without a finite-type hypothesis.


Dry-run correction: the first preflight required the explicit numeric `mathlib_match.line` field, in addition to the line already named in `how`. I added `line: 61`, verified against the source read above.
