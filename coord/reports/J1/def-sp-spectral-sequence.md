1. Files written:
- `dag/nodes/sec-abelian-varieties/def-sp-spectral-sequence.json`: definition, Mathlib exact match `CategoryTheory.SpectralSequence`.

2. Attachments:
- No project declaration attachment; the node is a Mathlib leaf.

3. WANTED:
- None.

4. What was checked:
- The item node and chapter record were read. The stated data (abelian category, index set, family of complex shapes, starting page, pages, page homology isomorphisms, and compatible morphisms) agrees exactly with the `CategoryTheory.SpectralSequence` and `.Hom` structures in Mathlib/Algebra/Homology/SpectralSequence/Basic.lean, lines 37-61. The project source was searched for the blueprint tag and for the defining terminology; no project declaration was found.
- I searched the DAG and blueprint references for duplicate definitions; `blueprint_refs.py search` found no other blueprint node for this definition. The item was searched twice with LeanFinder, Loogle, and Mathlib grep; the exact Mathlib declaration was read directly. LeanSearch was unavailable and is recorded as unavailable. The first LeanFinder/Loogle searches returned only related homology declarations; the second Loogle and grep searches found the exact structure.
- Since this is a Mathlib leaf, there are no proof steps or citation quotes. The definition was tested against the small conceptual case of a single page index: the structure still supplies a page and its homology-to-next-page isomorphism for each permitted page, exactly as the project statement requires.

## Review by J1
- I checked the source declaration hypothesis by hypothesis: `[Category C] [Abelian C]`, `c : ℤ → ComplexShape κ`, and `r₀ : ℤ` are the same parameters as the node. `page r` is a homological complex of shape `c r`; `iso r r' pq` identifies its homology at `pq` with the next page object when `r + 1 = r'`. The Mathlib `Hom` structure states the compatible family of page morphisms and its commuting homology squares. Thus the match is exact, not a specialization requiring an additional theorem.
- No new unsplit node was created, no external fact is cited, and no statement was altered. The item status is `mathlib`, with the declaration and source lines recorded in `mathlib_match`.

## Second reading by J1
- Item `def-sp-spectral-sequence`: checked the statement against `CategoryTheory.SpectralSequence` and `.Hom` in `Mathlib/Algebra/Homology/SpectralSequence/Basic.lean` lines 37-61; verdict: exact Mathlib leaf.
- New nodes: none; no proof steps or citations require review.
- Changes: none; the worker split already records the declaration, source lines, blueprint search, and unavailable LeanSearch service accurately.
