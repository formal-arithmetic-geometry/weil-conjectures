Files written:

- `dag/nodes/sec-abelian-varieties/lem-pc-recd-fibre-cartier-local.json` — split proof of Tag 062Y(3); no Mathlib match.
- `citations.json` — empty, because the new node is statement-only.

Attachments: none.

WANTED: none.

What was wrong: the imported item had no proof even though it is a real local input to the Tag 0EX8 proof. Its source uses the local part (3) of Divisors Lemma 31.19.9, which is not stated by the existing all-fibres criterion node. I retained the precise local criterion and added its affine-local proof route without duplicating the stronger global statement.

What could not be finished: no sorry-free Lean declaration states this scheme-level local criterion exactly; the algebraic Tag 062Y theorem in the project is lower-level and does not state the scheme conclusion. The Lean proving stage must still formalize the affine translation.

## Not duplicates

`lem-pc-recd-fibre-cartier-local` vs `lem-pc-recd-locally-principal`: the existing node assumes every fibre is an effective Cartier divisor and concludes globally; this node is the local Tag 062Y(3) criterion from one fibre germ and local principality.

`lem-pc-algebra-fibre-cartier-local` vs `lem-pc-recd-fibre-cartier-local`: the new node is the ring-level localization theorem used in the affine reduction, while the item is the scheme-level local conclusion.
`lem-pc-algebra-fibre-cartier-local` vs `lem-pc-recd-locally-principal`: the new node is an algebraic Mathlib declaration for one affine chart, while the existing node is the global scheme criterion over all fibres.

## Review by G1

I checked the item against Divisors, Lemma 31.19.9 (Tag 062Y), part (3), and read the existing all-fibres node `lem-pc-recd-locally-principal` to verify that its hypotheses and conclusion are genuinely stronger and global. I also read `RelativeEffectiveCartier.lean` and the algebraic Tag 062Y declaration in `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`; neither declaration states this scheme-level local neighbourhood result exactly. The proof step follows the source's affine reduction, lifting a fibre regular generator and localizing so it generates the ideal and leaves a flat quotient. The item hypotheses are preserved verbatim: flat and locally of finite presentation for the morphism, local principality of the closed subscheme, an effective Cartier fibre germ at the chosen point, and a relative effective Cartier neighbourhood as conclusion. I checked the small distinction between a single fibre germ and the existing all-fibres theorem, and recorded all required Mathlib searches, including the unavailable LeanSearch service.

## Second reading by G1

- Item statement checked against Divisors Lemma 31.19.9 (Tag 062Y), part (3), hypothesis by hypothesis; local principality is explicitly only near x, matching the source.
- Step 1 checked against the affine reduction in Tag 062Y(3); the affine rings, prime ideals, fibre generator, and quotient flatness hypotheses are stated.
- Step 2 checked against Fiber.lean lines 1024-1035 and Definition 31.19.2; localization gives a regular principal ideal and flat quotient, hence relative effective Cartier.
- New Mathlib leaf checked against `Algebra.exists_notMem_isRegularPrincipal_of_flat_of_fiber` at Fiber.lean lines 1024-1035; searches were rerun with msearch.py and recorded.
- Edge cases checked conceptually: a field base reduces to the usual Cartier criterion; the empty subscheme is excluded by x∈Z; no numerical parameter occurs.
- Changed the item from an elementary placeholder to two explicit proof steps, added the algebraic Mathlib leaf and citations, corrected `created.item`, and corrected global principality to neighbourhood-local principality.
