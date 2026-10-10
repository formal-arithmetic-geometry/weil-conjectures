Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-descend-morphisms.json` (statement, split)
- `dag/nodes/sec-picard-framework/lem-pc-affine-perfect-hom-colimit.json` (statement-only, Mathlib no match)
- `citations.json`

Attachments: none.

WANTED: none.

What was wrong or incomplete: the imported item had no proof and omitted the scheme dependency from `stmt_deps`; the proof is supplied here. The item is the full-faithfulness statement of Stacks Tag 09RE, not the semicontinuity theorem named by the unit record. The affine computation is isolated as a narrower auxiliary statement; it is not a restatement of the global item.

## Not duplicates

`lem-pc-affine-perfect-hom-colimit` vs `lem-pc-affine-perfect-colimit-descent`: the existing node descends a bounded finite-projective complex, while the new node descends derived Hom morphisms into a K-flat complex.

`lem-pc-affine-perfect-hom-colimit` vs `lem-pc-perfect-descend-morphisms`: the delivered item is the global scheme-level full-faithfulness theorem, including finite-open induction, isomorphism descent, and simultaneous equalities; the new node is only its affine algebra calculation for a fixed bounded finite-projective source and K-flat target.

## Review by F1

I read `literature/stacks-project/perfect.tex` at Lemma 36.29.2, Tag 09RE, including the induction on quasi-compact opens, the affine bounded-projective/K-flat calculation, and the eventual equality argument used to descend inverses. I also read the existing statements of `lem-pc-derived-mayer-vietoris-triangle` and `lem-pc-affine-perfect-colimit-descent`; the former supplies exactly the two-open distinguished triangle used in Step 1, while the latter only descends complexes and therefore cannot replace the new affine Hom statement. Step 1 uses the Mayer–Vietoris triangle and the quasi-compact/quasi-separated finite affine cover; Step 2 uses the new affine Hom-colimit statement verbatim; Step 3 is elementary filteredness plus the inverse equations and cites no node. The hypotheses that the source is perfect and that the affine target admits a K-flat representative are checked before applying the affine statement. I tested the edge cases of a one-point affine scheme (the map is the ordinary filtered-colimit Hom calculation) and an identity morphism (the descended inverse is the identity at every stage). The new node was searched with LeanFinder, Loogle, grep, and LeanSearch; no Mathlib theorem matched, and the unavailable LeanSearch service is recorded as such.

## Second reading by F1

- Item statement: checked against Stacks `perfect.tex`, Lemma 36.29.2, Tag 09RE, hypothesis by hypothesis; the filtered-system stages and later pullbacks are now explicit, and the perfect/perfect specialization is valid.
- Step 1: checked against Tag 09RE's quasi-compact-open induction and Mayer–Vietoris paragraph; the existing induction node and the triangle node now state the facts used.
- Step 2: checked against Tag 09RE's affine bounded finite-projective/K-flat calculation; it uses the auxiliary affine statement verbatim.
- Step 3: checked against Tag 09RE's inverse and finite-equality conclusion; filtered-colimit representative equality and the two inverse equations justify the elementary step.
- `lem-pc-affine-perfect-hom-colimit`: checked against the affine paragraph of Tag 09RE; self-contained ring-system, bounded finite-projective, and K-flat hypotheses, with recorded LeanFinder/Loogle/grep/LeanSearch searches and no Mathlib match.

Changes made: added the existing quasi-compact-open induction dependency and verbatim citation; defined `X_j`, `P_j`, and `Q_j` in the item statement; corrected the item recorded in `created`; and recorded the induction node as a tool used by the split. Small cases checked were a one-point affine scheme, the identity morphism, and the zero morphism; no statement failure was found.
