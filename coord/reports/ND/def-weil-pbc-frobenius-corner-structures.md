# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/def-weil-pbc-frobenius-corner-structures.json`: existing definition audited and marked split; no new nodes and no Mathlib leaves.
- `citations.json`: empty list because a definition has no proof steps.

## Attachments

None. I searched the read-only slopmaster2 WeilConjectures source for the blueprint id and for the Frobenius/corner names; no declaration states this definition. The upstream master source is reference material only and is not treated as a finished proof.

## WANTED

None.

## Problems corrected or reported

The imported node was an unsplit definition with empty blueprint `same_as` and no stage-1 split metadata. I preserved its statement and its sole statement dependency `def-weil-pbc-frobenius-tower-datum`, set `status` to `split`, filled `same_as` with the result of whole-blueprint searches (none), and recorded the complete blueprint clause in `split_report`. No child lemma is appropriate: the displayed composites are the data of the definition itself, not separately proved propositions. No statement error was found.

I ran the required Mathlib searches for the item. LeanFinder returned only Witt-vector isocrystal declarations, Loogle returned no usable hit (the query parser reported an unknown `IsIso` identifier), Mathlib grep returned no hits, and LeanSearch was unavailable; none matches the derived-category Weil-structure definition.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches for the item id and for the phrases “Weil structures on the four finite corners”, `vartheta_E`, `Theta_B`, and `Theta_D` found no duplicate statement.

## Review by ND

I read the item node, chapter and unit records, the master blueprint definition at `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-frobenius-corner-structures.md`, and the dependency `def-weil-pbc-frobenius-tower-datum`. The item statement agrees clause by clause: from the tower datum it takes `E_n=L(g')^*K_n`, `vartheta_n`, `kappa_{g'}`, `kappa_g`, `beta_{f,n}`, `beta_{f',E_n}`, and the four corner objects and projection-formula maps. The first composite has type `Phi_{X'} E_n -> E_n`; the second and third composites have types `Phi_{Y'}B_n -> B_n` and `Phi_{Y'}D_n -> D_n`; conjugation by the displayed isomorphisms `h_n` and `h'_n` gives the A and C structures. Since every component is an isomorphism, the final sentence's genuine Weil types follow directly from the definition of transport across an isomorphism. There are no numbered proof steps, so no non-elementary fact is cited and `citations.json` is correctly empty.

I checked edge cases at the definitional level: `n=1` uses the same tower component without an extra hypothesis; zero complexes make every displayed composite the unique zero-category isomorphism when applicable; and identity projection-formula maps make the transported A/C structures reduce to the B/D structures. The statement introduces no additional coefficient category or hypotheses beyond the tower datum. No Lean files, compiler, Lake, or build tools were used.

## Unfinished work

None. The sandbox is ready for the second reader and the mandated dry run.

## Second reading by ND

- Item statement: checked every displayed object, composite, source and target against the blueprint TeX node (order 1333) and dependency `def-weil-pbc-frobenius-tower-datum`; all hypotheses and four corner cases agree.
- Definition clause for `E_n` and `\vartheta_{E,n}`: checked that the pullback comparison `\kappa_{g',K_n}` and `L(g')^*(\vartheta_n)` compose with the stated source and target, using only the dependency's displayed isomorphisms.
- Definitions of `\Theta_{B,n}` and `\Theta_{D,n}`: checked each arrow and intermediate object against the source, including the exchange maps and the induced Weil isomorphism types; no proof step is required for a definition.
- Transport definitions of `\Theta_{A,n}` and `\Theta_{C,n}`: checked conjugation by `h_n` and `h'_n` has the stated domains and codomains and preserves isomorphisms.
- New-node audit: there are no child nodes; this imported definition is not a duplicate, restatement requiring a proof, or Mathlib declaration. Whole-DAG and whole-blueprint searches for the identifier and distinctive Frobenius/projection-formula terms found no duplicate.
- Edge cases: checked `n=1`, zero complexes, and identity comparison maps; the formulas remain well typed and reduce as stated.
- Metadata repair: retained the source statement and dependency, with `status = split`, complete `split_report`, and blueprint `same_as = []`; no citation or proof dependency is needed for a definition, so `citations.json` remains empty.
