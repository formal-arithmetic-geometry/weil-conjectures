# Stage 1 report: lem-per-regular-lci-geometric-calculus

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-lci-geometric-calculus.json` — statement node, split, with eleven proof steps. No new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement excerpts (whole statements where helpful) for every node cited in every proof step, including elementary steps.
- `report.md` — this report, continued from the interrupted attempt.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag, regular immersions and virtual dimension found no declaration stating all clauses of this item. `AlgebraicGeometry.IsRegularImmersion.ringKrullDim_stalk_add` in `AlgebraicGeometry/Morphisms/RegularImmersion.lean` concerns a regular immersion into a smooth scheme over a perfect field, with additional finite-type hypotheses; it is not the present general theorem. Other declarations in that file give only individual clauses, so no attachment of the whole item is claimed.

## WANTED

None. The split uses local Stacks sources and existing DAG inputs; it does not require an additional ILO argument beyond the provenance already recorded on the item.

## What I checked and corrected

The interrupted attempt had already written the item, report, citations and `searches.jsonl`. No delivery process was still running. Its required first resumed dry run passed at `17d34007af`, but mathematical rereading exposed gaps that mechanical preflight did not detect. I retained the statement, blueprint provenance, inherited searches and logged search results. I restored the original `created` metadata instead of claiming creation of this existing node. I corrected statement dependencies to definitions actually used in its statement.

The old flat-base-change step applied `lem-pur-relative-regular-equations-base-change` without its flat-quotient hypothesis, which is not a consequence of flat ambient base change. The repaired step tensors each regular-sequence multiplication injection using flat tensor exactness and the quotient/tensor isomorphism. The old dimension step used `lem-trf-local-dimension-formula`, whose statement gives an inequality under integral/dominance hypotheses, to assert an equality. The repaired calculation instead uses the exact flat height formula and the dimension formula on the smooth fibre. The old section step cited regular equations without proving their number was the relative dimension; the conormal exact sequence and rank of smooth differentials now give that number. The argument now also spreads local generators to actual principal neighbourhoods, justifies local constancy by conormal freeness, and cites the finite-residue-field theorem in the quasi-finite case. No statement correction or route departure was necessary.

I read the inherited Mathlib hits and the actual `searches.jsonl` results rather than rerunning unchanged queries. The logged searches find smooth-relative-dimension declarations and separate regular-sequence tools, not this combined theorem. Rejected Loogle expected-name queries are identified as such and not treated as evidence of absence. The last logged item queries are also recorded verbatim in the node with their actual result records. No search is invented and no new-node search obligation arises.

## Review by Q68

I read the fixed chapter and unit records, the ancestor `lem-per-artin-gabber-affine-curve` and its blueprint provenance, the current repository item and the interrupted sandbox copy. The item is a geometric tool below the regular finite-torsion duality argument; none of the unit or chapter statements is changed. I checked delivery-errors B through E with the files open. There are no new nodes, so self-contained new statements, duplicate tags, new Mathlib leaves, and clause-restatement nodes do not arise. All reused statements were read from their actual node files; `citations.json` copies their wording rather than supplying stronger paraphrases.

Step 1 uses exactly the regular-local quotient-kernel theorem (Stacks 00NR, `lemma-regular-quotient-regular`) and the regular-system-of-parameters theorem. I checked that both local rings are regular and that the quotient is nonzero at the source point. Restricting an immersion to an ambient open is legitimate by the cited definition. An initial segment is regular by its multiplication tests and the proper maximal ideal.

Step 2 uses `lem-exc-regular-sequence-principal-neighbourhood` (061L, `lemma-regular-sequence-in-neighbourhood`) and `lem-weil-pbc-regular-sequence-conormal-free` (00LN in degree one). Their statements supply precisely spreading and conormal freeness. Noetherianity gives finite generation of the ideal; the denominators killing the finitely many generator classes are written explicitly. Reducing a free-module isomorphism modulo the maximal ideal proves equality of lengths, so local constancy is established on the immersed source, not asserted on its complement.

Step 3 was checked against divisors 067P, `lemma-flat-base-change-regular-immersion`, and algebra 00LM. Its four cited statements now give flat tensor exactness, the explicit quotient/tensor identification, regularity after prime localization, and conormal rank. Flatness is assumed of the ambient ring map, exactly where tensor exactness uses it. The pulled-back quotient need not be flat. Localization is only at a prime containing all equations, so the final quotient is nonzero. Step 4 follows algebra 065K, `lemma-join-regular-sequences`, and divisors 067Q: I checked each prefix quotient and the final local quotient. This concatenation is elementary from the definition, with conormal freeness cited for additive rank, and is not moved into a new node.

Step 5 was read against divisors 067R, schemes 01KT (`lemma-section-immersion`), algebra 06A9 (`lemma-application-NL-smooth`), and morphisms 02G1 (`lemma-smooth-omega-finite-locally-free`). The separated-section node says exactly that the section is closed. The smooth-pair node applies to the identity of S and the smooth V over S. The smooth conormal node is applied with A=C=R and I=0, which makes its exact sequence the required isomorphism. The differential-rank node states constant rank r and the conormal-free node states that the rank equals the number of equations. Thus no field hypothesis from the different, field-only conormal node is silently used.

Step 6 uses regularity ascent for smooth ring maps (07NF, `lemma-regular-goes-up`) and the existing affine-space smoothness statement, both with their actual regular-base hypothesis. Step 7 uses the all-affine-pairs finite-type characterization (01T2), the polynomial-surjection definition of finite-type algebra, and the affine spectrum/closed-immersion definitions. The evaluated polynomial presentation is written down, and regularity of every such immersion follows from Steps 1, 2 and 6; it is not asserted from a missing polynomial-regularity citation.

Step 8 was checked against algebra 00ON, `lemma-dimension-base-fibre-equals-total`, and morphisms 02FX, `lemma-dimension-fibre-at-a-point`. `sbc-lem-smooth-criterion` supplies flatness, local finite presentation and smooth fibres. The flat height node states the exact stalk equality used, and `lem-sbc-scheme-fibre-stalk-quotient` identifies its quotient term with the fibre stalk. The field dimension node supplies dimension plus residue transcendence degree on a finite-type affine fibre chart. Relative dimension r refers to dimension at a fibre point, as in the smoothness definition, not fibre local-ring dimension. Step 9 uses the regular-sequence dimension equality and the existing theorem that Noetherian local dimensions are finite before subtracting integers. The closed-immersion residue fields agree by quotienting local rings. Smooth relative dimension is locally constant by its cited node; codimension is locally constant by Step 2. No universal-catenarity, dominance or extra hypothesis is smuggled into the calculation.

Step 10 uses algebra 0ALW (`lemma-finite-type-algebra-finite-nr-primes`) and morphisms 01TG/01TH to pass from finite fibres to isolated fibre points and finite residue extensions. Finiteness of the topological fibre alone does not imply discreteness; the finite-type-field-algebra theorem is explicitly used to make all points closed, after which finite unions give open singletons. The isolated-fibre-point node then states precisely the finite residue extension needed. Linear dependence of powers proves algebraicity, and the transcendence-degree definition gives zero. Step 11 checks empty sources and empty regular sequences at nonzero local rings. I also tested the formulas on the identity (r=c=0), a rational-point section of affine r-space (codimension r), a generic point of affine space over a field (the transcendence term equals r), a hypersurface of a regular local ring (dimension drops by one), and finite field extensions (transcendence degree zero).

No proof step exceeds 2000 characters. The longest is a single neighbourhood-generation argument, with its non-elementary spreading input cited separately. The statement is unchanged and no new statement requires a small-case audit. All off-unit statement inputs are declared as generic tools in `split_report.tool_uses`; they do not replace the unit's proof route. No SGA source, Lean writing, compiler, Lake, build, direct live edit or launcher edit was used.

## Not duplicates

No new nodes were created. Existing algebraic and scheme-theoretic nodes were reused throughout.

## What remains

The interrupted split and the first repaired snapshot passed server preflight. The final snapshot receives the required dry run and direct delivery; the successful delivery command's commit is reported in the final answer.
