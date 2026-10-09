# Stage 1 delivery: \`lem-weil-pbc-constant-sheaf-sections-locally-constant\`

## Files written

- \`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-sheaf-sections-locally-constant.json\`
- \`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-group-scheme-morphism-clopen.json\`
- \`dag/nodes/sec-proper-base-change/lem-weil-pbc-small-etale-representable-presheaf-sheaf.json\`

The two new nodes are public unsplit statement nodes. Each has \`created.item\`
equal to the assigned item, its own source citation and four Mathlib searches
(LeanSearch, LeanFinder, Loogle and source grep), with no Mathlib match.

## Repair

The parent proof now has two explicit steps. The first cites the new clopen
decomposition node and compares, for every etale \(U\), the canonical map
\(E\to h_{T_E}(U)\) with the constant maps. The second cites the new
representable-sheaf node at Stacks Tag 03O3, forms the factorization
\(\underline E\to h_{T_E}\), and explains why the clopen local representatives
make this sheafification comparison an isomorphism. It then identifies sections
over \(T\) with Zariski-locally-constant maps and tracks the canonical constant
section.

## Verification

- \`python3 tools/review_split.py lem-weil-pbc-constant-sheaf-sections-locally-constant\`: PASS; reports the two new nodes.
- \`python3 tools/check_dag.py --cycles\`: 0 cycles. It prints the repository's nine pre-existing reach warnings; this repair introduces no new warning.
- All three modified JSON files parse successfully, and \`git diff --check\` is clean.

No Lean code or compilation was used.

## Review by C1

I checked the return points against the repaired graph and sources. The new
constant-group-scheme node states the actual coproduct \(T_E=\coprod_{e\in E}T\)
and the inverse-image clopen decomposition; it also states, rather than leaves
implicit, that \(e\in E\) maps to the constant section in
\(h_{T_E}(U)\). Its source is Groupoids Example 39.5.6 (Tag 03YW), as used by
Etale Cohomology Remark 59.23.2 (Tag 03P5). The new representable-presheaf node
states the descent datum and unique gluing on the small etale site and cites
Etale Cohomology Lemma 59.15.8 (Tag 03O3).

The repaired parent proof uses both nodes. It forms the canonical map from the
constant presheaf to \(h_{T_E}\), factors it through sheafification, and
explicitly proves the induced comparison \(\underline E\to h_{T_E}\) is an
isomorphism: clopen pieces give etale-local constant representatives, while
the sheaf uniqueness condition gives injectivity. Taking sections over \(T\)
then gives precisely the Zariski-locally-constant maps of 03P5 and preserves
the canonical constant section and pointwise group law. The statement and
dependencies remain on unit sk-thm-p1; no unrelated node or route was changed.
