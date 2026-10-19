# Worker report

Files written: `lem-trf-integral-support-saturation.json` (split item), `lem-trf-integral-support-weighted-initial-degree.json` (new unsplit statement node), and `citations.json`.

Attachments: none. No finished declaration with this statement occurs in the slopmaster2 source.

WANTED: none; the ILO PDF is present. The least-weight argument is stated as an agent node because the cited source gives the normalization argument but not a separately formalized lemma.

The imported item was unsplit. I checked the parent normalization node and the unit/chapter records. The new node is strictly smaller: it only gives the obstruction from one negative weight. The item proof first puts the monoid generators, the support of the element, and the finite supports in a chosen monic equation into one finitely generated torsion-free subgroup. This avoids assuming that an arbitrary ambient torsion-free group is finitely generated or that a weight extends from a subgroup. The rational-cone finite half-space node gives a weight nonnegative on P and negative at the selected support exponent. The weighted obstruction then contradicts integrality.

## Review by Q64

I read the item source, ILO Expose VIII, Lemma 3.2.9 and the monomial-basis normalization discussion on printed page 104, and the full statements of `lem-trf-fg-torsionfree-group-free`, `lem-trf-rational-cone-dual-finite`, and the new weighted obstruction node. The first item step uses the finite-basis statement exactly for the finitely generated torsion-free subgroup H and uses the rational-cone node exactly for its finite rational half-space description. The second step uses only the new node's stated negative-weight obstruction. The finite-support hypotheses ensure every term in the monic equation lies in k[H]. I tested P={0}, P=N, P=2N, a negative monomial x=e^{-1}, and a sum with both positive and negative exponents; the conclusion behaves as expected. Mathlib searches for the item and the new node were run with LeanFinder, Loogle, grep, and LeanSearch and are recorded in the node and searches log; Mathlib supplies only degree inequalities and generic integral-closure APIs, not this support theorem. No duplicate blueprint or DAG statement was found. No Lean files were written or compiled.
