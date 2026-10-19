# Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-local-dimension-formula.json — item, split statement; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-affine-dimension-inequality.json — new statement-only algebraic inequality node; no Mathlib match.
- citations.json — verbatim citations for both proof steps.

Attachments: none.

WANTED: none.

The item has no sorry-free declaration in /home/ubuntu/weil-src-slopmaster2/WeilConjectures; the source search found no declaration tagged (blueprint: lem-trf-local-dimension-formula). The statement is unchanged and agrees with Morphisms Tag 02JU, including the dominance, integrality, local finite type, locally Noetherian, and residue-transcendence terms.

## Not duplicates

lem-trf-affine-dimension-inequality vs lem-exc-dimension-formula-universally-catenary-finite-type-domain: both use the Stacks dimension-formula family, but the new node is the inequality for an arbitrary Noetherian domain base and does not assume universal catenarity, while the existing node states equality under universal catenarity and includes a different general finite-type domain formulation.\n\nlem-trf-affine-dimension-inequality vs lem-exc-weakly-etale-normalization-dimension: the existing node is only the finite integral-closure-in-the-same-function-field specialization for a universally catenary local domain and maximal ideals, whereas the new node is the general finite-type domain height inequality for arbitrary primes and does not assume universal catenarity.

## Review by Q25

I read the item node, the unit dag/units/sk-i-curve-zero.json, and chapter dag/chapters/sec-trace-formula.json, then checked the imported statement against literature/stacks-project/morphisms.tex, Tag 02JU (the displayed local dimension inequality) and its proof sentence referring to Algebra Tag 02IJ. I also read the full algebra statement and proof context at Tag 02IJ in literature/stacks-project/algebra.tex.

Step 1 is the affine reduction. I checked that a nonempty affine open in an integral scheme contains its generic point, that the affine point correspondence is exactly the statement of lem-weil-pbc-affine-open-spec-points, and that the stalk is the indicated localization by lem-weil-pbc-affine-open-stalk-localization. The finite-type ring map is precisely the pair-of-affines conclusion of lem-weil-pbc-lft-affine-pairs. Integrality supplies domain coordinate rings and dominance supplies injectivity of the map on the chosen generic-containing charts; these are the only hypotheses used.

Step 2 applies the new algebra node to those domains and primes. I checked its statement against Tag 02IJ and tested the edge cases R=S, a polynomial algebra over a field, and a finite algebraic extension. The existing lem-weil-pbc-localization-dimension-chains-below-prime states exactly the height interpretation needed for the two local rings. The residue-field identifications use the affine stalk localizations and def-weil-residue-field; the generic-point/function-field identifications use def-sc-generic-point and the stalk definition, and the transcendence-degree terms use def-kun-transcendence-degree. Every cited statement was opened and matched to the quoted text in citations.json.

I ran the required Mathlib searches for the item and for the new algebra node with LeanFinder, Loogle, grep, and LeanSearch. They found only general local finite-type, height, and transcendence-degree facts; no exact scheme-level or algebraic dimension formula. No Lean files were written or compiled.
