# Q16: lem-trf-lattice-torus-coordinates-action

## Files written

- dag/nodes/sec-trace-formula/lem-trf-lattice-torus-coordinates-action.json: item split, statement unchanged; ten proof steps. No new nodes and no new Mathlib leaves.
- citations.json: sixteen verbatim statement citations, one for each step/node pair.
- searches.jsonl: actual msearch results for the item; the node retains the original searches and adds these four searches.

## Attachments

None. Searched lean/WeilConjectures/ for the blueprint id, torus, monoid algebra, Laurent polynomials and coaction. The polynomial and Hopf primitives and single-variable Laurent helpers do not state the complete item; no project declaration supplies all clauses.

## Wanted sources

None.

## Problems found and changes

The item was statement-only, not a completed split. I retained its full statement, original search history, source and blueprint lineage. I replaced no unit route. ILO's sentence that the torus action naturally extends leaves the overlap compatibility implicit; Steps 4--6 now give the coaction, its denominator formula, invariant chart opens and gluing argument. Likewise Steps 8--9 supply both inverse maps for coefficient base change and the Laurent quotient instead of asserting an unnamed comparison. No statement dispute was found.

Read the newest blueprint locality node and proof in literature/blueprint/latest/, and the chapter and sk-i-curve-zero unit records. This is an inherited auxiliary toric-resolution branch, not a proposed new proof route for the contracting-local-term statement. Blueprint searches for monoid algebra, gluing morphisms, morphisms glue, torus, lattice, Laurent, and fibre product affine found no duplicate of the item. The two Laurent blueprint matches concern a single-variable definition and duality reciprocity. The generic lattice and scheme tools already exist in the DAG, so I created no replacements.

## Unfinished work

None for the stage-1 split. Cited statement-only nodes remain independent stage-1 obligations, as allowed by splitting one level.

## Not duplicates

No new nodes. Reused lem-trf-monoscheme-finite-chart-components for the canonical generic group; lem-weil-pbc-fibre-product-affine-spectra for tensor products; lem-weil-pbc-open-fibre-product for product chart opens; and lem-weil-pbc-scheme-morphism-gluing for existence and uniqueness. In particular I did not create nodes merely naming one clause of the item, a Laurent-coordinate reindexing, a tensor coefficient calculation or the finite presentation quotient.

## Review by Q16

I read ILO Expose VIII, Proposition 3.2.2, 3.2.4--3.2.5 and Lemma 3.2.12 with its proof on printed pp.103--104 (PDF pp.109--110). Proposition 3.2.2 explicitly constructs the realization and explains compatibility with monoid localization; 3.2.4 identifies the generic group torus and extends its action. The source's smoothness input motivates the explicit Laurent presentation, without using smoothness as an unproved substitute. I read the current item, all six statement-definition dependencies, and all four additional proof-node statements. I also read the Stacks source at labels lemma-fibre-product-affine-schemes (01I4), lemma-fibre-product-affines (01JQ), lemma-open-fibre-product (01JR), and the sheaf gluing mapping property (00AN), together with the existing scheme-gluing node's source information. No new node needs a separate source.

Step 1 uses no theorem: a basis gives unique exponent coordinates, so the two maps of finite sums are visibly inverse and multiplicative. The proof explicitly specifies multivariable Laurent polynomials over arbitrary coefficient rings, rather than using the field-only single-variable Laurent definition beyond its scope.

Step 2 uses exactly the affine fibre-product statement for the product/tensor identification, the affine-spectrum statement for the contravariant correspondence and its faithfulness, and the group-scheme definition for the diagrams. Each cited statement supplies that clause. The Hopf identities are actually computed, not taken from the name of a structure. Step 3 uses the same spectrum correspondence and group definition, and writes the coordinate formulas; no abstract Hopf-to-group equivalence is assumed as a theorem.

Step 4 uses the generic-stalk clause of lem-trf-monoscheme-finite-chart-components, which does state the canonical identification of each chart's group completion with the generic stalk. Its hypotheses hold: N is fine, torsion free, nonempty, connected, and has the stipulated finite cover. The affine fibre-product and spectrum nodes give the chart morphism. I verified no dependency from this cited node back to the item: its statement and proof dependency lists do not contain the item. The exponent calculation gives both action identities locally.

Step 5 uses only the realization definition's localization gluing. It writes the image of the inverse monomial and checks why an action preserves each basic open, which is necessary before gluing. Basic monoid opens refine overlaps by the monoid-spectrum definition; affine scheme intersections need not be affine and are never assumed so. Step 6 cites open fibre products for the induced open covers and scheme-morphism gluing for existence and equality. The gluing node states existence and uniqueness for arbitrary open covers of arbitrary schemes, with no separatedness or finiteness hypothesis. This also justifies equality of the associativity and unit morphisms after the explicit local calculations, not a hidden equivariant descent lemma.

Step 7 cites open fibre products with the whole first factor and the chosen affine open of the second, and affine fibre products over Spec k. These nodes explicitly give the open inverse image and tensor product, including both projection formulas. Step 8 uses the latter projection formulas to check functoriality and writes the mutually inverse balanced tensor maps. It checks a general coefficient homomorphism R to R', so compatibility is proved even when an affine open inclusion is not a principal localization.

Step 9 is the explicit two-map proof of the quotient presentation. In the quotient the relations cancel opposite exponents; there is no integral-domain assumption or coefficient-field assumption. Step 10 applies exactly the finite-presentation-at-a-point definition and the finite affine cover criterion in the finite-type definition. It uses a finite affine cover only after the stated finite-type hypothesis on Y, while the arbitrary-base projection assertion remains only locally of finite presentation. No assertion that arbitrary Y is quasi-compact is made.

I tested r=0 (the group algebra and presentation reduce to k and R), r=1 with negative exponents (the coaction denominator and inverse-coordinate formulas agree), a nonsaturated chart P generated by 2 and 3 (the action still uses degrees 2 and 3, with no normalization hypothesis), empty Y (empty cover), and the zero ring R (empty affine scheme; all algebra maps still exist). Nonseparated N is allowed: the overlap-refinement and morphism-gluing proof uses no separatedness.

Against delivery-errors B--E: no new statement-only-node or duplicate issue arises; all proof citations were checked against statements and copied verbatim to citations.json; all non-elementary geometric transitions cite their existing nodes; no proof is transferred into a new clause-shaped node. Elementary steps are finite-sum, monomial, tensor-balancing or finite-generator calculations, with formulas supplied. Every step is under 2000 characters. The proof contains no SGA source and changes neither the statement nor the chapter/unit route. Generic off-unit tools are declared in split_report.tool_uses, with their exact roles, for maintainer review. This is my mathematical review of the split, not a claim that a local compiler or local DAG check ran; those are forbidden here.

## Validation

Required deliver.py --no-push exited successfully: OK (not pushed), preflight passed, dry-run commit 7abaa742295. The dry run ran the required server checks; no compiler or local check script was run. Delivery follows with the same node and citation contents.
