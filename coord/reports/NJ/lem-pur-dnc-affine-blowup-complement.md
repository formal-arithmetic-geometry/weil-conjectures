Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-dnc-affine-blowup-complement.json`: item split into seven proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for all cited nodes in every proof step.

Attachments: none.

WANTED: none.

What was wrong or incomplete in the imported item: the item had the correct statement but no proof. I supplied the affine Rees-chart calculation. The statement itself was not changed. The existing Stacks-based definitions and chart lemmas were used rather than duplicating them.

What I could not finish: nothing. The Mathlib searches found only ordinary Rees-algebra and Proj-chart primitives; no theorem states this strict-transform complement, so the item remains a split statement node.

## Review by NJ

I read the item statement, its source entry in `literature/stacks-project/divisors.tex` (Tags 0804 and 080D), the current blueprint ancestor `def-pur-dnc-section-family`, and the affine blow-up definitions in `literature/stacks-project/algebra.tex` (Tag 052Q). I also checked the source and statements of every cited DAG node: the global blow-up/glue/local-model definitions, the affine chart and chart-cover propositions, the chart-map and homogeneous-fraction definitions, the chart-ring definition, the strict-transform and schematic-closure definitions, the scheme-theoretic-image definition, the open-restriction image lemma, and the standard-open Proj proposition. Each citation quote in `citations.json` is the complete statement of the node it cites.

Step 1 uses the global blow-up local model and the affine chart and cover statements to obtain the (t)-chart and the (f_i)-charts. The chart-map and homogeneous-fraction statements justify the fraction coordinate, while the chart-ring statement identifies (A[J/t]) with (R[t,I/t]). Step 2 is elementary coefficient comparison in the polynomial ring and was checked also when (R_f=0). Step 3 uses the definitions of strict transform, scheme-theoretic closure and image, together with the open-restriction image lemma, to compute the closure chartwise; the required immersion is quasi-compact and quasi-separated because it is a finite union of principal opens.

Step 4 checks the (t)-chart directly: all generators of (J=(I,t)) become multiples of (t), so the center is (V(t)), and the strict-transform open part is empty. Step 5 checks the (f_i)-chart with (C=R[I/f_i]subseteq R_{f_i}): the center is (V(f_i)), the open part has ring (R_{f_i}), and the kernel of (C[v]	o R_{f_i}), (vmapsto0), is exactly ((v)). Step 6 uses the standard-open Proj identification and the chart fraction formula to identify the overlap with (D(v)). Step 7 uses the chart cover to conclude that removing the strict transform is exactly the (t)-chart, over (operatorname{Spec}R[t]).

I tested the argument on (I=0), (I=R), nilpotent and zero-divisor generators, and the zero ring. In each case the subalgebra and kernel descriptions still give the asserted empty or principal strict-transform chart. The seven steps are all under 2,000 characters, and no hidden lemma was moved into a new node. The Mathlib searches were run with `msearch.py` for LeanFinder (two phrasings), LeanSearch, Loogle and Mathlib grep; they returned no theorem for this calculation, while identifying only generic Rees/Proj primitives. The server `check_dag` preflight passed with no introduced finding.
