# Q09 — lem-sfb-pulled-torsor-normalization-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-pulled-torsor-normalization-model.json`: statement node, now split in seven steps; no full Mathlib match.
- `citations.json`: fourteen verbatim citations for the seven proof steps.
- `report.md`: this report. Search command results are retained in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written and no compilation was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, pulled torsors, and torsor/normalization combinations, then read the existing `FieldTorsorGaloisComponents.lean` interface. Its declaration gives the field-components input, not the normalization statement. The related Cartier/stalk/root normalization declarations specialize to DVRs or effective Cartier centres and do not attach this arbitrary normal-domain result.

## WANTED

None. All sources needed are already in the read repository.

## What was corrected

The item was statement-only and unsplit. Its statement, statement dependencies and source remain unchanged. No statement dispute was found. The proof now distinguishes normality from integral closedness in the total ring of fractions, proves that the generic algebra really is that total ring, and proves both inclusions in the normalization equality inside the actual generic algebra. This avoids replacing the required specified structural comparison by an abstract isomorphism. Nonempty field-factor families use the item's explicit surjective, nonempty-fibre torsor hypothesis.

The proof is marked agent-written: ILO IX Proposition 2.1(ii) explains the normalization comparison on printed pages 133–134 (PDF pages 139–140), but does not itself prove this complete general ring-theoretic formulation. Its surrounding Kummer and log-regular statements are not used as black boxes. The algebraic proof uses the existing DAG statements for Stacks 032L, 033C, 034M and 0307, together with the existing torsor inputs. It does not use the SGA reference appearing in the ILO proof of essential surjectivity.

## Unfinished work

None for this one-level split. Existing cited unsplit dependencies remain the responsibility of their assigned workers. No new statement-only nodes were needed.

## Not duplicates

No new nodes. Before deciding this, searched all DAG nodes by tags 032L, 033C, 034M, 0307 and keywords for normal finite etale algebras, total fractions and integral closure. Whole-blueprint searches `integral closure`, `torsor`, and `normalization` located existing notions and the weaker weak-etale integral-closure result. The item is not a duplicate of that result: it additionally identifies the actual pulled torsor, Galois field factors, their quotient maps and degrees, finite normalization without excellence, and the structural restriction isomorphism. `blueprint_refs.py ancestor` reports no imported ancestor for this added input, so its inherited null ancestor and precise from/via chain are retained, with `same_as: []`. No chapter or unit file changes.

## Mathlib search reading

Read and retained the item's inherited five recorded searches and their returned names. Ran four fresh searches through the mandated msearch command, with exact queries and actual summaries appended to `mathlib_searches`: LeanFinder on finite torsor normalization over a principal open; Loogle `"IsIntegralClosure", "Etale"`; the torsor/integralClosure regex grep; and LeanSearch on finite etale normalization and generic fibres. All four services answered successfully. The two natural-language queries provide different formulations. LeanFinder returned fraction-field and integral-closure localization ingredients; Loogle and grep returned no hits. LeanSearch returned `Algebra.Etale.iff_exists_algEquiv_prod` and related formally-etale results, and `Ring.NormalClosure` interfaces. Read `Mathlib/RingTheory/Etale/Field.lean:271` (finite separable fields, without the torsor Galois/degree and normalization comparison clauses), and `Mathlib/AlgebraicGeometry/Normalization.lean:46` (definition of a normalization diagram, not the required theorem). The full item is therefore not a Mathlib leaf. Existing nodes already record the integral-closure finiteness and localization matches.

## Review by Q09

I read ILO IX Proposition 2.1 and its proof on printed pages 133–134, especially the paragraph identifying a standard Kummer cover with the normalization of its restriction. I read Stacks `algebra.tex` labels `lemma-Noetherian-normal-domain-finite-separable-extension` (032L), `lemma-normal-goes-up` (033C), `lemma-normal-ring-integrally-closed` (034M), `lemma-integral-closure-localize` (0307), `lemma-localize-normal-domain` (00GY), `lemma-finite-is-integral` (00GK), and `lemma-etale` (00U2), and `schemes.tex` label `lemma-fibre-product-affine-schemes` (01I4). For flat torsion-freeness I read `more-algebra.tex` label `lemma-flat-torsion-free`, immediately before the valuation-specific lemma 0539: the former applies to every domain, as our cited node requires. I also read the current blueprint unit and its recorded unit/chapter route. This is the existing finite-cover normalization subargument below its coefficient finiteness step, not a replacement for the unit route.

Step 1 uses exactly the finite morphism definition's affine and module-finiteness clauses, the base-change torsor lemma's cartesian torsor, and the affine tensor base-change lemma's singleton case. I opened each cited node and checked that its statement includes these assertions, including the actual structural map. The tensor association is written on pure tensors, with inverse and invertible-denominator justification; it is not assumed to identify unspecified isomorphisms.

Step 2 uses the field-torsor lemma over both K and E. Its statement supplies all the Galois and degree-divisibility claims and an isomorphism over the given field. The finite affine coproduct-spectrum node supplies exactly the product-algebra interpretation with coordinate maps. The proof then writes the idempotent refinement, including the unique j, surjectivity of the resulting factor quotient and its E-linearity. This is an elementary consequence of the cited decompositions, not a new field base-change theorem. The nonempty fibres ensure that both products have nonempty index sets; no connectedness of P is used.

Step 3 uses localization of a normal domain to obtain A' and its precise fraction field E, then the etale-algebra-flat node and the flat-domain-torsionfree node. Their statements really apply to these affine rings and give injectivity of nonzero base multiplication. The explicit fraction-zero argument proves T injects into D. For a regular element t of T, clearing a base denominator proves injectivity of its action on D; in the finite product of fields from step 2 this makes t a unit. This proves the total-fractions assertion without an uncited minimal-prime or generic-flatness theorem.

Step 4 cites the etale-over-normal-ring normality node and the normal-ring-integrally-closed-total node. I checked the first assumes only etaleness and normality of the base, and the second is for normal rings, not just domains. Thus disconnected T is allowed. Step 3 is what permits using the second statement with our actual D.

Step 5 applies the 032L node factor by factor with Noetherian normal base B and finite separable extension F_a/E. Every hypothesis is present; separability comes from the field-torsor node. No excellence or perfectness is inserted. Finite-product module generators and the product of finitely many monic annihilating polynomials establish the remaining assertions directly. This is not a hidden finiteness theorem for arbitrary algebraic extensions.

Step 6 uses the localization node's actual image equality for B inside D and powers of f, not only existence of an abstract normalization isomorphism. Injectivity of R into B and f nonzero justify that f is invertible in D. The finite-algebra-integral node supplies exactly T integral over A'. The reverse inclusion needs no transitivity theorem: the very same monic polynomial over A' is a monic polynomial over T, and step 4 applies. This gives the stated equality as subalgebras.

Step 7 is a routine application of the existing affine base-change statement and the explicit fraction formula. It checks the structural map b/f^m on both sides inside D. This is why the conclusion is the actual restriction isomorphism over U_B.

I checked B–E of delivery-errors against the files and sources. No new nodes, hollow constructions, restated clauses or circular citations were introduced. All thirteen distinct proof dependencies are named in the steps, and each of the fourteen citations quotes the cited node's statement verbatim. Generic tools from other units are declared in split_report.tool_uses with a reason specific to their application. Every step is shorter than 2000 characters (maximum 1089); no hidden comparison is left behind the words “transport” or “standard”.

Small cases checked: G trivial gives S=A, T=A', D=E and C=B; a split torsor gives the corresponding finite products throughout; f a unit gives C=T immediately; R=B with a nonsplit Galois torsor gives the usual finite separable normalization; extension E containing a generic Galois field can split L_j tensor E further, and the coordinate-idempotent argument still selects maximal quotients with the right E-structure. Domain hypotheses exclude the zero ring; surjectivity excludes an empty torsor, so the nonempty products are valid. None of these checks revealed a statement error. The final dry run result is recorded below after it exits.

## Validation

Required server dry run exited 0 and printed `OK (not pushed)` at commit `52945e21348`; preflight passed, including the DAG and split checks. The delivery contains no new nodes and no new Mathlib leaves.
