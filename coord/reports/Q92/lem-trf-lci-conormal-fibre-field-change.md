# Worker report — Q92

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-lci-conormal-fibre-field-change.json`: statement, split into eight steps; no exact Mathlib match for the full localized conormal-fibre statement. No statement change.
- New nodes: none. New Mathlib leaves: none. Existing Mathlib leaves supply every substantive algebraic input.
- `citations.json`: one verbatim statement quote for every node used by every numbered step.
- `searches.jsonl`: actual search-command records; the item's `mathlib_searches` retains the inherited searches and appends this run's searches without inventing or rephrasing their query text.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact id and `(blueprint: lem-trf-lci-conormal-fibre-field-change)` tag, and by conormal, field-change, fibre, and 00SI phrases. No project declaration stating the item was found. The read-only upstream source and `dag/lean_names_upstream.json` supply no finished exact declaration either. No Lean code was written or compiled.

## WANTED

None: the source calculations are available locally.

## Findings and corrections

The item's statement is correct. Stacks algebra.tex Tag 00SI (`lemma-lci-field-change-local`, lines 36204--36259) writes its comparison using I tensor the polynomial residue field; the quotient-conormal form is explicitly written in the proof of Tag 00SJ, lines 36339--36345. They agree because the primes in P and P_K contain the respective presentation ideals. I kept the complete statement, all prime contractions, arbitrary field extensions, the canonical map, and the finite-dimension conclusion.

The inherited Mathlib search verdict claiming that cotangent base-change hits concern only complexes was too broad: `Ideal.tensorCotangentEquiv` is indeed about ideal conormals. The fresh Loogle and grep searches found it at `Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:112`, with the pure-tensor formula at 120 and injectivity at 87; I read the file through its proof. The existing node `lem-weil-pbc-ideal-cotangent-flat-base-change-ring` already records this generic input and is reused. It is not the entire item: the polynomial/quotient algebra structures, localizations, residue fields, canonical composite, and dimension clause still require the argument below. The other search hits give module localization/tensor ingredients or cotangent complexes, not this full statement.

I initially considered a generic prime-localization fibre-comparison node. On self-review its maps are two explicit fraction/tensor maps and elementary balancing identities, so I dropped that uncommitted draft and wrote the maps directly in steps 4--6. No clause of the item is moved to a new node. The abandoned draft is not part of this delivery.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for conormal, flat conormal base change, 0473, localized module, and 00SI found the existing conormal base-change leaf and the related global lci field-change item, whose proof is not used as an interface. `tools/blueprint_refs.py search 'conormal'` returned normal-bundle, normal-cone, purity-convention, and curve-differential definitions, not this fibre comparison; searches for `00SI`, `localized module`, and `conormal fibre field change` returned no equivalent blueprint statement. The nearest blueprint ancestor is `lem-trf-local-term-locality`; its existing historical `from`/`via` ancestry is preserved and `same_as` is empty.

## Route and tools

Read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current/local historical blueprint references. This is the existing historical local-algebra subbranch of `lem-trf-lci-field-change-local`, not a change to the curve/local-term argument. All off-unit inputs here are definitions or existing Mathlib leaves (presentation base change, faithful flatness under field extension, ideal-conormal flat base change, regularity/Noetherianity of a polynomial ring). They are generic algebra tools and require no replacement of a unit step. No SGA source is used. No unit or chapter record is edited.

## Review by Q92

I read algebra.tex Tag 00SI in full, the conormal quotient sentence in Tag 00SJ, morphisms.tex Tag 0473's affine proof, the module fraction definition Tag 07JZ and localization-at-prime example, and the source statement of each cited DAG node. The item is an ideal-conormal assertion, not a statement about Kähler differentials or the maximal-ideal cotangent space of a local ring.

Step 1 uses `lem-weil-pbc-presentation-base-change`, whose statement gives the base-changed generators and kernel, at the identity presentation with zero relations. Its tensor-factor swap is the explicit map on pure tensors. `def-weil-pbc-mv-polynomial-ring` states that homomorphisms agreeing on variables and coefficients agree, so the written inverse really identifies P tensor K with P_K. No arbitrary quotient is assumed finitely presented without justification: this step applies the presentation node only to P itself with zero kernel; the quotient presentation of C_K is already part of the item's hypotheses.

Step 2 uses exactly `lem-weil-pbc-field-extension-base-change-faithfully-flat` for a commutative k-algebra D=P and arbitrary field extension k to K. The node needs no finite/separable extension. `def-weil-pbc-faithfully-flat-ring-map` explicitly includes flatness. The P-algebra isomorphism of step 1 preserves the P-module structure, so its target P_K is flat via the actual coefficient map, not merely via some abstract k-algebra structure.

Step 3 applies `lem-weil-pbc-ideal-cotangent-flat-base-change-ring`, whose statement gives the canonical map, its formula, and its isomorphism under flatness. Its ideal J=IB is precisely I_K by definition; the flatness is step 2. The additional quotient-scalar identification is not taken from the proof of that node: it is proved by the two maps m tensor [b] to m tensor b and back. Changing b by a sum of multiples of gamma(i) changes the tensor by zero since I annihilates M=I/I². The tensor universal property in `def-weil-pbc-module-tensor-product` is exactly the quoted interface used to descend and check these maps. Thus C_K-linearity and the coefficientwise formula are checked, not assumed.

Step 4 uses only the localization and residue-field definitions in `def-weil-pbc-localization-at-prime`. Contraction of the prime makes every denominator outside q nonzero in L; fractions therefore define the displayed field map. Its kernel cannot contain 1. No separability or finite residue-field extension is required.

Step 5 uses the complete fraction equality criterion of `def-weil-pbc-module-localization` and the bilinearity relations/universal property of `def-weil-pbc-module-tensor-product`. Both directions of the maps are written; a localization annihilator is invertible in F (and respectively L), so the fraction equality relation is respected. This is a direct elementary calculation for the two modules, not a citation to a definition for an unstated exactness theorem.

Step 6 uses those same tensor relations. Both scalar-cancellation identifications and their inverses are explicit, and tensoring Theta is invertible because tensoring its inverse gives the inverse on pure tensors. The composite sends the presented conormal class to its coefficientwise image with the correct L scalar. Together with step 5 this checks the formula also for arbitrary localized fractions, and it makes the isomorphism canonical without choosing generators or bases.

Step 7 uses `lem-weil-pbc-polynomial-ring-field-regular-ring` only for its explicit Noetherian clause, and `def-weil-pbc-noetherian-ring` exactly for finite generation of I. Coefficients of an ideal expression reduce to C; fractions and tensoring preserve this given finite generating family. Thus the original residue fibre is finite dimensional. No unproved Nakayama assertion is needed here.

Step 8 is elementary finite-dimensional linear algebra: discard dependent vectors from a finite spanning family, and then extend the coordinate functionals using the tensor universal property. Applying them to a relation proves independence over L, including rank zero. This verifies the dimensions over F and L separately, rather than treating F and L as equal.

B--E audit: no new node, no duplicate, no relabelled clause; all statements used were opened and their actual interfaces are copied verbatim in citations.json. The proof uses no source's internal construction, no uncited non-elementary exactness claim, and no cycle through its parent. The original statement and blueprint ancestry are preserved. All eight steps are below 2000 characters (longest 882); the quotient and localization identifications have explicit inverses rather than a hidden comparison lemma.

Small cases checked against the formulas: I=0 gives zero conormal fibres; n=0 forces I=0 whenever a prime q_K exists (I=P gives C_K=0 and no prime). For C=k[x]/(x²) at (x), the conormal fibre is one-dimensional and remains so for any K. The identity extension gives the identity map. For k=R, K=C, C=R[x], and the prime (x-i) over q=(x²+1), contraction and the residue-field embedding give the same denominator calculation; the conormal is zero. Purely inseparable extensions in characteristic p are also covered since only field flatness and nonvanishing of denominators are used, never separability or reducedness. These checks exclude a hidden closed-point, algebraicity, domain, or reducedness hypothesis.

## Unfinished work

None within the assigned stage-1 split. The mandatory server dry run exited successfully: `OK (not pushed) deliver/Q92/lem-trf-lci-conormal-fibre-field-change at dfebd70a10: preflight passed`. This includes the server DAG and split checks. The delivery push follows this completed dry run.

