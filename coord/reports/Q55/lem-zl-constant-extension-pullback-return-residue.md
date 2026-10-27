# Q55 stage-1 delivery

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-constant-extension-pullback-return-residue.json`: item, split into six proof steps; no exact Mathlib match.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is sandbox-only preparation material.

No new nodes and no new Mathlib leaves. The statement is unchanged. The statement-dependency list additionally names the existing constant-extension datum defining the distinguished sheet and geometric-fibre identification.

## Attachments

None. Searched `lean/WeilConjectures` for the blueprint tag and constant-extension/Weil terminology. Read RealSheaves/ConstantExtension.lean and the relevant descriptions in FundamentalGroup/ConstantExtension.lean and RepresentationTheory/GeometricConstituents.lean: these concern Weil groups and representations, not the full actual-heart statement for arbitrary constructible sheaves. ConstantExtensionPresentationLift.lean concerns presentations of finite constant quotient sheaves and is unrelated. No attachment is claimed from either Mathlib or a partial project theorem.

## WANTED

None. The proof is explicitly agent-written, expanding the obtained Deligne source with existing DAG tools.

## Problems found and corrected

The imported item had no proof. Its assertions are consistent with Deligne II (1.1.8), Definition (1.1.10) and the following paragraph. The source gives the change-of-finite-base assertion tersely; it does not give the actual integral-normalized common-stage comparison or the lcm formula. These are supplied here, rather than pretending the terse source is a proof of those details. No statement dispute or unit-route departure was found.

The essential distinction is that the actual pullback has coordinates P^i M, not constant coordinates M. The latter appear only after applying the explicit cyclic normalization, whose comparison maps are the ordered initial products of the Weil map. The proof preserves that distinction. It also distinguishes the residue field of a tensor-product prime from its ring quotient until finiteness proves the quotient is a field.

## Unfinished work

None for this one-level split. Existing cited nodes retain their independent queue states. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Searched the DAG for the item, cyclic return, sheet coordinates, compositum/lcm, finite-field Frobenius and fibre-product residue fields. Blueprint searches `constant extension`, `compositum`, `finite subfields`, `pullback return`, `residue compositum` and `cyclic return` found no imported node stating this full item. The general sheet-coordinate and cyclic-return nodes are reused rather than re-created. The parent constant-extension-heart equivalence depends on this item and is not cited, avoiding a cycle. The separate return-local-operators node and general local-pullback theorem are not used to prove this item.

## Review by Q55

I read the full B–E sections of delivery-errors.md against the final node, as well as the worker brief, stage-1 rules, GOAL, the three blueprint levels in SETUP, the chapter/unit records and the current main-20261015 proof of thm-zl-real-mixed-by-curves. The split supplies the constant-extension restriction used in the first and later descent paragraphs without replacing the human unit route.

For the source, I read Deligne II pp.151–153: (1.1.8) explains finite-residue-extension Frobenius powers, (1.1.10) defines compatible Weil action, and the paragraph on p.152 uses the disjoint geometric sheets to identify finite-base interpretations. I also read Stacks schemes.tex Tag 01JT, label lemma-points-fibre-product, including the final residue-field sentence and the construction of the factor maps; fields.tex Tag 09HY, label section-finite, for finite fields; and Tag 09I1, label lemma-finite-Galois. Morphisms Tag 01TB was read as a cross-check of the closed-point input, but is not silently substituted for the cited closed-point theorem. For all the steps below I opened the cited JSON statements, not just their proof texts.

Step 1 uses exactly the sheet-coordinate node's h_i, semilinear heart equivalences, H^m j_0 identity and retained normalized compositors. The existing constant-extension datum supplies the actual geometric-fibre identification. The ind-Weil definition supplies the normalized equivariant pullback square, and the integral-composition theorem supplies the associativity identity needed to recognize its arrows. Its hypotheses hold because all schemes are in characteristic p and ell differs from p. The projections give pi h_i=g_X^i, so the actual arrows are P^i theta. The argument does not assume the sheaf or its Weil isomorphism has a chosen integral lattice; it uses the prescribed comparisons on rationalized integral representatives already specified by the cited interface. The sheet-coordinate statement explicitly retains these comparisons at common coefficient stages.

Step 2 uses the cyclic-return theorem's product formula and underlying exactness assertion, the constructible-heart definition's abelian assertion, and the sheet-coordinate theorem's exact autoequivalence P. The Weil-sheaf definition supplies the precise morphism equation. The source fixed-pair exactness assertion is obtained by applying the same cyclic theorem at cycle length 1, rather than applying a Grothendieck-category statement that incorrectly assumes all small limits and colimits in the constructible heart. Induction writes out why the unchanged carrier morphism commutes with the m-fold map. Exactness follows because the carrier functor is unchanged.

Step 3 uses the cyclic theorem's specified S and natural isomorphism with components r_i, then the sheet-coordinate equivalence's correspondence on morphisms. These statements explicitly give the last-arrow equation and naturality; no local equality of derived morphisms is asserted to imply a global equality. This gluing is the stated equivalence on disjoint sheets. It takes place before any direct image.

Step 4 uses lem-kun-closed-point-field(a), which says closed iff the residue extension over the base field is finite for finite-type schemes. I checked that X_{0,m} is finite type over both bases by its affine presentations. Thus kappa(z) is a finite set, and its embedded subfield kappa(x) is finite, making x closed by the converse. The fibre-product residue-field theorem gives exactly the fraction field of the selected prime quotient and compatibility with both residue maps. It does not yet claim that the tensor product itself is a field or split.

Step 5 is the only step marked elementary: a finite spanning set over a finite field makes the tensor ring finite; multiplication by a nonzero element of its prime quotient is an injection of a finite set and hence surjective. This proves it is a field. Sums of products of the two factor images then show generation. There is no hidden general tensor-compositum lemma and no new node restating a clause of the item.

Step 6 uses the finite-field Galois/Frobenius Mathlib leaf for the orders R, d and m on the actual residue-field images. A basis count verifies [k_m:k_0]=m, so the order is m under the specified inclusion. Restricting a power of sigma proves d and m divide R. The reverse divisibility follows because sigma^lcm fixes both generating fields and therefore every element of the quotient. This proves equality of degrees without an unproved identification of abstract copies of finite fields. The tower-degree leaf explicitly supplies R=fd. The gcd/lcm rearrangement is integer arithmetic for positive d,m; the cardinality identity is the direct basis-coordinate bijection. I read the relevant Mathlib Frobenius-order and bijection declarations in Finite/Basic.lean and verified the leaf states the required order assertion.

For B, no new statements need independent self-containedness or search records; the existing statement keeps all coefficient conventions and hypotheses. Every proof step has source and explicit uses, and there are no double-escaped TeX commands. For C, citations.json copies the cited statements verbatim and every non-elementary input is named; the off-unit integral-composition, residue-field and closed-point tools are declared in split_report.tool_uses with their limited role. For D, the proof carries the actual coordinate and Frobenius-order arguments and adds no clause-restatement nodes. For E, I checked small cases: m=1 gives theta and the identity comparison; d=1 gives f=m; d=m gives f=1; d=2,m=3 gives R=6,f=3; d=2,m=4 gives R=4,f=2, illustrating that f need not equal m. Empty schemes make point statements vacuous, zero carriers satisfy all formulas, and neither disconnectedness nor nonlissity affects any step. No step exceeds 2000 characters and no hidden auxiliary comparison was retained as a long step.

The actual search commands and results are retained in searches.jsonl and appended to mathlib_searches. The first semantic phrasing concerned Weil pullback return; a second concerned finite-field tensor-quotient degrees. Loogle's unknown identifier Functor.iterate is recorded in its result, not treated as evidence by itself. The semantic hits about scheme-module pullbackComp and tensor products were read in Mathlib: they do not state this common-stage Weil-heart/residue-degree conjunction. The finite-field Frobenius hit is used through its existing leaf. No new Mathlib match is claimed.

Initial server review_split passed. Final dry run and delivery results are recorded by the required delivery command.
