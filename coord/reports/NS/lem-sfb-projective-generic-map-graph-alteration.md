# Stage-1 report: lem-sfb-projective-generic-map-graph-alteration

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-generic-map-graph-alteration.json: statement, split; seven proof steps, using existing nodes only. Mathlib verdict: no exact match or one-line specialization.
- citations.json: 22 entries, one for every step/node pair, containing verbatim statement excerpts.
- searches.jsonl: actual search-command records; report.md: this report.

## Attachments

None. Searched the project source under lean/WeilConjectures by the exact blueprint id and by graph closure and generic-fibre notions. The partial-section graph results in Mathlib/AlgebraicGeometry/Pullbacks.lean concern open-domain partial sections and their scheme-theoretic images; none states this item with its prescribed reduced closure and exact generic field fibre. They are not an attachment.

## WANTED

None. The proof is an agent assembly from the local Stacks sources; it does not claim that a single Stacks lemma proves this statement. No SGA route is used.

## What changed and what was wrong

The imported item had a complete statement but no proof. Its statement and statement dependencies are unchanged. The supplied normality and separability assumptions are retained; the graph argument does not need to exploit them. I did not introduce a lemma for the conclusion or move a clause into a new node. No new nodes or Mathlib leaves were necessary.

The proof computes the affine reduced-closure ring R/ker(R→L), then uses A⊆B⊆Frac(A)=L to identify both the function field and the entire generic fibre. It assembles properness and obtains dense-open finiteness from the existing generic-finite-neighbourhood statement. The residual topological-fibre assertion is supplied by def-pc-scheme-fibre, whose statement actually contains the homeomorphism; I do not use the fibre-product universal property as evidence for that topological fact.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None for this chain. I retained the inherited from/via data and the precise place through stable-pointed-generic-extension. The local blueprint direct-image proof and the item's inherited alteration route were read. Nothing changes a unit or chapter route. Whole-blueprint searches for graph closure, reduced closure, generic map and generic finite found no equivalent statement (the generic-map results concern Nagata valuation lifts, and the generic-finite result concerns constructibility of a finite pushforward). The item's same_as remains [].

## Mathlib searches

Ran msearch.py for the item with leanfinder (two different formulations), leansearch, loogle and grep, recorded exactly in searches.jsonl and appended to mathlib_searches without deleting the inherited searches. All services answered. The semantic hits are RationalMap.ofFunctionField, its recovery equation, residue-point maps and function-field declarations. Read Mathlib/AlgebraicGeometry/Birational/RationalMap.lean:516–523: these produce a rational map and recover its generic restriction, without the reduced graph closure, the proper surjection or the exact scheme fibre. The old RationalMap.lean path is a deprecated re-export of this file. The closure hits in the grep and Loogle searches concern ideal sheaves, topological closure, and local morphism-property closures. They do not state the item. This is several arguments, not a one-line specialization of those hits.

## Tool uses

The split_report.tool_uses records generic tools outside this unit: reduced induced closed subschemes, affine function-field fractions, projective-implies-proper, finite-type-over-Noetherian and generic-finite-neighbourhood. These implement the prescribed graph-closure and alteration construction; they replace no step of the unit route. Other cited morphism and affine-fibre-product results are Mathlib leaves, and definitions are used only through their written clauses.

## Review by NS

I read delivery-errors B–E in full and checked the delivered node against them. There are no new nodes to check for duplicate tags, unsupported notions, statement-only shape, or disguised restatement. The item has no statement correction. Its original source names closedness of an algebraic residue point, but the direct affine calculation makes that intermediate closed-point lemma unnecessary; it is not silently used. I read Stacks schemes.tex Tag 01J3 (statement and affine radical-ideal construction), Tags 01I4 and 01JQ (affine pullbacks), Tag 01K1 (topology of a fibre); properties.tex Tag 01ON (integral iff reduced irreducible); morphisms.tex Tags 01RV and 01RW (generic stalk/function field), Tag 01T6 (Noetherian finite-type source), Tags 01WC, 01W4, 01W5, 01WN and 01W3 (properness inputs), and Tag 02NW (all four clauses and the shrinking hypotheses). I also read schemes.tex Tag 01HV for the stalk at (0). Each source is available locally.

Step 1 uses the reduced-induced-subscheme statement for its radical-ideal description and reducedness, the integral-scheme definition for its explicit equivalence with reduced irreducible nonempty, and affine-spectrum for the prime kernel and ring-map correspondence. Its factorization is an actual quotient factorization, rather than an inference from set-theoretic containment alone. The common local quotient maps agree on overlaps, giving j_T. The irreducibility argument is written out.

Step 2 uses lem-sc-integral-function-field-affine-fraction, which explicitly applies to arbitrary integral schemes, not just curves, and def-sc-function-field's final general-scheme clause. The affine open of N is nonempty, and the affine open of T contains x_T; both schemes are integral. The map A→B→L is the specified generic map j, so it is injective and its fraction-field identification is the given one. The two inclusions prove Frac(B)=L without an extra unproved birationality assertion. This also verifies the specified K-structure, not merely an abstract field isomorphism.

Step 3 uses the same affine-fraction statement on every nonempty affine open of b^{-1}W and the affine-spectra fibre-product statement, including its projection equations. Such opens all contain x_T, so their evaluations embed in L and contain A. The multiplication map and the inverse 1⊗λ are written out: sc=a forces c⊗λ=1⊗aλ/s. Thus the scheme charts of the generic fibre are Spec L with the correct structural projection; the chart inverses are restrictions of the very same map j_T. They glue to inverse global maps. This is a short computation from the cited statements, not an unstated theorem that closure commutes with arbitrary base change.

Step 4 uses only the defining projection equations of the fibre product to establish m j_T=a and b j_T=j.

Step 5 reads exactly what the three morphism lemmas say: projective M→Spec k is proper; arbitrary base change makes Q→N proper; the closed-immersion-proper statement includes properness of the composite with i. The proper definition gives a closed underlying image. That image contains the generic point by b j_T=j, hence is N. This proves surjectivity without assuming the image of every dense subset is dense.

Step 6 uses finite-implies-proper on q (which is actually finite), proper composition on q and b, and the proper and finite-type definitions for finite type and quasi-compactness. The quasi-separated definition is checked directly: a separated diagonal is a closed immersion, and the cited closed-immersion definition supplies affine inverse images Spec(R/I), which are quasi-compact. No unrelated quasi-separatedness theorem is assumed.

Step 7 uses fibre-product universality for associativity, the given generic fibre of N/S and the calculated generic fibre of T/N. The scheme-fibre node explicitly identifies the topological fibre with the scheme fibre. S is Noetherian by the existing finite-type-over-Noetherian node applied to Spec k; the field case is verified directly. The generic-finite-neighbourhood node requires a Noetherian target, quasi-compactness, quasi-separatedness, local finite type and finite set-theoretic fibres at every component generic point. S is integral, so there is just one such point; its fibre is the singleton Spec L. Every hypothesis is present. Its conclusion is exactly finiteness on the inverse image of a dense open V.

For C4 I opened every cited node's statement and supplied a verbatim quote for every step/node citation. For C1 I checked that the remaining arguments are quotient factorizations, elementary topology, explicit tensor identities, or universal-property equations, with no hidden existence or comparison theorem. The coordinate calculation and each proof step are below 2000 characters (largest 975). The elementary flags occur only on those explicit short arguments.

Small cases checked: S=Spec K and N=Spec L give T=Spec L even when the original point in M has a smaller residue field, because the N-projection embeds L; M may be nonreduced or reducible, since taking R/ker(R→L) removes precisely the kernel and makes a domain; dimension zero is included; L=K gives a proper birational modification; M empty admits no a, so no unsupported existence assertion arises. Over a positive-dimensional S, additional special-fibre components or points of T do not affect the generic localization calculation. The proof neither assumes that a singleton fibre is automatically reduced nor that a topological factorization is automatically a scheme factorization.

The standalone server review_split check passed with zero new nodes. The final delivery dry run will run both DAG and split checks again on the packaged overlay.

## Unfinished work

None within this stage-1 item. No Lean files were written, no compiler or Lake tool was run, and no repository or launcher files were modified.
