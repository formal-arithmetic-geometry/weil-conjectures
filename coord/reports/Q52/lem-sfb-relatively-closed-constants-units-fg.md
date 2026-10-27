# Stage-1 report: lem-sfb-relatively-closed-constants-units-fg

Group Q52; 2026-10-24. Direct delivery; no second worker and no subagents. Only the sandbox was written. No Lean, compiler, Lake or local DAG/preflight checker was run; no git command was run in the shared repository.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relatively-closed-constants-units-fg.json`: unchanged statement, now split into five proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-geometric-connected-component-surjective.json`: statement, unsplit; no Mathlib match. This isolates the geometric cover needed before doing any unit-group calculation.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-units-finite-valuation-map.json`: statement, unsplit; no Mathlib match. This isolates the integral algebraically closed case in its finite integer-coordinate form.
- `citations.json`: one verbatim statement quotation for each of the fourteen step/node citations.
- `searches.jsonl`: actual msearch.py records, including exploratory group-finiteness searches that led to reusing an existing node instead of making a third node.
- `report.md` and sandbox-only `write_split.py`.

Two new nodes; zero new Mathlib leaves. Neither new node contains a proof or proof dependencies.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag, relatively closed constants, Rosenlicht, global units, unit quotients and the geometric component input. The curve unit-power quotient results do not state the item, and the affine-line constants lemma concerns only the affine line. No exact project declaration was found.

## WANTED

None. All mathematical sources used are in the local Stacks checkout.

## Corrections and route

The item statement is precisely alternative (1) of Stacks 04L7 with nonemptiness and the scalar embedding explicit. I kept it verbatim. There is no statement dispute. The original item had no proof. Its parent already carried a reviewed scalar-field comparison split; I did not edit or re-prove the parent.

The proof follows 04L7's geometric connected component and scalar descent, and 04L6's finite component restriction argument. Instead of introducing a new theorem about subgroups of finitely generated groups, I retained the finite valuation-coordinate map visible in the proofs of 04L4 and 04L5, and reused `lem-weil-subgroup-finite-free-abelian-group-free`. The existing node states exactly the final subgroup conclusion. The two new nodes are smaller inputs: one concerns geometry alone and says nothing about units, the other concerns integral schemes over algebraically closed fields and says nothing about the non-integral component argument or descent of constants over the original field. Thus neither merely renames the item.

I read the chapter record and unit record, the current latest blueprint unit and its direct-images proof, especially paragraph (3). This item supports the inherited alteration/moduli/groupoid chain through 06FF and 04MK. The ancestor command returns `None`, as on the already reviewed parent; that inherited null ancestor is retained, with the exact source place and full via chain. There is no change to the chapter or unit route. The reduced induced closed-subscheme theorem is declared as a generic tool use in `split_report.tool_uses`; the subgroup result is already a Mathlib leaf.

## Searches and existing nodes

Before creating nodes I searched all `dag/nodes/` by Stacks tags 04L4, 04L5, 04L7, 04KZ and 038H, by unit/finiteness and geometric-component keywords, and by reduced-section detection. Blueprint searches were run for Rosenlicht, units, finitely generated abelian, subgroup finitely, 04L4, 04L5, 04KZ, normal proper, valuation units, geometric connected component and irreducible components finite. I opened the candidate statements, including the finite-separable descent nodes, geometric component-count base change, the separably closed valuation-field components lemma, and the projective-line component descent lemma. None states either new input.

All new-node Mathlib searches were made through msearch.py and copied from its actual results, with the exact query texts. Both new nodes have LeanFinder, Loogle, grep and LeanSearch searches, including a second natural-language phrasing. All services answered. Proper global-functions finiteness requires universal closedness and an integral source; it does not give the integral open-scheme unit theorem. Selmer-group maps concern a Dedekind fraction field and power quotients, with a different kernel. Geometric connected-component homeomorphisms require geometrically connected fibres, which the algebraic-closure projection need not have. Noetherian component finiteness alone does not cover the non-quasi-compact hypothesis here. Exploratory general subgroup searches were not turned into an unnecessary node.

## Not duplicates

lem-sfb-geometric-connected-component-surjective vs lem-sfb-relatively-closed-constants-units-fg: the former is the geometric component cover in the proof of 04L7; the latter is the unit-quotient finiteness conclusion and assumes reducedness and relative integral closedness, neither needed for the cover.
lem-sfb-geometric-connected-component-surjective vs lem-sfb-connected-reduced-scalar-field-uniqueness: that node compares two ground fields and invokes 04L7 only as a unit-group input; it provides no geometric connected-component cover.
lem-sfb-geometric-connected-component-surjective vs lem-sbc-components-finite-separable-descent: the existing node assumes finiteness of the geometric irreducible components and descends them to a finite intermediate field. The new node proves geometric finiteness from finiteness over k and gives surjectivity of each geometric connected component to X.
lem-sfb-geometric-connected-component-surjective vs new-lem-sbc-finite-field-closed-component-descent: the existing node also assumes geometric component finiteness and descends closed subsets after a finite extension; it does not give the cover of the original connected scheme.
lem-sfb-geometric-connected-component-surjective vs lem-sbc-generic-components-split: the existing node assumes finite type, rather than locally finite type with finitely many components, and gives a finite etale splitting extension rather than a chosen geometric connected component surjecting onto X.
lem-sfb-geometric-connected-component-surjective vs new-lem-sbc-closed-component-descent-topology: the existing topological lemma assumes a surjective map and inverse-image descriptions of irreducible components; it does not construct the geometric cover or establish geometric finiteness.
lem-sfb-geometric-connected-component-surjective vs lem-trf-sepclosed-valuation-geometric-components: the existing node starts over a separably closed residue field of a valuation ring and with a finite-type geometrically reduced scheme, and concerns geometric integrality of irreducible components; it does not cover arbitrary ground fields and locally finite type non-quasi-compact schemes.
lem-sfb-geometric-connected-component-surjective vs lem-trf-geometric-fibre-component-count-base-change: invariance of the already geometric number, possibly infinite, supplies neither its finiteness nor a surjective connected-component cover.
lem-sfb-geometric-connected-component-surjective vs lem-trf-geometric-components-projective-line-descent: the existing theorem assumes both fields algebraically closed and finite type, and its additional conclusion is descent of a projective-line isomorphism; it does not apply to the arbitrary-field projection used here.
lem-sfb-geometric-connected-component-surjective vs lem-sfb-group-local-minimal-prime: the existing theorem is about a group scheme's local minimal primes and its identity irreducible component, not connected components of an arbitrary scheme after algebraic closure.
lem-sfb-integral-units-finite-valuation-map vs lem-sfb-relatively-closed-constants-units-fg: the new node is the integral algebraically closed valuation input of 04L5/04L4; it does not address the item's connected reducible case or descent of constants over k. The item performs both arguments explicitly.

There were no existing nodes sourced from 04L4 or 04L5. The extra comparisons above include tags found anywhere in existing node text, not only their primary sources.

## Review by Q52

I read `varieties.tex`, Tags 04L7 (proposition-units-general), 04L6 (lemma-units-general-algebraically-closed), 04L5 (lemma-units-integral-finite-type-algebraically-closed), and the complete proof of 04L4 (lemma-open-in-normal-proper). For the new geometric node I also read 04KZ (lemma-galois-action-irreducible-components-locally-finite-type), especially (3), and 038H (lemma-separably-closed-field-irreducible-components). For the valuation node I checked the reduction to a nonempty affine open, its projective closure, finite dominant normalization, and the displayed integer-valued boundary map in 04L4. The stronger finite-coordinate formulation is what that proof actually constructs. No normality, properness or separatedness of the original T is assumed: those belong only to the normal proper model used after restricting to an affine open. The constants are still detected because all pullbacks are K-linear and injective on functions of the integral source.

For step 1, the geometric node explicitly gives every needed hypothesis of Y: nonempty, connected, reduced, locally finite type over the algebraic closure, finitely many irreducible components, and surjectivity to X. The algebraic-closure definition explicitly asserts existence. This does not assume that X_K is reduced or connected. For the new geometric statement itself, 04KZ gives finite geometric irreducible components, with 038H passing from a separable closure to an algebraic closure. Finite irreducible components make connected components open and closed by their finite intersection graph. Their maps to X have open image (field-extension projection, after identifying the topology of reduction) and closed image (integral projection restricted to a closed component). Nonemptiness and connectedness of X force each image to be all of X. Reduction and passage to an open subscheme preserve the locally finite type affine-coordinate condition. This is a genuine geometric input, not a unit-group theorem in disguise.

For step 2 I opened both cited statements. The residue-field definition gives the field homomorphism, and hence injectivity by the elementary inverse argument. Clauses (1) and (3) of the reduced induced closed-subscheme theorem identify sections vanishing in every residue field with the zero ideal on a reduced scheme: take the whole closed subset and the identity closed immersion. Thus the argument uses only the cited statement, not its proof, and does not falsely infer injectivity from mere topological surjectivity without reducedness. I used that same consequence on Y in step 4.

For step 3 I opened the reduced induced closed-subscheme theorem, the integral-scheme definition, and the locally finite type definition. Reduced irreducible components are nonempty and integral. Quotients of each finitely generated chart algebra are finitely generated, so each component satisfies the valuation node's exact locally finite type hypothesis without needing quasi-compactness or affineness of intersections. I read the new valuation statement back against the step: it supplies a finite coordinate set and a homomorphism with kernel exactly K^times for each integral component. Taking a finite disjoint union of the coordinate sets and forming the product of the actual maps is an elementary explicit construction, not an unstated group-finiteness theorem.

For step 4 the residue-field statement justifies equality of constants on nonempty intersections. The graph argument uses finiteness essentially: a union of a subcollection of the closed components is closed, and the two unions form a clopen partition if the graph is disconnected. Connectedness of Y, from step 1 and its cited definition, forbids it. Reduced-section detection from step 2 then gives equality as a section, rather than merely pointwise equality on the underlying space. Conversely each constant lies in every coordinate kernel. This routine connected-cover argument is elementary and was kept as a step instead of made a new node.

For step 5 the algebraic-closure definition gives a nonzero k-polynomial for lambda; dividing by its leading coefficient is valid because k is a field. Pullback preserves coefficients and evaluation, and the already proved injection alpha converts its vanishing into a monic equation in A. The integral-closure definition says exactly that such an element belongs to k. Its being a unit excludes zero, so the kernel is k^times, not a possibly larger constant field. The quotient injection is explicitly defined by [u] -> h(u). The existing subgroup theorem states that an abelian group isomorphic to a subgroup of Z^J is free of finite rank, exactly what is used. Choosing representatives of a finite basis gives units as required, including the zero-rank case.

I checked small cases: T=Spec K and any proper integral T have the zero-coordinate map when all units are constant; G_m gives its exponent coordinate; affine space has no nonconstant units; singular integral schemes are covered by normalization without assuming they were normal. For X consisting of connected reducible components meeting in points, the overlap evaluation forces their constants to agree. For X=Spec k the quotient is trivial and the empty basis suffices. Imperfect k is allowed: reduction after algebraic closure is necessary and retained. A disconnected X would allow independent constants, explaining the connectedness hypothesis rather than silently omitting it. Non-quasi-compact X with finitely many irreducible components is retained throughout; no global Noetherian hypothesis or affine intersections were introduced.

I checked delivery-errors B to E against the final files: self-contained statements with definition references and explicit source labels; no proof in new nodes; no duplicate or clause relabel; all non-elementary inputs cited; exact statement quotations in citations.json; no proof-to-statement substitution; no cycle through the scalar-field uniqueness parent; no changes to locked targets; correct reduced scheme and scalar rings at every step. Every proof step is below 2000 characters. The existing Mathlib subgroup leaf is reused rather than recreated. No SGA source is cited.

## Unfinished work

None within the authorized one-level split. The two new statement-only inputs remain unsplit for later workers, as required.

Final self-review refinement: the geometric node explicitly defines a connected component as a maximal nonempty connected subset and cites the affine-spectrum definition for Spec K; the corresponding quotation was regenerated. The statement and proof of the item are unchanged.
