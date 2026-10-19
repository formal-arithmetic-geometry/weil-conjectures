# Q64: lem-trf-geometrically-irreducible-fibre-locus

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-irreducible-fibre-locus.json`: statement unchanged; split into five proof steps following Stacks 055B, with the finite-presentation model constructed explicitly.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-component-count-generic-constancy.json`: statement, unsplit; Stacks 055A with the count convention of 0556; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-noetherian-constructible-subset-criterion.json`: statement, unsplit; the sufficient direction of Stacks 053Z for schemes, with 01OZ; no Mathlib match.
- `citations.json`: a verbatim statement excerpt for each node used in each proof step.

## Attachments

None. I searched `WeilConjectures/` in the read-only slopmaster2 source for the blueprint tag, geometric irreducibility, constructible fibres and component-count terminology. `GenericIrreducibility.exists_ne_zero_forall_isIrreducible_fiber` in `WeilConjectures/RingTheory/GenericIrreducibility.lean` gives irreducibility on a generic open under a Noetherian-domain hypothesis; it does not give constructibility of this locus over arbitrary rings and is not an attachment. The other scheme geometric-irreducibility declarations likewise do not state this item. The exact master source was searched for the item tag as reference only.

## Literature wanted

None. The Stacks sources used are present locally.

## Corrections and scope

The imported item is true as written. There is no STATEMENT-DISPUTED and no changed hypothesis or conclusion. In particular empty fibres are excluded from the locus. I retained the inherited statement, source, searches, created record and blueprint ancestry. The new search records are the exact queries in this sandbox's `searches.jsonl`, with their actual results; no unavailable service was reported in these runs.

The imported source pointer to 055B at level one is a starting point, not a proof: I supplied the descent, geometric-count interpretation and pullback argument. I used 055A as a new input, rather than creating a new node that repeats the constructible-locus theorem or the whole 055B theorem. The criterion node is an independent generic topological tool: it has neither a morphism nor a fibre hypothesis. Neither new node has a proof or proof dependencies. Both carry their complete statement and definition dependencies.

The current main-20261015 `lem-trf-local-term-locality.proof.md` and the unit `sk-i-curve-zero` use the contracting-correspondence argument; the item's old semistable-alteration ancestry is historical. I preserve that ancestry and only split the existing algebraic supporting node, as assigned. No unit statement, proof route, chapter, realized field, target, or coefficient category is changed. No SGA source is used. This item is not a declaration target and introduces no six-functor base-change morphism.

Generic off-unit tools declared in `split_report.tool_uses`: `lem-sbc-subset-geometric-irreducibility` tests irreducibility over a separably closed extension, and `lem-sbc-radicial-preparation-fibre-comparison` supplies the exact fibre-locus inverse-image equality, applied with an identity universal homeomorphism. These black-box geometric tools have no equivalent in the item's unit; they replace no step of its unit route. The other off-unit statements cited are Mathlib leaves.

## Search and duplication audit

I searched the whole DAG for 055A, 0556, 053Z, 01OZ, the Stacks labels, generic geometric-component constancy, irreducibility over separably closed extensions, and constructibility criteria. I ran `tools/blueprint_refs.py search` for 055B, 055A, 053Z, geometric components, the number of irreducible components, the fibre-locus statement and the constructible Noetherian criterion; no blueprint statement duplicates either new input. The nearest ancestor command returns `lem-trf-local-term-locality`, and each new node puts this item first in the inherited via list. The item's `same_as` is empty after this search.

Mathlib searches for the item and both new nodes used msearch.py with LeanFinder, Loogle, grep and LeanSearch, and a second semantic phrasing. I read the actual hits. Chevalley image theorems assert constructibility of an image and do not assert constructibility of the locus of a fibre property. `Scheme.Hom.irreducibleComponentsEquiv` in `Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean:89` requires an already geometrically irreducible open morphism and compares total-space components, so it does not give generic constancy for arbitrary finite type morphisms. The reduced-total-space theorem with finitely many components, the finite/discrete-fibre instances, NoetherianSpace component finiteness and `genericPoints` also do not give that assertion. For the criterion, Mathlib's constructibility definitions, local-to-global theorem and Noetherian-scheme topology instance do not supply its irreducible-closed-subset hypothesis-to-conclusion implication. None specializes to either new statement in one line.

## Not duplicates

lem-trf-noetherian-constructible-subset-criterion vs lem-weil-pbc-noetherian-open-subscheme-noetherian: the shared 01OZ is a topology input only; the existing node proves Noetherianity of an open subscheme and has no constructibility criterion for a subset.

lem-trf-noetherian-constructible-subset-criterion vs lem-weil-pbc-noetherian-finitely-many-components: the existing node states finiteness of components, not the 053Z constructibility criterion.

lem-trf-noetherian-constructible-subset-criterion vs lem-weil-pbc-noetherian-scheme-closed-subsets-minimal: the existing node states the minimal-closed-subset principle, not the 053Z criterion for a specified subset E.

The similarly named `lem-weil-pbc-constructible-closed-generic-criterion` concerns a sheaf of modules on an etale site and finite local constancy, rather than constructibility of a subset of a topological space. The section-component and generic-geometric-irreducibility nodes supply neighbourhoods under section or already-irreducible-generic-fibre hypotheses, whereas 055A counts every geometric component on every point closure. No new input is a clause or a restatement of the item itself.

## Review by Q64

I read delivery-errors B through E in full and checked the actual node files and sources, not just the metadata. I read Stacks `more-morphisms.tex` at 055B (`lemma-nr-geom-irreducible-components-constructible`), its complete proof, 055A (`lemma-nr-geom-irreducible-components-good`) and its proof, 0556 (`lemma-base-change-fibres-nr-geometrically-irreducible-components`), and the 0555 fibre-locus equality. I read Topology 053Z (`lemma-characterize-constructible-Noetherian`) including its minimal-closed-subset argument, and Properties 01OZ (`lemma-Noetherian-topology`). The tag-to-label pairs were checked in `tags/tags`. These are the sources for the item and each of the two new nodes. I also read the project source definition of geometric irreducibility and every statement quoted in citations.json.

Step 1 uses the finite-presentation definition to select finitely many variables and relations, and the actual ring tensor-pushout statement to construct the maps. Its inverse sends scalars to the A factor and variables to the B_0 factor; the displayed relations vanish, and the uniqueness clause proves both maps inverse. This is the routine finite-data descent in 055B written out, not a use of a global Noetherian-approximation theorem that might already depend on this item. The ring A_0 is allowed to be zero.

Step 2 uses the affine finite-type definition and the exact sentence of `lem-weil-pbc-finite-type-over-noetherian` saying that schemes of finite type over Spec Z are Noetherian. This checks the Noetherian-base hypothesis of the later criterion without assuming A itself Noetherian. B_0 is finitely presented, so its morphism is in particular finite type, the only finiteness needed by 055A.

Step 3 uses the sober-scheme leaf for a generic point of every irreducible closed Z, then the new 055A statement with that point. It does not need to base-change to a closed subscheme and silently assume an extra base-change theorem. The components-cover leaf really states that all points belong to components. Together with the definition of maximal irreducible subset, it gives the one-component iff irreducible interpretation, including nonemptiness. I did not treat irreducibility as including the empty space or silently use connectedness in its place.

Step 4 uses the full subset inverse-image test of `lem-sbc-subset-geometric-irreducibility`, with the whole fibre as its subset and the fixed separable closure as its separably closed extension. Its statement really quantifies over every extension field, so it supplies the entire geometric-irreducibility clause, not just irreducibility over one extension. The separable-closure definition supplies its stated hypothesis. The 055A count is constant on V, so V is wholly inside E_0 or wholly outside it; this verifies every hypothesis of the new 053Z criterion. No inference from a definition node alone to a non-elementary geometric theorem is used.

Step 5 uses the exact affine fibre-product/tensor-product isomorphism. The fibre-comparison lemma is applied with the identity universal homeomorphism, permitted by its arbitrary-morphism statement; the identity satisfies the definition because every base change is again the identity. It gives the iff at each point and hence an equality of loci, not only an inclusion. The scheme constructible-preimage leaf has no finiteness hypothesis on r, and so applies even when A is not Noetherian or finitely generated. This is precisely where a merely continuous-preimage theorem without retrocompactness would have been insufficient; I used the scheme theorem instead.

Small cases for the item and count lemma: the zero ring has empty spectrum and a constructible empty locus; B=0 over a nonzero base gives count zero and empty locus; B=A and B=A[x] give count one and the entire base; B=A times A has two components in each nonempty geometric fibre and empty locus. Over a separably closed field, k[epsilon]/(epsilon^2) has one component and is geometrically irreducible although not reduced, confirming that no reducedness was added. Over k=R the finite algebra C has irreducible ordinary spectrum but two components over a separable closure, so it is correctly excluded. Empty geometric generic fibre gives n=0 and an open with empty fibres in 055A. The count lemma needs finite type but neither flatness nor a Noetherian base, just as its source states.

For the criterion I tested the empty scheme (hypothesis vacuous and E empty), a point (both subsets constructible), and a reducible finite union (each irreducible closed subset is tested, not just ambient components). The nonempty-relative-open hypothesis is essential and present. The criterion is a genuine Noetherian induction theorem, not an elementary new node. The 055A node is a generic-constancy theorem, not the constructibility conclusion being proved. I checked all statements are self-contained, every named notion has its definition dependency, both new nodes remain statement-only, proof_deps is exactly the union of uses, and the delivered closure has no cycle. No proof step exceeds 2000 characters; none hides a comparison or a lemma called standard in place of a proof. No Lean file was written and no compiler or Lake command was run.

## Unfinished work

No part of the assigned split remains unfinished. The two new statement-only inputs are deliberately unsplit for later stage-1 work. Server dry-run validation and direct delivery follow this report.
